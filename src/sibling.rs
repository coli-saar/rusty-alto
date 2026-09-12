//! Equality-indexed sibling-finder intersection.
//!
//! This module combines inverse homomorphism and automaton intersection in one
//! bottom-up chart construction.  Decomposition automata only provide an
//! equality key for each side of a binary operation.  The generic algorithm
//! lifts those local chart indexes through homomorphism terms.

use crate::{
    BottomUpTa, Explicit, ExplicitBuilder, FxHashMap, HomLabel, Homomorphism, Interner,
    ParseControl, StateId, Symbol, control::ParseCancelled,
};
use packed_term_arena::tree::{Tree, TreeArena};
use smallvec::SmallVec;
use std::{
    collections::VecDeque,
    hash::{Hash, Hasher},
};
use thiserror::Error;

/// A decomposition automaton whose binary transitions admit equality-indexed
/// partner lookup.
///
/// If `f(left, right)` is a valid transition, both calls to `sibling_key` must
/// return equal keys. Returning equal keys for an invalid pair is allowed: the
/// sibling materializer validates candidates with [`BottomUpTa::step`].
pub trait SiblingKeyedTa: BottomUpTa {
    /// Equality key stored in the local chart indexes.
    type Key: Clone + Eq + Hash;

    /// Return the partner-lookup key for `state` in child `position` of `f`.
    /// `None` means that the state cannot occur in that position.
    fn sibling_key(&self, f: Symbol, position: usize, state: &Self::State) -> Option<Self::Key>;
}

/// Failure while constructing a sibling-finder intersection.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SiblingIntersectionError {
    /// Parsing was cancelled through the supplied control.
    #[error("parsing was cancelled")]
    Cancelled,
    /// A homomorphic image contains a target operation above binary rank.
    #[error("sibling intersection supports target rank at most 2, but {symbol:?} has rank {arity}")]
    UnsupportedTargetArity {
        /// Target operation in the homomorphic term.
        symbol: Symbol,
        /// Number of children at that occurrence.
        arity: usize,
    },
}

impl From<ParseCancelled> for SiblingIntersectionError {
    fn from(_: ParseCancelled) -> Self {
        Self::Cancelled
    }
}

/// Counters from one sibling-finder intersection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SiblingIntersectionStats {
    /// Product states in the resulting chart.
    pub output_states: usize,
    /// Rules in the resulting chart.
    pub output_rules: usize,
    /// Product states removed from the bottom-up agenda.
    pub agenda_pops: usize,
    /// New facts inserted into homomorphism-term charts.
    pub term_items: usize,
    /// Equal-key partner candidates considered.
    pub partner_candidates: usize,
    /// Calls to the decomposition automaton's transition oracle.
    pub right_step_calls: usize,
    /// Completed homomorphism-root items.
    pub root_items: usize,
}

#[derive(Clone)]
struct LeftRule {
    symbol: Symbol,
    children: SmallVec<[StateId; 2]>,
    result: StateId,
    weight: f64,
    program: usize,
}

#[derive(Clone, Copy)]
struct ParentLink {
    node: usize,
    position: usize,
}

enum CompiledNode {
    Pending,
    Variable,
    Operation {
        symbol: Symbol,
        children: SmallVec<[usize; 2]>,
    },
}

struct NodePlan {
    parent: Option<ParentLink>,
    kind: CompiledNode,
}

struct CompiledTerm {
    nodes: Vec<NodePlan>,
    root: usize,
    variable_nodes: Vec<usize>,
    arity: usize,
}

fn compile_term(
    arena: &TreeArena<HomLabel>,
    root: Tree,
    arity: usize,
) -> Result<CompiledTerm, SiblingIntersectionError> {
    fn visit(
        arena: &TreeArena<HomLabel>,
        term: Tree,
        parent: Option<ParentLink>,
        nodes: &mut Vec<NodePlan>,
        variables: &mut [usize],
    ) -> Result<usize, SiblingIntersectionError> {
        let id = nodes.len();
        nodes.push(NodePlan {
            parent,
            kind: CompiledNode::Pending,
        });

        nodes[id].kind = match *arena.get_label(term) {
            HomLabel::Var(position) => {
                variables[position] = id;
                CompiledNode::Variable
            }
            HomLabel::Symbol(symbol) => {
                let term_children = arena.get_children(term);
                if term_children.len() > 2 {
                    return Err(SiblingIntersectionError::UnsupportedTargetArity {
                        symbol,
                        arity: term_children.len(),
                    });
                }
                let mut children = SmallVec::new();
                for (position, &child) in term_children.iter().enumerate() {
                    children.push(visit(
                        arena,
                        child,
                        Some(ParentLink { node: id, position }),
                        nodes,
                        variables,
                    )?);
                }
                CompiledNode::Operation { symbol, children }
            }
        };
        Ok(id)
    }

    let mut nodes = Vec::new();
    let mut variable_nodes = vec![usize::MAX; arity];
    let root = visit(arena, root, None, &mut nodes, &mut variable_nodes)?;
    debug_assert!(variable_nodes.iter().all(|&node| node != usize::MAX));
    Ok(CompiledTerm {
        nodes,
        root,
        variable_nodes,
        arity,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct TermItem {
    right: StateId,
    products: SmallVec<[StateId; 4]>,
}

struct BinaryIndex<K> {
    positions: [FxHashMap<K, Vec<usize>>; 2],
}

impl<K> Default for BinaryIndex<K> {
    fn default() -> Self {
        Self {
            positions: std::array::from_fn(|_| FxHashMap::default()),
        }
    }
}

struct NodeChart<K> {
    items: Vec<TermItem>,
    seen_by_hash: FxHashMap<u64, SmallVec<[usize; 1]>>,
    binary_index: BinaryIndex<K>,
}

impl<K> Default for NodeChart<K> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            seen_by_hash: FxHashMap::default(),
            binary_index: BinaryIndex::default(),
        }
    }
}

struct TermChart<K> {
    nodes: Vec<NodeChart<K>>,
    agenda: Vec<(usize, usize)>,
    initialized: bool,
}

impl<K> TermChart<K> {
    fn new(node_count: usize) -> Self {
        Self {
            nodes: (0..node_count).map(|_| NodeChart::default()).collect(),
            agenda: Vec::new(),
            initialized: false,
        }
    }
}

impl<K: Clone + Eq + Hash> TermChart<K> {
    fn insert(&mut self, node: usize, item: TermItem, stats: &mut SiblingIntersectionStats) {
        let chart = &mut self.nodes[node];
        let mut hasher = rustc_hash::FxHasher::default();
        item.hash(&mut hasher);
        let hash = hasher.finish();
        if chart
            .seen_by_hash
            .get(&hash)
            .is_some_and(|ids| ids.iter().any(|&id| chart.items[id] == item))
        {
            return;
        }
        let item_id = chart.items.len();
        chart.items.push(item);
        chart.seen_by_hash.entry(hash).or_default().push(item_id);
        self.agenda.push((node, item_id));
        stats.term_items += 1;
    }

    fn initialize<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        decomp: &D,
        right_states: &mut Interner<D::State>,
        roots: &mut Vec<TermItem>,
        stats: &mut SiblingIntersectionStats,
        control: &ParseControl,
    ) -> Result<(), SiblingIntersectionError> {
        if self.initialized {
            return Ok(());
        }
        self.initialized = true;
        for (node, node_plan) in plan.nodes.iter().enumerate() {
            let CompiledNode::Operation { symbol, children } = &node_plan.kind else {
                continue;
            };
            if !children.is_empty() {
                continue;
            }
            stats.right_step_calls += 1;
            decomp.step(*symbol, &[], &mut |result| {
                let right = right_states.intern(result);
                self.insert(
                    node,
                    TermItem {
                        right,
                        products: smallvec::smallvec![StateId::STUCK; plan.arity],
                    },
                    stats,
                );
            });
        }
        self.propagate(plan, decomp, right_states, roots, stats, control)
    }

    #[allow(clippy::too_many_arguments)]
    fn activate<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        variable: usize,
        right: StateId,
        product: StateId,
        decomp: &D,
        right_states: &mut Interner<D::State>,
        roots: &mut Vec<TermItem>,
        stats: &mut SiblingIntersectionStats,
        control: &ParseControl,
    ) -> Result<(), SiblingIntersectionError> {
        self.initialize(plan, decomp, right_states, roots, stats, control)?;
        let mut products = smallvec::smallvec![StateId::STUCK; plan.arity];
        products[variable] = product;
        self.insert(
            plan.variable_nodes[variable],
            TermItem { right, products },
            stats,
        );
        self.propagate(plan, decomp, right_states, roots, stats, control)
    }

    #[allow(clippy::too_many_arguments)]
    fn propagate<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        decomp: &D,
        right_states: &mut Interner<D::State>,
        roots: &mut Vec<TermItem>,
        stats: &mut SiblingIntersectionStats,
        control: &ParseControl,
    ) -> Result<(), SiblingIntersectionError> {
        while let Some((node, item_id)) = self.agenda.pop() {
            control.check()?;
            if node == plan.root {
                roots.push(self.nodes[node].items[item_id].clone());
                stats.root_items += 1;
                continue;
            }

            let link = plan.nodes[node]
                .parent
                .expect("every non-root compiled node has a parent");
            let CompiledNode::Operation { symbol, children } = &plan.nodes[link.node].kind else {
                unreachable!("variables cannot have children");
            };
            match children.len() {
                1 => {
                    let item = self.nodes[node].items[item_id].clone();
                    let raw = right_states.resolve(item.right).clone();
                    stats.right_step_calls += 1;
                    let mut results = SmallVec::<[StateId; 2]>::new();
                    decomp.step(*symbol, &[raw], &mut |result| {
                        results.push(right_states.intern(result));
                    });
                    for right in results {
                        self.insert(
                            link.node,
                            TermItem {
                                right,
                                products: item.products.clone(),
                            },
                            stats,
                        );
                    }
                }
                2 => {
                    let item = self.nodes[node].items[item_id].clone();
                    let raw = right_states.resolve(item.right).clone();
                    let Some(key) = decomp.sibling_key(*symbol, link.position, &raw) else {
                        continue;
                    };
                    let other_position = 1 - link.position;
                    let partner_count = self.nodes[link.node].binary_index.positions
                        [other_position]
                        .get(&key)
                        .map_or(0, Vec::len);
                    let partner_key = key.clone();
                    self.nodes[link.node].binary_index.positions[link.position]
                        .entry(key)
                        .or_default()
                        .push(item_id);

                    let other_node = children[other_position];
                    for partner_index in 0..partner_count {
                        let partner_id = self.nodes[link.node].binary_index.positions
                            [other_position][&partner_key][partner_index];
                        stats.partner_candidates += 1;
                        let (left_right, right_right, products) = {
                            let partner = &self.nodes[other_node].items[partner_id];
                            let (left, right) = if link.position == 0 {
                                (&item, partner)
                            } else {
                                (partner, &item)
                            };
                            let mut products = left.products.clone();
                            for (slot, &product) in right.products.iter().enumerate() {
                                if product != StateId::STUCK {
                                    debug_assert_eq!(products[slot], StateId::STUCK);
                                    products[slot] = product;
                                }
                            }
                            (left.right, right.right, products)
                        };
                        let raw_children = [
                            right_states.resolve(left_right).clone(),
                            right_states.resolve(right_right).clone(),
                        ];
                        stats.right_step_calls += 1;
                        let mut results = SmallVec::<[StateId; 2]>::new();
                        decomp.step(*symbol, &raw_children, &mut |result| {
                            results.push(right_states.intern(result));
                        });
                        for right in results {
                            self.insert(
                                link.node,
                                TermItem {
                                    right,
                                    products: products.clone(),
                                },
                                stats,
                            );
                        }
                    }
                }
                _ => unreachable!("rank above two was rejected while compiling"),
            }
        }
        Ok(())
    }
}

#[derive(Default)]
struct ProductMap {
    by_right: Vec<FxHashMap<StateId, StateId>>,
}

impl ProductMap {
    fn get(&self, left: StateId, right: StateId) -> Option<StateId> {
        self.by_right
            .get(right.index())
            .and_then(|row| row.get(&left).copied())
    }

    fn insert(&mut self, left: StateId, right: StateId, product: StateId) {
        if self.by_right.len() <= right.index() {
            self.by_right
                .resize_with(right.index() + 1, FxHashMap::default);
        }
        self.by_right[right.index()].insert(left, product);
    }
}

#[allow(clippy::too_many_arguments)]
fn product_id<D: BottomUpTa>(
    left_state: StateId,
    right_state: StateId,
    left: &Explicit,
    decomp: &D,
    right_states: &Interner<D::State>,
    products: &mut ProductMap,
    pairs: &mut Vec<(StateId, StateId)>,
    builder: &mut ExplicitBuilder,
) -> (StateId, bool) {
    if let Some(id) = products.get(left_state, right_state) {
        return (id, false);
    }
    let id = builder.new_state();
    products.insert(left_state, right_state, id);
    pairs.push((left_state, right_state));
    if left.is_accepting(&left_state) && decomp.is_accepting(right_states.resolve(right_state)) {
        builder.add_accepting(id);
    }
    (id, true)
}

/// Materialize the complete bottom-up intersection of `left` with the inverse
/// homomorphic image of `decomp`, using equality-indexed sibling lookup.
#[allow(clippy::type_complexity)]
pub fn materialize_sibling_intersection<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
) -> Result<
    (
        Explicit,
        Interner<D::State>,
        Vec<(StateId, StateId)>,
        SiblingIntersectionStats,
    ),
    SiblingIntersectionError,
>
where
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    materialize_sibling_intersection_controlled(left, decomp, hom, &ParseControl::new())
}

/// Cancellable counterpart of [`materialize_sibling_intersection`].
#[allow(clippy::type_complexity)]
pub(crate) fn materialize_sibling_intersection_controlled<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
    control: &ParseControl,
) -> Result<
    (
        Explicit,
        Interner<D::State>,
        Vec<(StateId, StateId)>,
        SiblingIntersectionStats,
    ),
    SiblingIntersectionError,
>
where
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    condensed::materialize(left, decomp, hom, control)
}

/// Rule-local sibling implementation retained for algorithm comparisons.
#[doc(hidden)]
#[allow(clippy::type_complexity)]
pub fn materialize_rule_local_sibling_intersection<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
) -> Result<
    (
        Explicit,
        Interner<D::State>,
        Vec<(StateId, StateId)>,
        SiblingIntersectionStats,
    ),
    SiblingIntersectionError,
>
where
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    materialize_rule_local_sibling_intersection_controlled(left, decomp, hom, &ParseControl::new())
}

#[allow(clippy::type_complexity)]
fn materialize_rule_local_sibling_intersection_controlled<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
    control: &ParseControl,
) -> Result<
    (
        Explicit,
        Interner<D::State>,
        Vec<(StateId, StateId)>,
        SiblingIntersectionStats,
    ),
    SiblingIntersectionError,
>
where
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    control.check()?;
    let mut programs = Vec::<CompiledTerm>::new();
    let mut program_by_term = FxHashMap::<usize, usize>::default();
    let mut rules = Vec::<LeftRule>::new();

    for rule in left.rules() {
        let Some(term_id) = hom.term_id(rule.symbol) else {
            continue;
        };
        let program = if let Some(&program) = program_by_term.get(&term_id) {
            program
        } else {
            let program = programs.len();
            programs.push(compile_term(
                hom.arena(),
                hom.term_by_id(term_id),
                rule.children.len(),
            )?);
            program_by_term.insert(term_id, program);
            program
        };
        debug_assert_eq!(programs[program].arity, rule.children.len());
        rules.push(LeftRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
            weight: rule.weight,
            program,
        });
    }

    let mut by_left_child = vec![Vec::<(usize, usize)>::new(); left.num_states() as usize];
    let mut nullary_rules = Vec::new();
    for (rule_id, rule) in rules.iter().enumerate() {
        if rule.children.is_empty() {
            nullary_rules.push(rule_id);
        }
        for (position, &child) in rule.children.iter().enumerate() {
            by_left_child[child.index()].push((rule_id, position));
        }
    }

    let mut charts: Vec<TermChart<D::Key>> = rules
        .iter()
        .map(|rule| TermChart::new(programs[rule.program].nodes.len()))
        .collect();
    let mut right_states = Interner::new();
    let mut products = ProductMap::default();
    let mut pairs = Vec::new();
    let mut builder = ExplicitBuilder::new();
    let mut agenda = VecDeque::<(StateId, StateId, StateId)>::new();
    let mut stats = SiblingIntersectionStats::default();
    let mut roots = Vec::<TermItem>::new();

    for rule_id in nullary_rules {
        control.check()?;
        roots.clear();
        let rule = &rules[rule_id];
        charts[rule_id].initialize(
            &programs[rule.program],
            decomp,
            &mut right_states,
            &mut roots,
            &mut stats,
            control,
        )?;
        for root in roots.drain(..) {
            let (parent, is_new) = product_id(
                rule.result,
                root.right,
                left,
                decomp,
                &right_states,
                &mut products,
                &mut pairs,
                &mut builder,
            );
            if is_new {
                agenda.push_back((rule.result, root.right, parent));
            }
            builder.add_weighted_rule_inline(rule.symbol, SmallVec::new(), parent, rule.weight);
        }
    }

    while let Some((left_state, right_state, product)) = agenda.pop_front() {
        control.check()?;
        stats.agenda_pops += 1;
        for &(rule_id, position) in &by_left_child[left_state.index()] {
            roots.clear();
            let rule = &rules[rule_id];
            charts[rule_id].activate(
                &programs[rule.program],
                position,
                right_state,
                product,
                decomp,
                &mut right_states,
                &mut roots,
                &mut stats,
                control,
            )?;
            for root in roots.drain(..) {
                debug_assert!(root.products.iter().all(|p| !p.is_stuck()));
                let (parent, is_new) = product_id(
                    rule.result,
                    root.right,
                    left,
                    decomp,
                    &right_states,
                    &mut products,
                    &mut pairs,
                    &mut builder,
                );
                if is_new {
                    agenda.push_back((rule.result, root.right, parent));
                }
                builder.add_weighted_rule_inline(
                    rule.symbol,
                    SmallVec::from_vec(root.products.into_vec()),
                    parent,
                    rule.weight,
                );
            }
        }
    }

    stats.output_states = pairs.len();
    let chart = builder.build_trusted();
    stats.output_rules = chart.rules().count();
    Ok((chart, right_states, pairs, stats))
}

mod condensed;
