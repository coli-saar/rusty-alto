//! Execution engine for compiled sibling-finder programs.
//!
//! A [`RunningProgram`] evaluates one distinct homomorphism right-hand side and
//! is shared by all source rules with that image. The outer [`Materializer`]
//! maintains reachable product states and joins completed program roots with
//! source rules. These two structures implement the two possible arrival
//! orders from `sibling-finder.typ`: a root item may arrive after its product
//! children, or a missing product child may arrive after the root item.

use super::*;
use crate::{
    ExplicitBuilder, SetTrie,
    materialize::{OwnedRule, ProductStateMap, TrustedRuleTracker},
};
use std::{collections::VecDeque, hash::Hasher};

/// Items derived for one node of a term program.
///
/// Conceptually, an item is `(u, q, assignment)`: `u` is implicit in the
/// containing vector position, `q` is stored in `items`, and `assignment`
/// records the decomposition states assigned to the source variables below
/// `u`. Assignments are packed row-major in one flat vector to avoid one heap
/// allocation per item.
struct NodeItems<I> {
    items: Vec<StateId>,
    /// Row-major variable assignments; every item occupies one fixed-width row.
    assignments: Vec<StateId>,
    assignment_width: usize,
    /// Candidate item IDs by precomputed hash; full rows are compared on collision.
    seen_by_hash: FxHashMap<u64, SmallVec<[usize; 1]>>,
    /// Present only at binary operation nodes.
    binary_index: Option<I>,
}

impl<I> NodeItems<I> {
    /// Create empty storage for a node whose assignment rows have fixed width.
    fn new(assignment_width: usize, binary_index: Option<I>) -> Self {
        Self {
            items: Vec::new(),
            assignments: Vec::new(),
            assignment_width,
            seen_by_hash: FxHashMap::default(),
            binary_index,
        }
    }

    /// Insert a distinct `(decomposition state, assignment)` pair.
    ///
    /// Returns its new item ID, or `None` if the same fact is already present.
    fn insert(&mut self, right: StateId, assignment: &[StateId]) -> Option<usize> {
        debug_assert_eq!(assignment.len(), self.assignment_width);
        let mut hasher = rustc_hash::FxHasher::default();
        right.hash(&mut hasher);
        assignment.hash(&mut hasher);
        let hash = hasher.finish();
        if self.seen_by_hash.get(&hash).is_some_and(|ids| {
            ids.iter().any(|&id| {
                let start = id * self.assignment_width;
                self.items[id] == right
                    && self.assignments[start..start + self.assignment_width] == assignment[..]
            })
        }) {
            return None;
        }
        let item = self.items.len();
        self.items.push(right);
        self.assignments.extend_from_slice(assignment);
        self.seen_by_hash.entry(hash).or_default().push(item);
        Some(item)
    }

    /// Borrow the packed assignment row for `item`.
    fn assignment(&self, item: usize) -> &[StateId] {
        let start = item * self.assignment_width;
        &self.assignments[start..start + self.assignment_width]
    }
}

/// Term chart for one distinct homomorphism right-hand side.
///
/// `nodes` contains the items for each term-program node. `agenda` drives local
/// upward propagation inside this program; it is distinct from the outer
/// product-state agenda. A root item records only decomposition states and is
/// therefore the condensed inverse-homomorphism transition from the note.
struct RunningProgram<'a, I> {
    compiled: &'a CompiledProgram,
    nodes: Vec<NodeItems<I>>,
    agenda: Vec<(usize, usize)>,
    assignment_scratch: Vec<StateId>,
    /// Root items indexed by source-child position and decomposition state.
    root_by_child: Vec<FxHashMap<StateId, Vec<usize>>>,
    /// Whether input-independent nullary operations have been evaluated.
    initialized: bool,
}

/// Borrowed services needed while a term chart performs decomposition steps.
///
/// This is a borrow bundle, not a separate semantic layer. It keeps the chart
/// API from taking four parallel parameters and gives all transition calls one
/// place to update statistics and intern their results.
struct StepContext<'a, D: BottomUpTa> {
    decomp: &'a D,
    right_states: &'a mut Interner<D::State>,
    stats: &'a mut SiblingIntersectionStats,
    control: &'a ParseControl,
}

impl<D: BottomUpTa> StepContext<'_, D> {
    /// Run one decomposition transition and intern every returned state.
    fn step(&mut self, symbol: Symbol, children: &[D::State]) -> SmallVec<[StateId; 2]> {
        self.stats.right_step_calls += 1;
        let mut results = SmallVec::new();
        self.decomp.step(symbol, children, &mut |result| {
            results.push(self.right_states.intern(result));
        });
        results
    }
}

impl<'a, I> RunningProgram<'a, I> {
    /// Allocate the per-node storage and one sibling index per binary node.
    fn new<D, F>(
        compiled: &'a CompiledProgram,
        decomp: &D,
        sibling_indexes: &F,
    ) -> Result<Self, SiblingIntersectionError>
    where
        D: BottomUpTa,
        F: SiblingIndexFactory<D, Index = I>,
    {
        let plan = &compiled.term;
        let mut nodes = Vec::with_capacity(plan.nodes.len());
        for node in &plan.nodes {
            let binary_index = match node.operation() {
                Some(operation) if operation.children.len() == 2 => Some(
                    sibling_indexes
                        .new_index(decomp, operation.symbol)
                        .ok_or(SiblingIntersectionError::SiblingIndexUnavailable)?,
                ),
                _ => None,
            };
            nodes.push(NodeItems::new(node.assignment_width(), binary_index));
        }
        Ok(Self {
            compiled,
            nodes,
            agenda: Vec::new(),
            assignment_scratch: Vec::with_capacity(plan.arity()),
            root_by_child: (0..plan.arity()).map(|_| FxHashMap::default()).collect(),
            initialized: false,
        })
    }

    /// Insert a new term item and schedule it for upward propagation.
    fn insert(
        &mut self,
        node: usize,
        right: StateId,
        assignment: &[StateId],
        stats: &mut SiblingIntersectionStats,
    ) {
        let chart = &mut self.nodes[node];
        let Some(item) = chart.insert(right, assignment) else {
            return;
        };
        self.agenda.push((node, item));
        stats.term_items += 1;
    }

    /// Evaluate the program's input-independent nullary operations once.
    fn seed_constants<D: BottomUpTa>(&mut self, evaluation: &mut StepContext<'_, D>) {
        if self.initialized {
            return;
        }
        self.initialized = true;
        let mut assignment = std::mem::take(&mut self.assignment_scratch);
        assignment.clear();
        for node in 0..self.compiled.term.nodes.len() {
            let Some(CompiledOperation { symbol, children }) =
                self.compiled.term.nodes[node].operation()
            else {
                continue;
            };
            if !children.is_empty() {
                continue;
            }
            let symbol = *symbol;
            for right in evaluation.step(symbol, &[]) {
                self.insert(node, right, &assignment, evaluation.stats);
            }
        }
        assignment.clear();
        self.assignment_scratch = assignment;
    }

    /// Add a reachable decomposition state at one source variable.
    ///
    /// Repeated activation is harmless: each `(variable, state)` pair enters
    /// the term chart once.
    fn activate<D: BottomUpTa>(
        &mut self,
        variable: usize,
        right: StateId,
        evaluation: &mut StepContext<'_, D>,
        new_roots: &mut Vec<usize>,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
        I: BinarySiblingIndex<D::State>,
    {
        self.seed_constants(evaluation);
        let mut assignment = std::mem::take(&mut self.assignment_scratch);
        assignment.clear();
        assignment.push(right);
        let variable_node = self.compiled.term.variable_nodes[variable];
        self.insert(variable_node, right, &assignment, evaluation.stats);
        assignment.clear();
        self.assignment_scratch = assignment;
        self.propagate(evaluation, new_roots)
    }

    /// Propagate scheduled items toward the root of the term program.
    ///
    /// Unary nodes call the decomposition automaton directly. At a binary node,
    /// the new item probes the sibling index before it is added, so each pair is
    /// considered when its second member arrives. `new_roots` receives the IDs
    /// of completed condensed transitions.
    fn propagate<D: BottomUpTa>(
        &mut self,
        evaluation: &mut StepContext<'_, D>,
        new_roots: &mut Vec<usize>,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
        I: BinarySiblingIndex<D::State>,
    {
        let plan = &self.compiled.term;
        let mut assignment = std::mem::take(&mut self.assignment_scratch);
        while let Some((node, item_id)) = self.agenda.pop() {
            evaluation.control.check()?;
            if node == ROOT_NODE {
                for position in 0..plan.arity() {
                    let child = self.nodes[node].assignment(item_id)[position];
                    self.root_by_child[position]
                        .entry(child)
                        .or_default()
                        .push(item_id);
                }
                new_roots.push(item_id);
                evaluation.stats.root_items += 1;
                continue;
            }

            let link = plan.nodes[node]
                .parent()
                .expect("every non-root compiled node has a parent");
            let Some(CompiledOperation { symbol, children }) = plan.nodes[link.node].operation()
            else {
                unreachable!("a variable cannot be a parent node");
            };
            match children.len() {
                1 => {
                    let item = self.nodes[node].items[item_id];
                    let raw = evaluation.right_states.resolve(item).clone();
                    let results = evaluation.step(*symbol, &[raw]);
                    copy_assignment_into(
                        self.nodes[node].assignment(item_id),
                        if link.node == ROOT_NODE {
                            plan.root_permutation.as_slice()
                        } else {
                            &[]
                        },
                        &mut assignment,
                    );
                    for right in results {
                        self.insert(link.node, right, &assignment, evaluation.stats);
                    }
                }
                2 => {
                    let item = self.nodes[node].items[item_id];
                    let raw = evaluation.right_states.resolve(item).clone();
                    let other_position = 1 - link.position;
                    let partner_count = {
                        let binary_index = self.nodes[link.node]
                            .binary_index
                            .as_mut()
                            .expect("binary operation nodes have a sibling index");
                        let partner_count = binary_index.partners(link.position, &raw).len();
                        binary_index.add(link.position, &raw, item_id);
                        partner_count
                    };

                    let other_node = children[other_position];
                    for partner_index in 0..partner_count {
                        let partner_id = self.nodes[link.node]
                            .binary_index
                            .as_ref()
                            .expect("binary operation nodes have a sibling index")
                            .partners(link.position, &raw)[partner_index];
                        evaluation.stats.partner_candidates += 1;
                        let partner = &self.nodes[other_node].items[partner_id];
                        let (left, right) = if link.position == 0 {
                            (item, *partner)
                        } else {
                            (*partner, item)
                        };
                        let (left_node, left_id, right_node, right_id) = if link.position == 0 {
                            (node, item_id, other_node, partner_id)
                        } else {
                            (other_node, partner_id, node, item_id)
                        };
                        merge_assignments_into(
                            self.nodes[left_node].assignment(left_id),
                            self.nodes[right_node].assignment(right_id),
                            if link.node == ROOT_NODE {
                                plan.root_permutation.as_slice()
                            } else {
                                &[]
                            },
                            &mut assignment,
                        );
                        let raw_children = [
                            evaluation.right_states.resolve(left).clone(),
                            evaluation.right_states.resolve(right).clone(),
                        ];
                        let results = evaluation.step(*symbol, &raw_children);
                        debug_assert!(
                            !results.is_empty(),
                            "sibling index returned an incompatible partner"
                        );
                        for right in results {
                            self.insert(link.node, right, &assignment, evaluation.stats);
                        }
                    }
                }
                _ => unreachable!("rank above two was rejected while compiling"),
            }
        }
        assignment.clear();
        self.assignment_scratch = assignment;
        Ok(())
    }

    /// Resolve a root item to its result state and source-ordered children.
    fn root(&self, root: usize) -> (StateId, &[StateId]) {
        (
            self.nodes[ROOT_NODE].items[root],
            self.nodes[ROOT_NODE].assignment(root),
        )
    }

    /// Find completed transitions that use `right` at source-child `position`.
    fn roots_with_child(&self, position: usize, right: StateId) -> &[usize] {
        self.root_by_child[position]
            .get(&right)
            .map_or(&[], Vec::as_slice)
    }
}

/// Merge the variable assignments of two sibling items.
///
/// Subterm assignments follow term traversal order. At the root only, the
/// compiler supplies `permutation` to restore source-rule child order.
fn merge_assignments_into(
    left: &[StateId],
    right: &[StateId],
    permutation: &[usize],
    merged: &mut Vec<StateId>,
) {
    merged.clear();
    if permutation.is_empty() {
        merged.extend_from_slice(left);
        merged.extend_from_slice(right);
        return;
    }
    merged.reserve(permutation.len());
    for &offset in permutation {
        if offset < left.len() {
            merged.push(left[offset]);
        } else {
            merged.push(right[offset - left.len()]);
        }
    }
}

/// Copy a unary child's assignment, applying the root permutation if needed.
fn copy_assignment_into(source: &[StateId], permutation: &[usize], target: &mut Vec<StateId>) {
    target.clear();
    if permutation.is_empty() {
        target.extend_from_slice(source);
        return;
    }
    target.reserve(permutation.len());
    target.extend(permutation.iter().map(|&offset| source[offset]));
}

/// Source-rule occurrences activated by one newly reachable source state.
///
/// Rules sharing a program and variable position can activate that term chart
/// once, after which their IDs are used to join older root items.
struct OccurrenceGroup {
    program: usize,
    variable: usize,
    rule_ids: Vec<usize>,
}

/// Grammar-only data for one distinct homomorphism right-hand side.
struct CompiledProgram {
    /// The shared target-side computation for this homomorphism image.
    term: CompiledTerm,
    /// Source rules indexed by their ordered child states.
    left_rules: SetTrie<StateId, Vec<usize>>,
}

/// Grammar-only data compiled once for repeated sibling-finder parsing.
///
/// Each source rule occurs in exactly one [`CompiledProgram`]. `by_left_child`
/// is the reverse index that turns a new product state into term-variable
/// activations. No decomposition state or input-sized chart is stored here, so
/// an `Irtg` can cache this value across inputs.
pub(crate) struct CompiledSiblingGrammar {
    programs: Vec<CompiledProgram>,
    rules: Vec<OwnedRule>,
    by_left_child: Vec<Vec<OccurrenceGroup>>,
    /// Acceptance flags copied from the source automaton by dense state ID.
    source_accepting: Vec<bool>,
}

impl std::fmt::Debug for CompiledSiblingGrammar {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CompiledSiblingGrammar")
            .field("programs", &self.programs.len())
            .field("rules", &self.rules.len())
            .field("left_states", &self.by_left_child.len())
            .finish()
    }
}

/// Outer fixed-point construction of the product parse chart.
///
/// This structure owns the `(source state, decomposition state)` relation, the
/// FIFO agenda of newly reachable pairs, and the output automaton. Term charts
/// remain separate because their items are condensed across source rules.
struct Materializer<'a, D: BottomUpTa> {
    decomp: &'a D,
    compiled: &'a CompiledSiblingGrammar,
    right_states: Interner<D::State>,
    products: ProductStateMap,
    pairs: Vec<(StateId, StateId)>,
    builder: ExplicitBuilder,
    rule_tracker: TrustedRuleTracker,
    agenda: VecDeque<(StateId, StateId)>,
    /// Completed `(source rule, root item)` joins.
    ///
    /// A rule belongs to exactly one program, so its ID also identifies the
    /// chart in which `root_id` is meaningful.
    emitted: crate::FxHashSet<(usize, usize)>,
    stats: SiblingIntersectionStats,
}

impl<'a, D: BottomUpTa> Materializer<'a, D> {
    fn new(decomp: &'a D, compiled: &'a CompiledSiblingGrammar) -> Self {
        Self {
            decomp,
            compiled,
            right_states: Interner::new(),
            products: ProductStateMap::new(),
            pairs: Vec::new(),
            builder: ExplicitBuilder::new(),
            rule_tracker: TrustedRuleTracker::default(),
            agenda: VecDeque::new(),
            emitted: crate::FxHashSet::default(),
            stats: SiblingIntersectionStats::default(),
        }
    }

    /// Emit a product rule once all of its child product states exist.
    ///
    /// The same join can be discovered from either arrival direction. `emitted`
    /// gives the join a single owner without imposing an order on those events.
    fn try_emit(
        &mut self,
        rule_id: usize,
        root_id: usize,
        root_right: StateId,
        root_children: &[StateId],
    ) {
        if self.emitted.contains(&(rule_id, root_id)) {
            return;
        }
        let rule = &self.compiled.rules[rule_id];
        let mut product_children = SmallVec::<[StateId; 2]>::new();
        for (&left_child, &right_child) in rule.children.iter().zip(root_children) {
            let Some(product) = self.products.get(left_child, right_child) else {
                return;
            };
            product_children.push(product);
        }
        self.emitted.insert((rule_id, root_id));
        let parent = if let Some(parent) = self.products.get(rule.result, root_right) {
            parent
        } else {
            let parent = self.builder.new_state();
            self.products.insert(rule.result, root_right, parent);
            self.pairs.push((rule.result, root_right));
            if self.compiled.source_accepting[rule.result.index()]
                && self
                    .decomp
                    .is_accepting(self.right_states.resolve(root_right))
            {
                self.builder.add_accepting(parent);
            }
            self.agenda.push_back((rule.result, root_right));
            parent
        };
        self.rule_tracker.add_rule(
            &mut self.builder,
            rule.symbol,
            product_children,
            parent,
            rule.weight,
        );
    }
}

impl CompiledSiblingGrammar {
    /// Compile the source grammar and homomorphism into shared term programs.
    ///
    /// `left_rules` indexes source rules by their ordered child-state sequence;
    /// it is queried when a new condensed root item arrives. `by_left_child`
    /// provides the reverse direction: it finds programs and variable positions
    /// affected when a new product state arrives.
    pub(crate) fn new(
        left: &Explicit,
        hom: &Homomorphism,
    ) -> Result<Self, SiblingIntersectionError> {
        let mut programs = Vec::<CompiledProgram>::new();
        let mut program_by_term = vec![None; hom.num_terms()];
        let mut rules = Vec::<OwnedRule>::new();
        let mut by_left_child: Vec<Vec<OccurrenceGroup>> =
            (0..left.num_states()).map(|_| Vec::new()).collect();
        let mut occurrence_group_ids: Vec<FxHashMap<(usize, usize), usize>> = (0..left
            .num_states())
            .map(|_| FxHashMap::default())
            .collect();

        for rule in left.rules() {
            let Some(term_id) = hom.term_id(rule.symbol) else {
                continue;
            };
            let program = if let Some(program) = program_by_term[term_id] {
                program
            } else {
                let program = programs.len();
                programs.push(CompiledProgram {
                    term: compile_term(hom.arena(), hom.term_by_id(term_id), rule.children.len())?,
                    left_rules: SetTrie::new(),
                });
                program_by_term[term_id] = Some(program);
                program
            };
            debug_assert_eq!(programs[program].term.arity(), rule.children.len());
            let rule_id = rules.len();
            let owned = OwnedRule {
                symbol: rule.symbol,
                children: rule.children.iter().copied().collect(),
                result: rule.result,
                weight: rule.weight,
            };
            programs[program]
                .left_rules
                .get_or_insert_with(&owned.children, Vec::new)
                .push(rule_id);
            for (variable, &child) in owned.children.iter().enumerate() {
                let groups = &mut by_left_child[child.index()];
                let group_ids = &mut occurrence_group_ids[child.index()];
                let group_id = *group_ids.entry((program, variable)).or_insert_with(|| {
                    let group_id = groups.len();
                    groups.push(OccurrenceGroup {
                        program,
                        variable,
                        rule_ids: Vec::new(),
                    });
                    group_id
                });
                groups[group_id].rule_ids.push(rule_id);
            }
            rules.push(owned);
        }

        Ok(Self {
            programs,
            rules,
            by_left_child,
            source_accepting: (0..left.num_states())
                .map(|state| left.is_accepting(&StateId(state)))
                .collect(),
        })
    }
}

/// Execute a compiled sibling-finder grammar for one decomposition automaton.
///
/// Ground programs are initialized first. Every newly created product state
/// then activates the affected term variables, processes new root items against
/// the source-rule trie, and processes older root items through the reverse
/// child index. The loop ends at the least fixed point of reachable product
/// states and rules.
///
/// The concrete `D`, factory, and sibling-index types remain generic throughout
/// this call, allowing Rust to monomorphize partner queries into the algebra's
/// chosen lookup operations.
#[allow(clippy::type_complexity)]
pub(crate) fn materialize_compiled<D, F>(
    decomp: &D,
    compiled: &CompiledSiblingGrammar,
    sibling_indexes: &F,
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
    D: BottomUpTa,
    D::State: Clone + Eq + Hash,
    F: SiblingIndexFactory<D>,
{
    control.check()?;
    let CompiledSiblingGrammar {
        programs,
        by_left_child,
        ..
    } = compiled;

    let mut running: Vec<RunningProgram<'_, F::Index>> = programs
        .iter()
        .map(|program| RunningProgram::new(program, decomp, sibling_indexes))
        .collect::<Result<_, _>>()?;
    let mut materializer = Materializer::new(decomp, compiled);
    let mut new_roots = Vec::<usize>::new();
    let mut candidate_rules = Vec::<usize>::new();

    // Ground images need no product state to activate them. They seed the outer
    // agenda with any source rules they can already complete.
    for program in 0..programs.len() {
        if programs[program].term.arity() != 0 {
            continue;
        }
        new_roots.clear();
        let mut evaluation = StepContext {
            decomp,
            right_states: &mut materializer.right_states,
            stats: &mut materializer.stats,
            control,
        };
        running[program].seed_constants(&mut evaluation);
        running[program].propagate(&mut evaluation, &mut new_roots)?;
        for root_id in new_roots.drain(..) {
            let (root_right, root_children) = running[program].root(root_id);
            if let Some(candidate_rules) = running[program].compiled.left_rules.get(&[]) {
                for &rule_id in candidate_rules {
                    materializer.try_emit(rule_id, root_id, root_right, root_children);
                }
            }
        }
    }

    while let Some((left_state, right_state)) = materializer.agenda.pop_front() {
        control.check()?;
        materializer.stats.agenda_pops += 1;
        let occurrence_groups = &by_left_child[left_state.index()];
        for group in occurrence_groups {
            let program = group.program;
            let variable = group.variable;

            // The new product state may complete a condensed transition that
            // was already present before this activation.
            for &root_id in running[program].roots_with_child(variable, right_state) {
                let (root_right, root_children) = running[program].root(root_id);
                for &rule_id in &group.rule_ids {
                    materializer.try_emit(rule_id, root_id, root_right, root_children);
                }
            }

            new_roots.clear();
            let mut evaluation = StepContext {
                decomp,
                right_states: &mut materializer.right_states,
                stats: &mut materializer.stats,
                control,
            };
            running[program].activate(variable, right_state, &mut evaluation, &mut new_roots)?;

            // New condensed transitions meet product states that may already
            // exist. The trie finds every source rule whose children match.
            for root_id in new_roots.drain(..) {
                let (root_right, root_children) = running[program].root(root_id);
                let mut child_sets = SmallVec::<[&FxHashMap<StateId, StateId>; 4]>::new();
                let mut complete = true;
                for child in root_children {
                    if let Some(row) = materializer.products.left_partners(*child) {
                        child_sets.push(row);
                    } else {
                        complete = false;
                        break;
                    }
                }
                if !complete {
                    continue;
                }
                candidate_rules.clear();
                running[program]
                    .compiled
                    .left_rules
                    .for_each_value_for_key_sets(&child_sets, |matches| {
                        candidate_rules.extend_from_slice(matches);
                    });
                drop(child_sets);
                for &rule_id in &candidate_rules {
                    materializer.try_emit(rule_id, root_id, root_right, root_children);
                }
            }
        }
    }

    materializer.stats.output_states = materializer.pairs.len();
    let chart = materializer.builder.build_trusted();
    materializer.stats.output_rules = chart.rules().count();
    Ok((
        chart,
        materializer.right_states,
        materializer.pairs,
        materializer.stats,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assignments_use_node_local_width_and_participate_in_item_identity() {
        let mut narrow = NodeItems::<()>::new(1, None);
        let mut wide = NodeItems::<()>::new(3, None);
        let first = [StateId(0), StateId(1), StateId(2)];
        let second = [StateId(0), StateId(1), StateId(3)];

        assert_eq!(narrow.insert(StateId(7), &[StateId(1)]), Some(0));
        assert_eq!(wide.insert(StateId(7), &first), Some(0));
        assert_eq!(wide.insert(StateId(7), &first), None);
        assert_eq!(wide.insert(StateId(7), &second), Some(1));

        assert_eq!(narrow.assignments.len(), 1);
        assert_eq!(wide.items.len(), 2);
        assert_eq!(wide.assignments.len(), 6);
        assert_eq!(wide.assignment(0), first);
        assert_eq!(wide.assignment(1), second);
    }

    #[test]
    fn root_assignment_is_reordered_without_per_item_storage() {
        let mut assignment = Vec::new();
        merge_assignments_into(
            &[StateId(10), StateId(20)],
            &[StateId(30)],
            &[2, 0, 1],
            &mut assignment,
        );
        assert_eq!(assignment, [StateId(30), StateId(10), StateId(20)]);

        copy_assignment_into(
            &[StateId(10), StateId(20), StateId(30)],
            &[2, 0, 1],
            &mut assignment,
        );
        assert_eq!(assignment, [StateId(30), StateId(10), StateId(20)]);
    }

    #[test]
    fn compilation_records_only_a_root_permutation() {
        let mut arena = TreeArena::new();
        let variable_one = arena.add_node(HomLabel::Var(1), Vec::new());
        let variable_zero = arena.add_node(HomLabel::Var(0), Vec::new());
        let root = arena.add_node(
            HomLabel::Symbol(Symbol(0)),
            vec![variable_one, variable_zero],
        );

        let plan = compile_term(&arena, root, 2).unwrap();

        assert_eq!(plan.root_permutation.as_slice(), [1, 0]);
        assert_eq!(plan.nodes[plan.variable_nodes[1]].assignment_width(), 1);
        assert_eq!(plan.nodes[plan.variable_nodes[0]].assignment_width(), 1);
        assert_eq!(plan.nodes[ROOT_NODE].assignment_width(), 2);
    }
}
