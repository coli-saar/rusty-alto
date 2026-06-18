use crate::{
    Arity, BottomUpTa, CondensedTa, CondensedTopDownTa, Explicit, ExplicitBuilder, FxHashSet,
    Interner, KeySet, Memo, SetTrie, StateId, Symbol, SymbolSet, run::cartesian_product,
};
use fixedbitset::FixedBitSet;
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::hash::Hash;

type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;

#[cfg(feature = "stats")]
macro_rules! stat_inc {
    ($stats:expr, $field:ident) => {
        $stats.$field += 1;
    };
}

#[cfg(not(feature = "stats"))]
macro_rules! stat_inc {
    ($stats:expr, $field:ident) => {};
}

/// Explore a finite automaton and return an equivalent explicit fragment.
///
/// `materialize` starts from all nullary symbols in `alphabet`, repeatedly
/// queries transitions over already discovered states, and freezes every
/// queried rule into an [`Explicit`] automaton. The returned [`Interner`] maps
/// the explicit [`StateId`] values back to the original state type.
///
/// The caller must provide a finite alphabet as `(symbol, arity)` pairs. The
/// construction terminates when the reachable state space is finite. If the
/// implicit automaton can keep producing fresh states forever, this function
/// will also keep exploring.
///
/// Arity 0, 1, and 2 are handled directly. Higher arities are supported but can
/// be expensive because the number of state tuples grows exponentially.
pub fn materialize<A: BottomUpTa>(
    a: &A,
    alphabet: &[(Symbol, Arity)],
) -> (Explicit, Interner<A::State>) {
    let memo = Memo::new(a);
    let mut known = Vec::<StateId>::new();
    let mut known_bits = FixedBitSet::new();
    let mut worklist = Vec::<StateId>::new();

    for &(symbol, arity) in alphabet {
        if arity == 0 {
            collect_step(
                &memo,
                symbol,
                &[],
                &mut known,
                &mut known_bits,
                &mut worklist,
            );
        }
    }

    while let Some(popped) = worklist.pop() {
        let snapshot = known.clone();
        for &(symbol, arity) in alphabet {
            match arity {
                0 => {}
                1 => collect_step(
                    &memo,
                    symbol,
                    &[popped],
                    &mut known,
                    &mut known_bits,
                    &mut worklist,
                ),
                2 => {
                    for &other in &snapshot {
                        collect_step(
                            &memo,
                            symbol,
                            &[popped, other],
                            &mut known,
                            &mut known_bits,
                            &mut worklist,
                        );
                        if other != popped {
                            collect_step(
                                &memo,
                                symbol,
                                &[other, popped],
                                &mut known,
                                &mut known_bits,
                                &mut worklist,
                            );
                        }
                    }
                }
                n => {
                    let pools = vec![snapshot.as_slice(); n as usize];
                    cartesian_product(&pools, |tuple| {
                        if tuple.contains(&popped) {
                            collect_step(
                                &memo,
                                symbol,
                                tuple,
                                &mut known,
                                &mut known_bits,
                                &mut worklist,
                            );
                        }
                    });
                }
            }
        }
    }

    memo.into_explicit()
}

fn collect_step<A: BottomUpTa>(
    memo: &Memo<&A>,
    symbol: Symbol,
    children: &[StateId],
    known: &mut Vec<StateId>,
    known_bits: &mut FixedBitSet,
    worklist: &mut Vec<StateId>,
) {
    memo.step(symbol, children, &mut |q| {
        if !known_bits.contains(q.index()) {
            known_bits.grow(q.index() + 1);
            known_bits.set(q.index(), true);
            known.push(q);
            worklist.push(q);
        }
    });
}

/// Counters collected by [`materialize_indexed_condensed_intersection`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct IndexedCondensedIntersectionStats {
    /// Number of product states in the materialized intersection.
    pub output_states: usize,
    /// Number of product rules in the materialized intersection.
    pub output_rules: usize,
    /// Number of right-side condensed nullary rule shapes visited.
    pub right_nullary_rules: usize,
    /// Number of right-side indexed condensed queries issued.
    pub right_indexed_queries: usize,
    /// Number of product states popped from the work queue.
    #[cfg(feature = "stats")]
    pub queue_pops: usize,
    /// Number of left-rule child occurrences considered from reached product states.
    #[cfg(feature = "stats")]
    pub left_occurrences_considered: usize,
    /// Number of right condensed rules scanned while joining with left occurrences.
    #[cfg(feature = "stats")]
    pub right_rules_scanned: usize,
    /// Number of candidate pairs that matched on symbol and arity.
    #[cfg(feature = "stats")]
    pub symbol_arity_matches: usize,
    /// Number of candidate pairs whose child product states already existed.
    #[cfg(feature = "stats")]
    pub child_tuple_matches: usize,
}

impl IndexedCondensedIntersectionStats {
    /// Total number of right-side nullary shapes plus indexed queries.
    pub fn right_queries(&self) -> usize {
        self.right_nullary_rules + self.right_indexed_queries
    }
}

#[derive(Clone)]
pub(crate) struct OwnedRule {
    pub(crate) symbol: Symbol,
    pub(crate) children: SmallVec<[StateId; 2]>,
    pub(crate) result: StateId,
    pub(crate) weight: f64,
}

#[derive(Clone)]
pub(crate) struct OwnedCondensedRule<S> {
    pub(crate) children: SmallVec<[S; 2]>,
    pub(crate) symbols: SymbolSet,
    pub(crate) result: S,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ProductStateMap {
    by_right: Vec<FxHashMap<StateId, StateId>>,
}

impl ProductStateMap {
    fn new() -> Self {
        Self::default()
    }

    pub(crate) fn get(&self, left: StateId, right: StateId) -> Option<StateId> {
        self.by_right
            .get(right.index())
            .and_then(|partners| partners.get(&left).copied())
    }

    pub(crate) fn insert(&mut self, left: StateId, right: StateId, product: StateId) {
        if self.by_right.len() <= right.index() {
            self.by_right
                .resize_with(right.index() + 1, FxHashMap::default);
        }
        self.by_right[right.index()].insert(left, product);
    }
}

#[derive(Debug, Default)]
pub(crate) struct TrustedRuleTracker {
    #[cfg(debug_assertions)]
    seen: FxHashSet<(Symbol, SmallVec<[StateId; 2]>, StateId)>,
}

impl TrustedRuleTracker {
    pub(crate) fn add_rule(
        &mut self,
        builder: &mut ExplicitBuilder,
        symbol: Symbol,
        children: SmallVec<[StateId; 2]>,
        parent: StateId,
        weight: f64,
    ) {
        #[cfg(debug_assertions)]
        {
            let key = (symbol, children.clone(), parent);
            debug_assert!(
                self.seen.insert(key),
                "trusted materializer generated a duplicate transition"
            );
        }

        builder.add_weighted_rule_inline(symbol, children, parent, weight);
    }
}

#[derive(Clone, Copy)]
enum StateSetView<'a> {
    One(StateId),
    Many(&'a FxHashSet<StateId>),
}

impl KeySet<StateId> for StateSetView<'_> {
    fn len(&self) -> usize {
        match self {
            StateSetView::One(_) => 1,
            StateSetView::Many(states) => states.len(),
        }
    }

    fn contains(&self, key: &StateId) -> bool {
        match self {
            StateSetView::One(state) => state == key,
            StateSetView::Many(states) => states.contains(key),
        }
    }

    fn for_each(&self, out: &mut dyn FnMut(&StateId)) {
        match self {
            StateSetView::One(state) => out(state),
            StateSetView::Many(states) => {
                for state in *states {
                    out(state);
                }
            }
        }
    }
}

#[derive(Default)]
pub(crate) struct LeftIndex {
    nullary_by_symbol: FxHashMap<Symbol, Vec<usize>>,
    pub(crate) by_state: FxHashMap<StateId, Vec<(Symbol, usize, usize)>>,
    by_children: SetTrie<StateId, FxHashMap<Symbol, Vec<usize>>>,
    by_rotated_children: Vec<SetTrie<StateId, FxHashMap<Symbol, Vec<usize>>>>,
}

impl LeftIndex {
    pub(crate) fn build(rules: &[OwnedRule]) -> Self {
        Self::build_filtered(rules, |_, _| true)
    }

    pub(crate) fn build_filtered(
        rules: &[OwnedRule],
        mut include: impl FnMut(usize, &OwnedRule) -> bool,
    ) -> Self {
        let mut index = Self::default();
        for (rule_idx, rule) in rules.iter().enumerate() {
            if !include(rule_idx, rule) {
                continue;
            }
            index
                .by_children
                .get_or_insert_with(&rule.children, FxHashMap::default)
                .entry(rule.symbol)
                .or_default()
                .push(rule_idx);
            if rule.children.is_empty() {
                index
                    .nullary_by_symbol
                    .entry(rule.symbol)
                    .or_default()
                    .push(rule_idx);
            }
            for (position, &child) in rule.children.iter().enumerate() {
                index
                    .by_state
                    .entry(child)
                    .or_default()
                    .push((rule.symbol, position, rule_idx));
                if index.by_rotated_children.len() <= position {
                    index
                        .by_rotated_children
                        .resize_with(position + 1, SetTrie::default);
                }
                let mut rotated_children = SmallVec::<[StateId; 4]>::new();
                rotated_children.push(child);
                rotated_children.extend(rule.children[..position].iter().copied());
                rotated_children.extend(rule.children[position + 1..].iter().copied());
                index.by_rotated_children[position]
                    .get_or_insert_with(&rotated_children, FxHashMap::default)
                    .entry(rule.symbol)
                    .or_default()
                    .push(rule_idx);
            }
        }
        index
    }

    pub(crate) fn rule_indexes_for_sets_into<S>(
        &self,
        symbols: &SymbolSet,
        child_sets: &[S],
        out: &mut Vec<usize>,
    ) where
        S: KeySet<StateId>,
    {
        out.clear();
        self.by_children
            .for_each_value_for_key_sets(child_sets, |rules_by_symbol| {
                if symbols.len() < rules_by_symbol.len() {
                    for symbol in symbols.iter() {
                        if let Some(rule_indexes) = rules_by_symbol.get(&symbol) {
                            out.extend(rule_indexes.iter().copied());
                        }
                    }
                } else {
                    for (&symbol, rule_indexes) in rules_by_symbol {
                        if symbols.contains(symbol) {
                            out.extend(rule_indexes.iter().copied());
                        }
                    }
                }
            });
    }

    fn extend_symbol_matches(
        symbols: &SymbolSet,
        rules_by_symbol: &FxHashMap<Symbol, Vec<usize>>,
        out: &mut Vec<usize>,
    ) {
        if symbols.len() < rules_by_symbol.len() {
            for symbol in symbols.iter() {
                if let Some(rule_indexes) = rules_by_symbol.get(&symbol) {
                    out.extend(rule_indexes.iter().copied());
                }
            }
        } else {
            for (&symbol, rule_indexes) in rules_by_symbol {
                if symbols.contains(symbol) {
                    out.extend(rule_indexes.iter().copied());
                }
            }
        }
    }

    #[allow(dead_code)]
    pub(crate) fn rule_indexes_for_rotated_sets_into<S>(
        &self,
        trigger_position: usize,
        symbols: &SymbolSet,
        rotated_child_sets: &[S],
        out: &mut Vec<usize>,
    ) where
        S: KeySet<StateId>,
    {
        out.clear();
        let Some(trie) = self.by_rotated_children.get(trigger_position) else {
            return;
        };
        trie.for_each_value_for_key_sets(rotated_child_sets, |rules_by_symbol| {
            Self::extend_symbol_matches(symbols, rules_by_symbol, out);
        });
    }

    pub(crate) fn rule_indexes_for_rotated_trigger_sets_into<S>(
        &self,
        trigger_position: usize,
        trigger_left: StateId,
        symbols: &SymbolSet,
        sibling_sets: &[S],
        out: &mut Vec<usize>,
    ) where
        S: KeySet<StateId>,
    {
        out.clear();
        let Some(trie) = self.by_rotated_children.get(trigger_position) else {
            return;
        };
        trie.for_each_value_for_prefix_and_key_sets(
            &[trigger_left],
            sibling_sets,
            |rules_by_symbol| {
                Self::extend_symbol_matches(symbols, rules_by_symbol, out);
            },
        );
    }
}

/// A matched nullary edge from `for_each_nullary_edge`.
pub(crate) struct NullaryEdge {
    pub(crate) rule_index: usize,
    pub(crate) parent_left: StateId,
    pub(crate) parent_right: StateId,
    pub(crate) symbol: Symbol,
    pub(crate) weight: f64,
}

/// A candidate non-nullary edge from `for_each_candidate_edge`.
pub(crate) struct CandidateEdge {
    pub(crate) parent_left: StateId,
    pub(crate) parent_right: StateId,
    pub(crate) children: SmallVec<[StateId; 2]>,
    pub(crate) weight: f64,
    pub(crate) symbol: Symbol,
    pub(crate) trigger_position: usize,
}

/// Intern all right-side nullary results and match them against left nullary
/// rules. Calls `on_edge` for every matched (left_rule, right_result) pair.
/// Increments `stats.right_nullary_rules` once per right condensed nullary
/// shape.
pub(crate) trait StateInterner<T> {
    fn intern(&mut self, state: T) -> StateId;
}

impl<T> StateInterner<T> for Interner<T>
where
    T: Clone + Eq + Hash,
{
    fn intern(&mut self, state: T) -> StateId {
        Interner::intern(self, state)
    }
}

pub(crate) fn for_each_nullary_edge<R, I>(
    left_rules: &[OwnedRule],
    left_index: &LeftIndex,
    right: &R,
    right_interner: &mut I,
    stats: &mut IndexedCondensedIntersectionStats,
    on_edge: &mut dyn FnMut(NullaryEdge),
) where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: StateInterner<R::State>,
{
    right.condensed_nullary_rules(&mut |symbols, right_result| {
        stats.right_nullary_rules += 1;
        let right_result = right_interner.intern(right_result);
        for symbol in symbols.iter() {
            let Some(left_rule_indexes) = left_index.nullary_by_symbol.get(&symbol) else {
                continue;
            };
            for &left_rule_idx in left_rule_indexes {
                let left_rule = &left_rules[left_rule_idx];
                on_edge(NullaryEdge {
                    rule_index: left_rule_idx,
                    parent_left: left_rule.result,
                    parent_right: right_result,
                    symbol,
                    weight: left_rule.weight,
                });
            }
        }
    });
}

/// For a single trigger product state, assemble candidate non-nullary edges.
/// Queries right condensed rules indexed by `(trigger_position, trigger_right)`,
/// caches results, and calls `on_edge` for every candidate where all sibling
/// children already have product IDs. Does not check `current_product_is_latest`
/// or intern the parent — those are caller responsibilities.
///
/// Increments `stats.right_indexed_queries` on cache misses.
#[allow(clippy::too_many_arguments)]
pub(crate) fn for_each_candidate_edge<R: CondensedTa>(
    trigger_left: StateId,
    trigger_right: StateId,
    trigger_product: StateId,
    left_rules: &[OwnedRule],
    left_index: &LeftIndex,
    product_ids: &ProductStateMap,
    right: &R,
    right_interner: &mut Interner<R::State>,
    right_by_child_cache: &mut FxHashMap<(usize, StateId), Vec<OwnedCondensedRule<StateId>>>,
    stats: &mut IndexedCondensedIntersectionStats,
    on_edge: &mut dyn FnMut(CandidateEdge),
) where
    R::State: Clone + Eq + Hash,
{
    let Some(left_occurrences) = left_index.by_state.get(&trigger_left) else {
        return;
    };

    for &(symbol, position, left_rule_idx) in left_occurrences {
        stat_inc!(stats, left_occurrences_considered);
        let left_rule = &left_rules[left_rule_idx];
        let cache_key = (position, trigger_right);
        let right_rules = right_by_child_cache.entry(cache_key).or_insert_with(|| {
            stats.right_indexed_queries += 1;
            let raw_state = right_interner.resolve(trigger_right).clone();
            let mut collected = Vec::new();
            right.condensed_rules_by_child(
                position,
                &raw_state,
                &mut |children, symbols, result| {
                    collected.push(OwnedCondensedRule {
                        children: children
                            .iter()
                            .cloned()
                            .map(|child| right_interner.intern(child))
                            .collect(),
                        symbols: symbols.clone(),
                        result: right_interner.intern(result),
                    });
                },
            );
            collected
        });

        for right_rule in right_rules {
            stat_inc!(stats, right_rules_scanned);
            if !right_rule.symbols.contains(symbol)
                || right_rule.children.len() != left_rule.children.len()
            {
                continue;
            }
            stat_inc!(stats, symbol_arity_matches);

            let mut children = SmallVec::<[StateId; 2]>::new();
            let mut ok = true;
            for (child_position, (&left_child, &right_child)) in left_rule
                .children
                .iter()
                .zip(&right_rule.children)
                .enumerate()
            {
                if child_position == position
                    && left_child == trigger_left
                    && right_child == trigger_right
                {
                    children.push(trigger_product);
                } else if let Some(child) = product_ids.get(left_child, right_child) {
                    children.push(child);
                } else {
                    ok = false;
                    break;
                }
            }
            if !ok {
                continue;
            }
            stat_inc!(stats, child_tuple_matches);

            on_edge(CandidateEdge {
                parent_left: left_rule.result,
                parent_right: right_rule.result,
                children,
                weight: left_rule.weight,
                symbol,
                trigger_position: position,
            });
        }
    }
}

/// Materialize the intersection of an explicit grammar automaton with a
/// condensed right automaton using indexed condensed right-side queries.
///
/// The right automaton is not eagerly enumerated. Nullary rules are driven from
/// right condensed nullary shapes, and non-nullary rules are queried by
/// `(child_position, right_child_state)` as product states become reachable.
/// The returned interner maps the right component of product states back to
/// right automaton states; output state IDs are dense product-state IDs.
pub fn materialize_indexed_condensed_intersection<R>(
    left: &Explicit,
    right: &R,
) -> (
    Explicit,
    Interner<R::State>,
    IndexedCondensedIntersectionStats,
)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let (explicit, right_interner, _pairs, stats) =
        materialize_indexed_condensed_intersection_with_pairs(left, right);
    (explicit, right_interner, stats)
}

/// Like [`materialize_indexed_condensed_intersection`], but also returns the
/// `product_pairs` mapping: `pairs[s.index()] = (left_state, right_state)` for
/// every output product state `s`, where `right_state` resolves through the
/// returned interner. Used by analysis tooling (e.g. the F-heuristic probe) that
/// needs to recover the `(grammar state, right state)` identity of each fine
/// product state.
pub fn materialize_indexed_condensed_intersection_with_pairs<R>(
    left: &Explicit,
    right: &R,
) -> (
    Explicit,
    Interner<R::State>,
    Vec<(StateId, StateId)>,
    IndexedCondensedIntersectionStats,
)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let left_rules: Vec<_> = left
        .rules()
        .map(|rule| OwnedRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
            weight: rule.weight,
        })
        .collect();
    let left_index = LeftIndex::build(&left_rules);

    let mut right_interner = Interner::new();
    let mut product_ids = ProductStateMap::new();
    let mut product_pairs = Vec::<(StateId, StateId)>::new();
    let mut queue = VecDeque::<(StateId, StateId, StateId)>::new();
    let mut builder = ExplicitBuilder::new();
    let mut rule_tracker = TrustedRuleTracker::default();
    let mut right_by_child_cache =
        FxHashMap::<(usize, StateId), Vec<OwnedCondensedRule<StateId>>>::default();
    let mut stats = IndexedCondensedIntersectionStats::default();

    // Collect nullary edges first, then apply them (avoids borrow conflict on
    // right_interner which is both mutated by the helper and read in get_or_create_product_id).
    let mut nullary_edges = Vec::<NullaryEdge>::new();
    for_each_nullary_edge(
        &left_rules,
        &left_index,
        right,
        &mut right_interner,
        &mut stats,
        &mut |edge| nullary_edges.push(edge),
    );
    for edge in nullary_edges {
        let (parent, is_new) = get_or_create_product_id(
            edge.parent_left,
            edge.parent_right,
            left,
            right,
            &mut product_ids,
            &mut product_pairs,
            &right_interner,
            &mut builder,
        );
        if is_new {
            queue.push_back((edge.parent_left, edge.parent_right, parent));
        }
        rule_tracker.add_rule(
            &mut builder,
            edge.symbol,
            SmallVec::new(),
            parent,
            edge.weight,
        );
    }

    while let Some((left_state, right_state, current_product)) = queue.pop_front() {
        stat_inc!(stats, queue_pops);

        // Collect candidate edges first, then apply them (avoids borrow conflicts on
        // product_ids and right_interner which are both read/mutated by the helper and
        // the driver closure).
        let mut candidate_edges = Vec::<CandidateEdge>::new();
        for_each_candidate_edge(
            left_state,
            right_state,
            current_product,
            &left_rules,
            &left_index,
            &product_ids,
            right,
            &mut right_interner,
            &mut right_by_child_cache,
            &mut stats,
            &mut |edge| candidate_edges.push(edge),
        );
        for edge in candidate_edges {
            if !current_product_is_latest(&edge.children, edge.trigger_position, current_product) {
                continue;
            }

            let (parent, is_new) = get_or_create_product_id(
                edge.parent_left,
                edge.parent_right,
                left,
                right,
                &mut product_ids,
                &mut product_pairs,
                &right_interner,
                &mut builder,
            );
            if is_new {
                queue.push_back((edge.parent_left, edge.parent_right, parent));
            }
            rule_tracker.add_rule(
                &mut builder,
                edge.symbol,
                edge.children,
                parent,
                edge.weight,
            );
        }
    }

    stats.output_states = product_pairs.len();
    let explicit = builder.build_trusted();
    stats.output_rules = explicit.rules().count();
    (explicit, right_interner, product_pairs, stats)
}

/// Materialize the intersection using parent-indexed condensed right queries.
///
/// This mirrors Alto's condensed CKY-style intersection: traverse reachable
/// states of the right automaton from its top-down initial states, recursively
/// compute left partner states for right children, then join right condensed
/// rules against left grammar rules whose children are in those partner sets.
pub fn materialize_topdown_condensed_intersection<R>(
    left: &Explicit,
    right: &R,
) -> (
    Explicit,
    Interner<R::State>,
    IndexedCondensedIntersectionStats,
)
where
    R: CondensedTopDownTa,
    R::State: Clone + Eq + Hash,
{
    let left_rules: Vec<_> = left
        .rules()
        .map(|rule| OwnedRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
            weight: rule.weight,
        })
        .collect();
    let left_index = LeftIndex::build(&left_rules);

    let mut ctx = TopDownIntersection {
        left,
        right,
        left_rules: &left_rules,
        left_index: &left_index,
        right_interner: Interner::new(),
        product_ids: ProductStateMap::new(),
        product_pairs: Vec::new(),
        builder: ExplicitBuilder::new(),
        rule_tracker: TrustedRuleTracker::default(),
        partners: Vec::new(),
        visited: FixedBitSet::new(),
        matches_scratch: Vec::new(),
        stats: IndexedCondensedIntersectionStats::default(),
    };

    right.condensed_initial_states(&mut |q| {
        let q = ctx.intern_right(q);
        ctx.visit(q);
    });

    ctx.stats.output_states = ctx.product_pairs.len();
    let explicit = ctx.builder.build_trusted();
    ctx.stats.output_rules = explicit.rules().count();
    (explicit, ctx.right_interner, ctx.stats)
}

struct TopDownIntersection<'a, R>
where
    R: CondensedTopDownTa,
    R::State: Clone + Eq + Hash,
{
    left: &'a Explicit,
    right: &'a R,
    left_rules: &'a [OwnedRule],
    left_index: &'a LeftIndex,
    right_interner: Interner<R::State>,
    product_ids: ProductStateMap,
    product_pairs: Vec<(StateId, StateId)>,
    builder: ExplicitBuilder,
    rule_tracker: TrustedRuleTracker,
    partners: Vec<FxHashSet<StateId>>,
    visited: FixedBitSet,
    matches_scratch: Vec<usize>,
    stats: IndexedCondensedIntersectionStats,
}

impl<R> TopDownIntersection<'_, R>
where
    R: CondensedTopDownTa,
    R::State: Clone + Eq + Hash,
{
    fn intern_right(&mut self, state: R::State) -> StateId {
        let id = self.right_interner.intern(state);
        if self.partners.len() <= id.index() {
            self.partners
                .resize_with(id.index() + 1, FxHashSet::default);
        }
        if self.visited.len() <= id.index() {
            self.visited.grow(id.index() + 1);
        }
        id
    }

    fn visit(&mut self, q: StateId) {
        if self.visited.contains(q.index()) {
            return;
        }
        self.visited.set(q.index(), true);
        self.stats.right_indexed_queries += 1;

        let raw_parent = self.right_interner.resolve(q).clone();
        let mut normal_rules = SmallVec::<[OwnedCondensedRule<StateId>; 4]>::new();
        let mut loop_rules = SmallVec::<[OwnedCondensedRule<StateId>; 4]>::new();

        self.right
            .condensed_rules_by_parent(&raw_parent, &mut |symbols, children| {
                let children: SmallVec<[StateId; 2]> = children
                    .iter()
                    .cloned()
                    .map(|child| self.intern_right(child))
                    .collect();
                let rule = OwnedCondensedRule {
                    children,
                    symbols: symbols.clone(),
                    result: q,
                };
                if rule.children.iter().any(|&child| child == q) {
                    loop_rules.push(rule);
                } else {
                    normal_rules.push(rule);
                }
            });

        for right_rule in normal_rules {
            for &child in &right_rule.children {
                self.visit(child);
            }
            self.process_normal_rule(&right_rule);
        }

        for right_rule in &loop_rules {
            for &child in &right_rule.children {
                if child != q {
                    self.visit(child);
                }
            }
        }
        self.process_loop_rules(q, &loop_rules);
    }

    fn process_normal_rule(&mut self, right_rule: &OwnedCondensedRule<StateId>) {
        if !right_rule
            .children
            .iter()
            .all(|&child| self.has_partners(child))
        {
            return;
        }

        let child_sets = right_rule
            .children
            .iter()
            .map(|&child| &self.partners[child.index()])
            .collect::<SmallVec<[&FxHashSet<StateId>; 4]>>();
        self.left_index.rule_indexes_for_sets_into(
            &right_rule.symbols,
            &child_sets,
            &mut self.matches_scratch,
        );
        drop(child_sets);
        let matches = std::mem::take(&mut self.matches_scratch);
        for &rule_idx in &matches {
            let left_rule = &self.left_rules[rule_idx];
            self.collect_pair(left_rule, right_rule);
        }
        self.matches_scratch = matches;
    }

    fn process_loop_rules(&mut self, q: StateId, loop_rules: &[OwnedCondensedRule<StateId>]) {
        if !self.has_partners(q) {
            return;
        }

        for right_rule in loop_rules {
            for loop_position in right_rule
                .children
                .iter()
                .enumerate()
                .filter_map(|(position, &child)| (child == q).then_some(position))
            {
                let mut agenda = self.partners[q.index()]
                    .iter()
                    .copied()
                    .collect::<VecDeque<_>>();
                let mut seen = self.partners[q.index()].clone();

                while let Some(left_at_loop) = agenda.pop_front() {
                    let mut child_sets = SmallVec::<[StateSetView<'_>; 4]>::new();
                    let mut missing = false;
                    for (position, &right_child) in right_rule.children.iter().enumerate() {
                        if position == loop_position {
                            child_sets.push(StateSetView::One(left_at_loop));
                        } else if self.has_partners(right_child) {
                            child_sets
                                .push(StateSetView::Many(&self.partners[right_child.index()]));
                        } else {
                            missing = true;
                            break;
                        }
                    }
                    if missing {
                        continue;
                    }

                    self.left_index.rule_indexes_for_sets_into(
                        &right_rule.symbols,
                        &child_sets,
                        &mut self.matches_scratch,
                    );
                    drop(child_sets);
                    let matches = std::mem::take(&mut self.matches_scratch);

                    let mut newly_added = SmallVec::<[StateId; 4]>::new();
                    for &rule_idx in &matches {
                        let left_rule = &self.left_rules[rule_idx];
                        if self.collect_pair(left_rule, right_rule) && seen.insert(left_rule.result)
                        {
                            newly_added.push(left_rule.result);
                        }
                    }
                    for state in newly_added {
                        agenda.push_back(state);
                    }
                    self.matches_scratch = matches;
                }
            }
        }
    }

    fn has_partners(&self, right_state: StateId) -> bool {
        self.partners
            .get(right_state.index())
            .is_some_and(|partners| !partners.is_empty())
    }

    fn collect_pair(
        &mut self,
        left_rule: &OwnedRule,
        right_rule: &OwnedCondensedRule<StateId>,
    ) -> bool {
        let mut children = SmallVec::<[StateId; 2]>::new();
        for (&left_child, &right_child) in left_rule.children.iter().zip(&right_rule.children) {
            let Some(child_pair) = self.product_ids.get(left_child, right_child) else {
                return false;
            };
            children.push(child_pair);
        }

        let (parent, is_new_product) = get_or_create_product_id(
            left_rule.result,
            right_rule.result,
            self.left,
            self.right,
            &mut self.product_ids,
            &mut self.product_pairs,
            &self.right_interner,
            &mut self.builder,
        );
        if is_new_product {
            self.partners[right_rule.result.index()].insert(left_rule.result);
        }

        self.rule_tracker.add_rule(
            &mut self.builder,
            left_rule.symbol,
            children,
            parent,
            left_rule.weight,
        );
        is_new_product
    }
}

fn current_product_is_latest(
    children: &SmallVec<[StateId; 2]>,
    current_position: usize,
    current_product: StateId,
) -> bool {
    let mut latest = StateId(0);
    let mut first_latest_position = 0;
    for (position, &child) in children.iter().enumerate() {
        if position == 0 || child.0 > latest.0 {
            latest = child;
            first_latest_position = position;
        }
    }
    latest == current_product && first_latest_position == current_position
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn get_or_create_product_id<R>(
    left_state: StateId,
    right_state: StateId,
    left: &Explicit,
    right: &R,
    ids: &mut ProductStateMap,
    pairs: &mut Vec<(StateId, StateId)>,
    right_interner: &Interner<R::State>,
    builder: &mut ExplicitBuilder,
) -> (StateId, bool)
where
    R: BottomUpTa,
{
    if let Some(id) = ids.get(left_state, right_state) {
        return (id, false);
    }
    let id = builder.new_state();
    ids.insert(left_state, right_state, id);
    pairs.push((left_state, right_state));
    if left.is_accepting(&left_state) && right.is_accepting(right_interner.resolve(right_state)) {
        builder.add_accepting(id);
    }
    (id, true)
}

pub(crate) fn get_or_create_product_id_direct(
    left_state: StateId,
    right_state: StateId,
    ids: &mut ProductStateMap,
    pairs: &mut Vec<(StateId, StateId)>,
) -> (StateId, bool) {
    if let Some(id) = ids.get(left_state, right_state) {
        return (id, false);
    }

    let id = StateId(pairs.len() as u32);
    ids.insert(left_state, right_state, id);
    pairs.push((left_state, right_state));
    (id, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BottomUpTa, ExplicitBuilder};

    #[test]
    fn product_state_map_is_right_major_and_sparse() {
        let mut map = ProductStateMap::new();
        let left = StateId(7);
        let right = StateId(3);
        let product = StateId(11);

        assert_eq!(map.get(left, right), None);
        map.insert(left, right, product);
        assert_eq!(map.get(left, right), Some(product));
        assert_eq!(map.get(StateId(8), right), None);
        assert_eq!(map.get(left, StateId(4)), None);
    }

    #[test]
    fn state_set_view_matches_set_trie_traversal() {
        let mut trie = SetTrie::new();
        trie.get_or_insert_with(&[StateId(1), StateId(2)], Vec::new)
            .push("hit");
        trie.get_or_insert_with(&[StateId(3), StateId(2)], Vec::new)
            .push("miss");

        let second = FxHashSet::from_iter([StateId(2)]);
        let key_sets = [StateSetView::One(StateId(1)), StateSetView::Many(&second)];
        let mut values = Vec::new();
        trie.for_each_value_for_key_sets(&key_sets, |found| {
            values.extend(found.iter().copied());
        });

        assert_eq!(values, vec!["hit"]);
    }

    #[test]
    fn left_index_reuses_output_buffer_for_set_queries() {
        let symbol = Symbol(1);
        let other_symbol = Symbol(2);
        let q0 = StateId(0);
        let q1 = StateId(1);
        let rules = vec![
            OwnedRule {
                symbol,
                children: SmallVec::from_slice(&[q0, q1]),
                result: StateId(2),
                weight: 1.0,
            },
            OwnedRule {
                symbol: other_symbol,
                children: SmallVec::from_slice(&[q0, q1]),
                result: StateId(3),
                weight: 1.0,
            },
        ];
        let index = LeftIndex::build(&rules);
        let mut symbols = SymbolSet::default();
        symbols.insert(symbol);
        let first = FxHashSet::from_iter([q0]);
        let second = FxHashSet::from_iter([q1]);
        let key_sets = [&first, &second];
        let mut out = vec![usize::MAX];

        index.rule_indexes_for_sets_into(&symbols, &key_sets, &mut out);
        assert_eq!(out, vec![0]);

        symbols.insert(other_symbol);
        index.rule_indexes_for_sets_into(&symbols, &key_sets, &mut out);
        out.sort_unstable();
        assert_eq!(out, vec![0, 1]);
    }

    #[test]
    fn materializes_explicit_identity_fragment() {
        let a = Symbol(0);
        let f = Symbol(1);
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let root = b.new_state();
        b.add_rule(a, vec![], leaf);
        b.add_rule(f, vec![leaf, leaf], root);
        b.add_accepting(root);
        let explicit = b.build();

        let (mat, _interner) = materialize(&explicit, &[(a, 0), (f, 2)]);
        let mut leaves = Vec::new();
        mat.step(a, &[], &mut |q| leaves.push(q));
        let mut roots = Vec::new();
        mat.step(f, &[leaves[0], leaves[0]], &mut |q| roots.push(q));
        assert_eq!(roots.len(), 1);
        assert!(mat.is_accepting(&roots[0]));
    }

    #[test]
    fn topdown_condensed_intersection_matches_indexed_on_explicit_pair() {
        let a = Symbol(0);
        let f = Symbol(1);

        let mut left_builder = ExplicitBuilder::new();
        let left_leaf = left_builder.new_state();
        let left_root = left_builder.new_state();
        left_builder.add_rule(a, vec![], left_leaf);
        left_builder.add_rule(f, vec![left_leaf, left_leaf], left_root);
        left_builder.add_accepting(left_root);
        let left = left_builder.build();

        let mut right_builder = ExplicitBuilder::new();
        let right_leaf = right_builder.new_state();
        let right_root = right_builder.new_state();
        right_builder.add_rule(a, vec![], right_leaf);
        right_builder.add_rule(f, vec![right_leaf, right_leaf], right_root);
        right_builder.add_accepting(right_root);
        let right = right_builder.build();

        let (topdown, _, topdown_stats) = materialize_topdown_condensed_intersection(&left, &right);
        let (indexed, _, indexed_stats) = materialize_indexed_condensed_intersection(&left, &right);

        assert_eq!(topdown_stats.output_states, indexed_stats.output_states);
        assert_eq!(topdown_stats.output_rules, indexed_stats.output_rules);
        assert_eq!(topdown.rules().count(), indexed.rules().count());
        assert!(!topdown.is_empty());
    }
}
