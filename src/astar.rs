//! A* intersection materializer for weighted tree automata.
//!
//! This module provides two entry points:
//!
//! * [`materialize_astar_intersection`] — runs A* and emits a full (or beam-filtered)
//!   intersection chart as an [`Explicit`] automaton.
//!
//! * [`astar_one_best`] — runs A* in one-best mode and returns the highest-weighted
//!   accepted tree without building a chart.

mod lazy_span;
mod span;

use crate::{
    BottomUpTa, CondensedTa, DetBottomUpTa, Explicit, ExplicitBuilder, FxHashMap, Interner, InvHom,
    KeySet, ProbabilityScorer, Span, StateId, StringDecompositionAutomaton, Symbol, WeightScorer,
    algebras::{SpanProductSibling, SpanProductSiblingFinder},
    heuristic::IntersectionHeuristic,
    materialize::{
        IndexedCondensedIntersectionStats, LeftIndex, NullaryEdge, OwnedCondensedRule, OwnedRule,
        ProductStateMap, StateInterner, TrustedRuleTracker, for_each_nullary_edge,
        get_or_create_product_id_direct,
    },
    viterbi::{Backpointer, ViterbiTree, build_tree},
};
use fixedbitset::FixedBitSet;
use orx_priority_queue::{
    PriorityQueue, PriorityQueueDecKey, QuaternaryHeapOfIndices, ResUpdateKeyOrPush,
};
use rusty_tree::tree::TreeArena;
use smallvec::SmallVec;
use std::hash::Hash;

use lazy_span::{SiblingEntry, SpanGenerator, SpanLazyFrontier};
use span::{SpanAstarLeftIndex, SpanInterner};

trait RightStateInterner<T> {
    fn intern(&mut self, state: T) -> StateId;
    fn resolve(&self, id: StateId) -> &T;
    fn into_generic_interner(self) -> Interner<T>
    where
        T: Clone + Eq + Hash;
}

impl<T> RightStateInterner<T> for Interner<T>
where
    T: Clone + Eq + Hash,
{
    fn intern(&mut self, state: T) -> StateId {
        Interner::intern(self, state)
    }

    fn resolve(&self, id: StateId) -> &T {
        Interner::resolve(self, id)
    }

    fn into_generic_interner(self) -> Interner<T> {
        self
    }
}

impl RightStateInterner<Span> for SpanInterner {
    fn intern(&mut self, state: Span) -> StateId {
        SpanInterner::intern(self, state)
    }

    fn resolve(&self, id: StateId) -> &Span {
        SpanInterner::resolve(self, id)
    }

    fn into_generic_interner(self) -> Interner<Span> {
        SpanInterner::into_interner(self)
    }
}

impl StateInterner<Span> for SpanInterner {
    fn intern(&mut self, state: Span) -> StateId {
        SpanInterner::intern(self, state)
    }
}

pub struct PreparedAstarGrammar {
    left_rules: Vec<OwnedRule>,
    left_index: LeftIndex,
    span_left_index: SpanAstarLeftIndex,
}

impl PreparedAstarGrammar {
    pub fn new(left: &Explicit) -> Self {
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
        let span_left_index = SpanAstarLeftIndex::build(&left_rules);
        Self {
            left_rules,
            left_index,
            span_left_index,
        }
    }
}
#[derive(Default)]
struct ChildStateRightRuleIndex {
    cache: FxHashMap<(usize, StateId), Vec<usize>>,
}

impl ChildStateRightRuleIndex {
    /// Cache right automaton rules that mention a finalized right child at a
    /// given child position. This is the generic fallback used for automata
    /// where we do not have a more precise sibling index.
    fn rules_by_child<R, I>(
        &mut self,
        right: &R,
        right_interner: &mut I,
        right_rules: &mut Vec<OwnedCondensedRule<StateId>>,
        stats: &mut IndexedCondensedIntersectionStats,
        position: usize,
        right_state: StateId,
    ) -> &[usize]
    where
        R: CondensedTa,
        R::State: Clone + Eq + Hash,
        I: RightStateInterner<R::State>,
    {
        let cache_key = (position, right_state);
        if !self.cache.contains_key(&cache_key) {
            stats.right_indexed_queries += 1;
            let raw_state = right_interner.resolve(right_state).clone();
            let mut collected = Vec::new();
            right.condensed_rules_by_child(
                position,
                &raw_state,
                &mut |children, symbols, result| {
                    let rule_id = right_rules.len();
                    right_rules.push(OwnedCondensedRule {
                        children: children
                            .iter()
                            .cloned()
                            .map(|child| right_interner.intern(child))
                            .collect(),
                        symbols: symbols.clone(),
                        result: right_interner.intern(result),
                    });
                    collected.push(rule_id);
                },
            );
            self.cache.insert(cache_key, collected);
        }
        self.cache
            .get(&cache_key)
            .expect("cache entry was just inserted")
            .as_slice()
    }

    fn rule_ids_for_trigger_into<R, I>(
        &mut self,
        right: &R,
        right_interner: &mut I,
        right_rules: &mut Vec<OwnedCondensedRule<StateId>>,
        stats: &mut IndexedCondensedIntersectionStats,
        position: usize,
        right_state: StateId,
        out: &mut Vec<usize>,
    ) where
        R: CondensedTa,
        R::State: Clone + Eq + Hash,
        I: RightStateInterner<R::State>,
    {
        out.clear();
        let rules = self.rules_by_child(
            right,
            right_interner,
            right_rules,
            stats,
            position,
            right_state,
        );
        out.extend_from_slice(rules);
    }
}

#[derive(Default)]
struct PartnerSet {
    states: Vec<StateId>,
    bits: FixedBitSet,
    products_by_left: Vec<Option<StateId>>,
}

impl PartnerSet {
    fn insert(&mut self, state: StateId, product: StateId) -> bool {
        if self.bits.len() <= state.index() {
            self.bits.grow(state.index() + 1);
        }
        if self.products_by_left.len() <= state.index() {
            self.products_by_left.resize(state.index() + 1, None);
        }
        if self.bits.contains(state.index()) {
            return false;
        }
        self.bits.set(state.index(), true);
        self.products_by_left[state.index()] = Some(product);
        self.states.push(state);
        true
    }

    fn len(&self) -> usize {
        self.states.len()
    }

    fn contains(&self, state: &StateId) -> bool {
        state.index() < self.bits.len() && self.bits.contains(state.index())
    }

    fn iter(&self) -> impl Iterator<Item = &StateId> {
        self.states.iter()
    }

    fn product_for(&self, state: StateId) -> Option<StateId> {
        self.products_by_left.get(state.index()).and_then(|&p| p)
    }
}

impl KeySet<StateId> for PartnerSet {
    fn len(&self) -> usize {
        self.len()
    }

    fn contains(&self, key: &StateId) -> bool {
        self.contains(key)
    }

    fn for_each(&self, out: &mut dyn FnMut(&StateId)) {
        for state in self.iter() {
            out(state);
        }
    }
}

// ---------------------------------------------------------------------------
// Agenda item
// ---------------------------------------------------------------------------

/// The edge information stored with an agenda item.
struct EmitEdge {
    symbol: Symbol,
    children: SmallVec<[StateId; 2]>,
    weight: f64,
}

/// The payload for a pending item on the A* agenda. The heap itself stores only
/// the product-state index and the priority key.
struct AgendaItem {
    inside: f64,
    edge: EmitEdge,
}

struct FinalizedItem {
    product: StateId,
    edge: EmitEdge,
    inside: f64,
    left_state: StateId,
    right_state: StateId,
    is_goal: bool,
}

struct AstarAgenda {
    heap: QuaternaryHeapOfIndices<usize, f64>,
    index_bound: usize,
}

impl Default for AstarAgenda {
    fn default() -> Self {
        Self::with_index_bound(16 * 1024)
    }
}

impl AstarAgenda {
    fn with_index_bound(index_bound: usize) -> Self {
        Self {
            heap: QuaternaryHeapOfIndices::with_index_bound(index_bound),
            index_bound,
        }
    }

    fn ensure_index(&mut self, index: usize) {
        if index < self.index_bound {
            return;
        }
        let mut new_bound = self.index_bound.max(1);
        while index >= new_bound {
            new_bound *= 4;
        }
        let entries: Vec<_> = self.heap.as_slice().to_vec();
        let mut new_heap = QuaternaryHeapOfIndices::with_index_bound(new_bound);
        for (node, key) in entries {
            new_heap.push(node, key);
        }
        self.heap = new_heap;
        self.index_bound = new_bound;
    }

    fn update_or_push(&mut self, index: usize, merit: f64) -> ResUpdateKeyOrPush {
        self.ensure_index(index);
        // `orx` is a min-priority queue. Negating the merit gives max-merit A*
        // order without changing the scorer abstraction.
        self.heap.update_key_or_push(&index, -merit)
    }

    fn pop(&mut self) -> Option<usize> {
        self.heap.pop().map(|(index, _)| index)
    }

    /// Merit of the current top entry, or `None` when empty. The stored key is
    /// `-merit`, so the merit is its negation. Used by the lazy frontier to
    /// interleave finalization against lazy candidate generation by merit.
    fn peek_merit(&self) -> Option<f64> {
        self.heap.peek().map(|(_, neg_merit)| -neg_merit)
    }
}

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Options controlling the A* materializer behaviour.
pub struct AstarOptions {
    /// If `true`, stop as soon as the first goal (accepting product state) is
    /// finalized.  The output chart will contain exactly the states and rules
    /// needed to derive that one best tree.
    pub stop_at_first_goal: bool,
    /// Beam threshold.  When `Some(threshold)`, only agenda items with
    /// `merit >= threshold` are emitted into the chart.  Ignored when
    /// `stop_at_first_goal` is `true`.
    pub beam: Option<f64>,
}

/// Statistics collected by the A* materializer.
#[derive(Clone, Copy, Debug, Default)]
pub struct AstarStats {
    /// Number of items pushed onto the heap.
    pub heap_pushes: usize,
    /// Number of candidate pushes that superseded an older heap entry for the
    /// same product state. With the current lazy-duplicate heap, these are not
    /// decrease-key updates; they are the entries that a decrease-key heap
    /// would update in place.
    pub heap_updates: usize,
    /// Number of items popped from the heap (including re-opens that are skipped).
    pub pops: usize,
    /// Number of popped heap items discarded because a better version for the
    /// same product state was pushed later.
    pub stale_pops: usize,
    /// Number of distinct product states finalized.
    pub finalized_states: usize,
    /// Number of rules emitted into the output chart (chart mode only).
    pub emitted_rules: usize,
    /// Number of product states in the output chart (chart mode only).
    pub output_states: usize,
    /// Number of cached right-side child-index queries issued.
    pub right_indexed_queries: usize,
    /// Number of right-side condensed rules considered by incremental joins.
    pub right_rules_scanned: usize,
    /// Number of rotated left-index joins issued by A* candidate generation.
    pub rotated_left_join_queries: usize,
    /// Number of left rules returned by set-trie joins before product lookup.
    pub left_rule_matches: usize,
    /// Number of complete candidate edges considered for agenda insertion.
    pub candidate_edges: usize,
    /// Number of candidate edges discarded because they did not improve the
    /// best pending score for their parent product state.
    pub dominated_candidates: usize,
    /// Number of candidate edges discarded because their parent product state
    /// had already been finalized.
    pub finalized_candidate_discards: usize,
    /// Number of product-aware span sibling queries issued.
    pub sibling_tuple_queries: usize,
    /// Number of exact sibling products returned by the span sibling finder.
    pub sibling_tuples_returned: usize,
    /// Number of exact right-transition calls issued by the sibling-finder
    /// expansion path. The span path uses deterministic stepping when
    /// available.
    pub right_step_calls: usize,
    /// Number of right parent states returned by exact right-transition calls.
    pub right_step_results: usize,
    /// Number of finalized products expanded by the old set-trie path because
    /// at least one relevant left occurrence had arity greater than 2.
    pub sibling_fallback_expansions: usize,
    /// Number of agenda-item pops that were discarded because the state was
    /// already finalized.  For a consistent heuristic this should always be 0.
    pub reopen_attempts: usize,
    /// Lazy frontier: number of binary generators created (one per finalized
    /// product, child position, and sibling-left group with a non-empty
    /// snapshot).
    pub generators_created: usize,
    /// Lazy frontier: number of generator pops from the frontier heap.
    pub frontier_pops: usize,
    /// Lazy frontier: number of (sibling) realizations, i.e. distinct sibling
    /// slots whose rules were pushed to the parent agenda on demand.
    pub sibling_realizations: usize,
    /// Lazy frontier: number of individual candidate edges realized (rules
    /// pushed to the parent agenda). Compare against eager `candidate_edges`.
    pub candidates_realized: usize,
}

// ---------------------------------------------------------------------------
// Internal: `first_trigger` dedup predicate
// ---------------------------------------------------------------------------

/// Returns `true` iff `children[trigger_position] == trigger_product` AND no
/// *earlier* position in `children` also equals `trigger_product`.
///
/// This replaces `current_product_is_latest` from the BFS materializer: instead
/// of comparing numeric IDs we check that the trigger product is at the first
/// occurrence of itself in the children slice, which avoids emitting the same
/// parent rule multiple times when the same product state appears in more than
/// one child position.
#[inline]
fn first_trigger(
    children: &SmallVec<[StateId; 2]>,
    trigger_position: usize,
    trigger_product: StateId,
) -> bool {
    if children.get(trigger_position) != Some(&trigger_product) {
        return false;
    }
    // No earlier position may equal trigger_product.
    children[..trigger_position]
        .iter()
        .all(|&c| c != trigger_product)
}

fn string_product_heap_bound(left: &Explicit, n: usize) -> usize {
    let spans = n.saturating_mul(n + 1) / 2;
    (left.num_states() as usize).saturating_mul(spans).max(1024)
}

/// Whether to use the N10 lazy candidate-generation frontier on the
/// deterministic span/binary path. Gated by the `RUSTY_ALTO_LAZY_FRONTIER`
/// environment variable so the eager path remains the default and the A/B
/// baseline (the benchmarked one-best entry takes no `AstarOptions`). The caller
/// additionally requires a purely binary grammar (no higher-arity left rules).
fn lazy_frontier_enabled() -> bool {
    matches!(
        std::env::var("RUSTY_ALTO_LAZY_FRONTIER").as_deref(),
        Ok("1") | Ok("true")
    )
}

// ---------------------------------------------------------------------------
// Core A* loop (shared between the two entry points)
// ---------------------------------------------------------------------------

/// Context for the core A* loop. Kept in a struct so the hot path can reuse
/// buffers and indexes instead of allocating them at each finalized state.
struct AstarContext<'a, R, I = Interner<<R as BottomUpTa>::State>>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: RightStateInterner<R::State> + StateInterner<R::State>,
{
    left: &'a Explicit,
    right: &'a R,
    left_rules: &'a [OwnedRule],
    left_index: &'a LeftIndex,
    right_rule_index: ChildStateRightRuleIndex,
    right_interner: I,
    product_ids: ProductStateMap,
    product_pairs: Vec<(StateId, StateId)>,
    builder: Option<ExplicitBuilder>,
    rule_tracker: TrustedRuleTracker,
    right_rules: Vec<OwnedCondensedRule<StateId>>,
    mat_stats: IndexedCondensedIntersectionStats,
    // A* specific state
    finalized: FixedBitSet,
    finalized_partners: Vec<PartnerSet>,
    best_inside: Vec<f64>,
    /// Best inside score discovered so far for each product state.
    best_seen_inside: Vec<f64>,
    back: Vec<Option<Backpointer>>,
    store_backpointers: bool,
    heap: AstarAgenda,
    pending: Vec<Option<AgendaItem>>,
    matches_scratch: Vec<usize>,
    right_rule_ids_scratch: Vec<usize>,
    span_product_siblings_scratch: Vec<SpanProductSibling>,
    stats: AstarStats,
}

impl<'a, R, I> AstarContext<'a, R, I>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: RightStateInterner<R::State> + StateInterner<R::State>,
{
    fn new(
        left: &'a Explicit,
        right: &'a R,
        left_rules: &'a [OwnedRule],
        left_index: &'a LeftIndex,
        right_interner: I,
        with_builder: bool,
        heap_index_bound: usize,
    ) -> Self {
        let store_backpointers = !with_builder;
        Self {
            left,
            right,
            left_rules,
            left_index,
            right_rule_index: ChildStateRightRuleIndex::default(),
            right_interner,
            product_ids: ProductStateMap::default(),
            product_pairs: Vec::new(),
            builder: if with_builder {
                Some(ExplicitBuilder::new())
            } else {
                None
            },
            rule_tracker: TrustedRuleTracker::default(),
            right_rules: Vec::new(),
            mat_stats: IndexedCondensedIntersectionStats::default(),
            finalized: FixedBitSet::new(),
            finalized_partners: Vec::new(),
            best_inside: Vec::new(),
            best_seen_inside: Vec::new(),
            back: Vec::new(),
            store_backpointers,
            heap: AstarAgenda::with_index_bound(heap_index_bound.max(1024)),
            pending: Vec::new(),
            matches_scratch: Vec::new(),
            right_rule_ids_scratch: Vec::new(),
            span_product_siblings_scratch: Vec::new(),
            stats: AstarStats::default(),
        }
    }

    /// Ensure per-state arrays are large enough for `product`.
    fn grow_to(&mut self, product: StateId, zero: f64) {
        let idx = product.index() + 1;
        if self.finalized.len() < idx {
            self.finalized.grow(idx);
        }
        if self.best_inside.len() < idx {
            self.best_inside.resize(idx, 0.0);
        }
        if self.best_seen_inside.len() < idx {
            self.best_seen_inside.resize(idx, zero);
        }
        if self.back.len() < idx {
            if self.store_backpointers {
                self.back.resize(idx, None);
            }
        }
        if self.pending.len() < idx {
            self.pending.resize_with(idx, || None);
        }
    }

    fn ensure_right_state(&mut self, right: StateId) {
        if self.finalized_partners.len() <= right.index() {
            self.finalized_partners
                .resize_with(right.index() + 1, PartnerSet::default);
        }
    }

    fn get_or_create_direct(
        &mut self,
        left_state: StateId,
        right_state: StateId,
    ) -> (StateId, bool) {
        get_or_create_product_id_direct(
            left_state,
            right_state,
            &mut self.product_ids,
            &mut self.product_pairs,
        )
    }

    fn get_or_create_product_id(
        &mut self,
        left_state: StateId,
        right_state: StateId,
    ) -> (StateId, bool) {
        if let Some(id) = self.product_ids.get(left_state, right_state) {
            return (id, false);
        }

        let id = if let Some(builder) = &mut self.builder {
            let id = builder.new_state();
            if self.left.is_accepting(&left_state)
                && self
                    .right
                    .is_accepting(self.right_interner.resolve(right_state))
            {
                builder.add_accepting(id);
            }
            id
        } else {
            StateId(self.product_pairs.len() as u32)
        };
        self.product_ids.insert(left_state, right_state, id);
        self.product_pairs.push((left_state, right_state));
        (id, true)
    }

    /// Return `true` if `product` is an accepting product state.
    fn is_accepting_product(&self, product: StateId) -> bool {
        if product.index() >= self.product_pairs.len() {
            return false;
        }
        let (left_state, right_state) = self.product_pairs[product.index()];
        let right_raw = self.right_interner.resolve(right_state);
        self.left.is_accepting(&left_state) && self.right.is_accepting(right_raw)
    }

    fn rule_ids_for_trigger(&mut self, position: usize, trigger_right: StateId) -> Vec<usize> {
        let mut out = std::mem::take(&mut self.right_rule_ids_scratch);
        self.right_rule_index.rule_ids_for_trigger_into(
            self.right,
            &mut self.right_interner,
            &mut self.right_rules,
            &mut self.mat_stats,
            position,
            trigger_right,
            &mut out,
        );
        out
    }

    fn push_candidate<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        parent_left: StateId,
        parent_right: StateId,
        symbol: Symbol,
        weight: f64,
        children: SmallVec<[StateId; 2]>,
        scorer: &S,
        h: &H,
    ) {
        let mut child_score = scorer.one();
        for &child in &children {
            child_score = scorer.times(child_score, self.best_inside[child.index()]);
        }
        self.push_candidate_with_child_score(
            parent_left,
            parent_right,
            symbol,
            weight,
            children.as_slice(),
            child_score,
            scorer,
            h,
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn push_candidate_with_child_score<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        parent_left: StateId,
        parent_right: StateId,
        symbol: Symbol,
        weight: f64,
        children: &[StateId],
        child_score: f64,
        scorer: &S,
        h: &H,
    ) {
        let inside = scorer.times(scorer.rule_score(weight), child_score);
        let (parent, _) = if self.builder.is_some() {
            self.get_or_create_product_id(parent_left, parent_right)
        } else {
            self.get_or_create_direct(parent_left, parent_right)
        };
        self.grow_to(parent, scorer.zero());

        if self.finalized.contains(parent.index()) {
            self.stats.finalized_candidate_discards += 1;
            return;
        }

        let old_inside = self.best_seen_inside[parent.index()];
        if !scorer.better(inside, old_inside) {
            self.stats.dominated_candidates += 1;
            return;
        }
        self.best_seen_inside[parent.index()] = inside;

        let right_raw = self.right_interner.resolve(parent_right);
        let h_val = h.outside_estimate(parent_left, right_raw);
        let merit = scorer.times(inside, h_val);
        self.pending[parent.index()] = Some(AgendaItem {
            inside,
            edge: EmitEdge {
                symbol,
                children: children.iter().copied().collect(),
                weight,
            },
        });
        match self.heap.update_or_push(parent.index(), merit) {
            ResUpdateKeyOrPush::Pushed => self.stats.heap_pushes += 1,
            ResUpdateKeyOrPush::Decreased | ResUpdateKeyOrPush::Increased => {
                self.stats.heap_updates += 1;
            }
        }
    }

    fn expand_from_finalized<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        trigger_left: StateId,
        trigger_right: StateId,
        trigger_product: StateId,
        h: &H,
        scorer: &S,
    ) {
        let Some(left_occurrences) = self.left_index.by_state.get(&trigger_left) else {
            return;
        };
        // Generic expansion for arbitrary right automata and higher-arity
        // rules. For each child position where the finalized left state can
        // occur, retrieve right rules containing the finalized right state at
        // that position. The left index is then queried with the finalized
        // sibling partner sets, and concrete product children are resolved
        // before a candidate is pushed.
        let mut positions = SmallVec::<[usize; 4]>::new();
        for &(_, position, _) in left_occurrences {
            if !positions.contains(&position) {
                positions.push(position);
            }
        }

        for position in positions {
            let right_rule_ids = self.rule_ids_for_trigger(position, trigger_right);
            for &right_rule_id in &right_rule_ids {
                self.stats.right_rules_scanned += 1;
                let right_rule = &self.right_rules[right_rule_id];
                if right_rule.children.is_empty() {
                    continue;
                }
                let mut sibling_sets = SmallVec::<[&PartnerSet; 4]>::new();
                let mut missing = false;
                for (child_position, &right_child) in right_rule.children.iter().enumerate() {
                    if child_position == position {
                        continue;
                    } else if self
                        .finalized_partners
                        .get(right_child.index())
                        .is_some_and(|partners| partners.len() > 0)
                    {
                        sibling_sets.push(&self.finalized_partners[right_child.index()]);
                    } else {
                        missing = true;
                        break;
                    }
                }
                if missing {
                    continue;
                }
                let parent_right = right_rule.result;

                self.stats.rotated_left_join_queries += 1;
                self.left_index.rule_indexes_for_rotated_trigger_sets_into(
                    position,
                    trigger_left,
                    &right_rule.symbols,
                    sibling_sets.as_slice(),
                    &mut self.matches_scratch,
                );
                drop(sibling_sets);
                let matches = std::mem::take(&mut self.matches_scratch);
                self.stats.left_rule_matches += matches.len();

                for &rule_idx in &matches {
                    let Some((parent_left, symbol, weight, children)) = ({
                        let left_rule = &self.left_rules[rule_idx];
                        let right_rule = &self.right_rules[right_rule_id];
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
                            } else if let Some(child) = self
                                .finalized_partners
                                .get(right_child.index())
                                .and_then(|partners| partners.product_for(left_child))
                            {
                                children.push(child);
                            } else {
                                ok = false;
                                break;
                            }
                        }
                        (ok && first_trigger(&children, position, trigger_product)).then_some((
                            left_rule.result,
                            left_rule.symbol,
                            left_rule.weight,
                            children,
                        ))
                    }) else {
                        continue;
                    };
                    self.stats.candidate_edges += 1;
                    self.push_candidate(
                        parent_left,
                        parent_right,
                        symbol,
                        weight,
                        children,
                        scorer,
                        h,
                    );
                }

                self.matches_scratch = matches;
            }
            self.right_rule_ids_scratch = right_rule_ids;
        }
    }

    fn binary_right_parent_det(
        &mut self,
        symbol: Symbol,
        right_children: [StateId; 2],
    ) -> Option<StateId>
    where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        let raw_right_children = [
            *self.right_interner.resolve(right_children[0]),
            *self.right_interner.resolve(right_children[1]),
        ];
        self.stats.right_step_calls += 1;
        let parent = self.right.step_det(symbol, &raw_right_children)?;
        self.stats.right_step_results += 1;
        Some(RightStateInterner::intern(&mut self.right_interner, parent))
    }

    fn expand_from_finalized_with_span_product_siblings<
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    >(
        &mut self,
        trigger_left: StateId,
        trigger_right: StateId,
        trigger_product: StateId,
        span_left_index: &SpanAstarLeftIndex,
        sibling_finder: &SpanProductSiblingFinder,
        h: &H,
        scorer: &S,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        if span_left_index.has_higher_arity(trigger_left) {
            // The product-aware span sibling finder is a binary-rule
            // optimization. If this left state also appears in a larger rule,
            // run the generic expansion so those candidates are still found.
            self.stats.sibling_fallback_expansions += 1;
            self.expand_from_finalized(trigger_left, trigger_right, trigger_product, h, scorer);
            return;
        }

        let raw_trigger = *self.right_interner.resolve(trigger_right);

        // Unary rules do not need sibling lookup. In the string fast path the
        // right automaton is deterministic for concrete child spans, so this
        // avoids the allocation-heavy generic inverse-homomorphism step.
        if let Some(unary_rules) = span_left_index.unary_rules(trigger_left) {
            for &rule_idx in unary_rules {
                let (parent_left, symbol, weight) = {
                    let left_rule = &self.left_rules[rule_idx];
                    (left_rule.result, left_rule.symbol, left_rule.weight)
                };
                let children = [trigger_product];

                let raw_children = [raw_trigger];
                self.stats.right_step_calls += 1;
                let Some(parent) = self.right.step_det(symbol, &raw_children) else {
                    continue;
                };
                self.stats.right_step_results += 1;
                let parent_right = RightStateInterner::intern(&mut self.right_interner, parent);
                self.stats.candidate_edges += 1;
                self.push_candidate_with_child_score(
                    parent_left,
                    parent_right,
                    symbol,
                    weight,
                    &children,
                    self.best_inside[trigger_product.index()],
                    scorer,
                    h,
                );
            }
        }

        for position in 0..2 {
            let Some(groups) = span_left_index.binary_groups(trigger_left, position) else {
                continue;
            };

            for group in groups {
                // Query by span boundary and required sibling left state. Every
                // returned item is already a finalized product that can fill
                // the sibling slot for this group of left rules.
                let mut sibling_products = std::mem::take(&mut self.span_product_siblings_scratch);
                self.stats.sibling_tuple_queries += 1;
                sibling_finder.sibling_products_into(
                    raw_trigger,
                    position,
                    group.sibling_left,
                    &mut sibling_products,
                );
                self.stats.sibling_tuples_returned += sibling_products.len();

                for &sibling in &sibling_products {
                    let (children, right_children) = match position {
                        0 => (
                            [trigger_product, sibling.product],
                            [trigger_right, sibling.right_state],
                        ),
                        1 => (
                            [sibling.product, trigger_product],
                            [sibling.right_state, trigger_right],
                        ),
                        _ => unreachable!(),
                    };

                    if position == 1 && sibling.product == trigger_product {
                        continue;
                    }

                    let child_score = scorer.times(
                        self.best_inside[children[0].index()],
                        self.best_inside[children[1].index()],
                    );
                    for symbol_group in &group.symbol_groups {
                        // All left rules in this group share the same symbol
                        // and left-child requirements, so one deterministic
                        // right transition gives the parent state for all of
                        // them.
                        let Some(parent_right) =
                            self.binary_right_parent_det(symbol_group.symbol, right_children)
                        else {
                            continue;
                        };
                        for &rule_idx in &symbol_group.rule_indexes {
                            let left_rule = &self.left_rules[rule_idx];
                            debug_assert_eq!(left_rule.symbol, symbol_group.symbol);
                            debug_assert_eq!(left_rule.children[position], trigger_left);
                            debug_assert_eq!(left_rule.children[1 - position], group.sibling_left);
                            self.stats.candidate_edges += 1;
                            self.push_candidate_with_child_score(
                                left_rule.result,
                                parent_right,
                                symbol_group.symbol,
                                left_rule.weight,
                                &children,
                                child_score,
                                scorer,
                                h,
                            );
                        }
                    }
                }

                self.span_product_siblings_scratch = sibling_products;
            }
        }
    }

    /// Push a nullary seed item onto the heap.
    fn push_seed<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        edge: NullaryEdge,
        h: &H,
        scorer: &S,
    ) {
        let (product, _) = if self.builder.is_some() {
            self.get_or_create_product_id(edge.parent_left, edge.parent_right)
        } else {
            self.get_or_create_direct(edge.parent_left, edge.parent_right)
        };
        self.grow_to(product, scorer.zero());

        let inside = scorer.rule_score(edge.weight);
        let old_inside = self.best_seen_inside[product.index()];
        if !scorer.better(inside, old_inside) {
            self.stats.dominated_candidates += 1;
            return;
        }
        self.best_seen_inside[product.index()] = inside;

        let right_raw = self.right_interner.resolve(edge.parent_right);
        let h_val = h.outside_estimate(edge.parent_left, right_raw);
        let merit = scorer.times(inside, h_val);
        self.pending[product.index()] = Some(AgendaItem {
            inside,
            edge: EmitEdge {
                symbol: edge.symbol,
                children: SmallVec::new(),
                weight: edge.weight,
            },
        });
        match self.heap.update_or_push(product.index(), merit) {
            ResUpdateKeyOrPush::Pushed => self.stats.heap_pushes += 1,
            ResUpdateKeyOrPush::Decreased | ResUpdateKeyOrPush::Increased => {
                self.stats.heap_updates += 1;
            }
        }
    }

    fn seed_nullary_edges<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        h: &H,
        scorer: &S,
    ) {
        let mut nullary_edges = Vec::<NullaryEdge>::new();
        for_each_nullary_edge(
            self.left_rules,
            self.left_index,
            self.right,
            &mut self.right_interner,
            &mut self.mat_stats,
            &mut |edge| nullary_edges.push(edge),
        );
        for edge in nullary_edges {
            self.push_seed(edge, h, scorer);
        }
    }

    fn pop_next_finalized<S: WeightScorer>(
        &mut self,
        scorer: &S,
        store_finalized_partners: bool,
    ) -> Option<FinalizedItem> {
        while let Some(product_index) = self.heap.pop() {
            self.stats.pops += 1;
            let product = StateId(product_index as u32);
            let Some(item) = self.pending[product_index].take() else {
                self.stats.stale_pops += 1;
                continue;
            };

            if self.finalized.contains(product.index()) {
                if scorer.better(item.inside, self.best_inside[product.index()]) {
                    self.stats.reopen_attempts += 1;
                }
                continue;
            }

            self.finalized.set(product.index(), true);
            self.best_inside[product.index()] = item.inside;
            self.best_seen_inside[product.index()] = item.inside;
            if self.store_backpointers {
                self.back[product.index()] = Some(Backpointer {
                    symbol: item.edge.symbol,
                    children: item.edge.children.clone(),
                    weight: item.inside,
                });
            }
            self.stats.finalized_states += 1;

            let is_goal = self.is_accepting_product(product);
            let (left_state, right_state) = self.product_pairs[product.index()];
            if store_finalized_partners {
                self.ensure_right_state(right_state);
                self.finalized_partners[right_state.index()].insert(left_state, product);
            }

            return Some(FinalizedItem {
                product,
                edge: item.edge,
                inside: item.inside,
                left_state,
                right_state,
                is_goal,
            });
        }

        None
    }

    /// Run the core A* loop until the heap is exhausted or `stop` returns true.
    fn run<H, S, OnFin>(
        &mut self,
        h: &H,
        scorer: &S,
        stop_at_first_goal: bool,
        mut on_finalize: OnFin,
    ) where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
        OnFin: FnMut(&mut Self, StateId, &EmitEdge, f64),
    {
        while let Some(item) = self.pop_next_finalized(scorer, true) {
            on_finalize(self, item.product, &item.edge, item.inside);

            if item.is_goal && stop_at_first_goal {
                break;
            }

            self.expand_from_finalized(item.left_state, item.right_state, item.product, h, scorer);
        }
    }

    fn run_with_span_product_sibling_finder<H, S, OnFin>(
        &mut self,
        h: &H,
        scorer: &S,
        span_left_index: &SpanAstarLeftIndex,
        stop_at_first_goal: bool,
        mut on_finalize: OnFin,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
        OnFin: FnMut(&mut Self, StateId, &EmitEdge, f64),
    {
        let mut sibling_finder = SpanProductSiblingFinder::default();
        let store_finalized_partners = span_left_index.has_any_higher_arity();

        while let Some(item) = self.pop_next_finalized(scorer, store_finalized_partners) {
            let raw_right = *self.right_interner.resolve(item.right_state);
            span_left_index.activate_product(
                &mut sibling_finder,
                item.product,
                item.left_state,
                item.right_state,
                raw_right,
            );

            on_finalize(self, item.product, &item.edge, item.inside);

            if item.is_goal && stop_at_first_goal {
                break;
            }

            self.expand_from_finalized_with_span_product_siblings(
                item.left_state,
                item.right_state,
                item.product,
                span_left_index,
                &sibling_finder,
                h,
                scorer,
            );
        }
    }

    // -----------------------------------------------------------------------
    // N10: lazy candidate generation (span/binary fast path)
    // -----------------------------------------------------------------------

    /// Inside score and merit for a candidate edge, computed exactly as
    /// [`Self::push_candidate_with_child_score`] would. Used to key the lazy
    /// frontier without resolving (or creating) the parent product id.
    fn candidate_merit<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &self,
        parent_left: StateId,
        parent_right: StateId,
        weight: f64,
        child_score: f64,
        scorer: &S,
        h: &H,
    ) -> f64 {
        let inside = scorer.times(scorer.rule_score(weight), child_score);
        let right_raw = self.right_interner.resolve(parent_right);
        let h_val = h.outside_estimate(parent_left, right_raw);
        scorer.times(inside, h_val)
    }

    /// Best (maximum) merit over all rules that combine the trigger (filling
    /// `position`, right state `trigger_right`) with `sibling`, or `None` if no
    /// rule yields a valid right transition. All rules for one sibling share the
    /// same child pair, so they realize together.
    fn lazy_sibling_merit<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        trigger: StateId,
        trigger_right: StateId,
        position: u8,
        sibling: SpanProductSibling,
        group: &span::SpanBinarySiblingGroup,
        scorer: &S,
        h: &H,
    ) -> Option<f64>
    where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        if position == 1 && sibling.product == trigger {
            return None;
        }
        let right_children = match position {
            0 => [trigger_right, sibling.right_state],
            _ => [sibling.right_state, trigger_right],
        };
        let child_score = scorer.times(
            self.best_inside[trigger.index()],
            self.best_inside[sibling.product.index()],
        );
        let mut best: Option<f64> = None;
        for symbol_group in &group.symbol_groups {
            let Some(parent_right) =
                self.binary_right_parent_det(symbol_group.symbol, right_children)
            else {
                continue;
            };
            for &rule_idx in &symbol_group.rule_indexes {
                let (parent_left, weight) = {
                    let rule = &self.left_rules[rule_idx];
                    (rule.result, rule.weight)
                };
                let merit =
                    self.candidate_merit(parent_left, parent_right, weight, child_score, scorer, h);
                best = Some(best.map_or(merit, |b| b.max(merit)));
            }
        }
        best
    }

    /// Realize every rule that combines the generator's trigger with the sibling at
    /// `sibling_index`, pushing each onto the parent agenda (which keeps the
    /// dominance gate and decrease-key dedup).
    fn lazy_push_sibling_rules<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        g: &SpanGenerator,
        finder: &SpanProductSiblingFinder,
        sibling_index: usize,
        span_left_index: &SpanAstarLeftIndex,
        scorer: &S,
        h: &H,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        let span = *self.right_interner.resolve(g.trigger_right);
        let Some(groups) = span_left_index.binary_groups(g.trigger_left, g.position as usize)
        else {
            return;
        };
        let group = &groups[g.group_idx as usize];
        let siblings = finder.siblings_slice(span, g.position as usize, group.sibling_left);
        let sibling = siblings[sibling_index];
        if g.position == 1 && sibling.product == g.trigger {
            return;
        }
        let (children, right_children) = match g.position {
            0 => (
                [g.trigger, sibling.product],
                [g.trigger_right, sibling.right_state],
            ),
            _ => (
                [sibling.product, g.trigger],
                [sibling.right_state, g.trigger_right],
            ),
        };
        let child_score = scorer.times(
            self.best_inside[children[0].index()],
            self.best_inside[children[1].index()],
        );
        let mut realized = false;
        for symbol_group in &group.symbol_groups {
            let Some(parent_right) =
                self.binary_right_parent_det(symbol_group.symbol, right_children)
            else {
                continue;
            };
            for &rule_idx in &symbol_group.rule_indexes {
                let (parent_left, symbol, weight) = {
                    let rule = &self.left_rules[rule_idx];
                    (rule.result, rule.symbol, rule.weight)
                };
                self.stats.candidate_edges += 1;
                self.stats.candidates_realized += 1;
                self.push_candidate_with_child_score(
                    parent_left,
                    parent_right,
                    symbol,
                    weight,
                    &children,
                    child_score,
                    scorer,
                    h,
                );
                realized = true;
            }
        }
        if realized {
            self.stats.sibling_realizations += 1;
        }
    }

    /// On finalization of a product, spawn one generator per `(position, group)`
    /// of its left state over the siblings already present in the finder.
    #[allow(clippy::too_many_arguments)]
    fn lazy_spawn_generators<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        frontier: &mut SpanLazyFrontier,
        product: StateId,
        left_state: StateId,
        right_state: StateId,
        span: Span,
        span_left_index: &SpanAstarLeftIndex,
        scorer: &S,
        h: &H,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        for position in 0..2usize {
            let Some(groups) = span_left_index.binary_groups(left_state, position) else {
                continue;
            };
            for (group_idx, group) in groups.iter().enumerate() {
                // Compute the merit of every sibling once and store them in a
                // max-heap, so the generator's next-best is a heap pop O(log s)
                // rather than a rescan O(s) (see docs/n10-asymptotics.md). The
                // finder slice is append-only, so the captured indices stay valid
                // for later re-derivation in `lazy_push_sibling_rules`.
                let siblings = frontier.finder.siblings_slice(span, position, group.sibling_left);
                let mut pending = std::collections::BinaryHeap::new();
                for (idx, &sibling) in siblings.iter().enumerate() {
                    if let Some(merit) = self.lazy_sibling_merit(
                        product,
                        right_state,
                        position as u8,
                        sibling,
                        group,
                        scorer,
                        h,
                    ) {
                        pending.push(SiblingEntry {
                            merit,
                            sibling_index: idx as u32,
                        });
                    }
                }
                let Some(top) = pending.peek().map(|entry| entry.merit) else {
                    continue;
                };
                let id = frontier.generators.len();
                frontier.generators.push(SpanGenerator {
                    trigger: product,
                    trigger_right: right_state,
                    trigger_left: left_state,
                    position: position as u8,
                    group_idx: group_idx as u32,
                    pending,
                });
                self.stats.generators_created += 1;
                frontier.frontier.update_or_push(id, top);
            }
        }
    }

    /// Realize the best (top-of-heap) sibling of generator `id` and return the
    /// merit of its next-best sibling (for re-keying), or `None` if drained.
    fn lazy_realize_generator<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        frontier: &mut SpanLazyFrontier,
        id: usize,
        span_left_index: &SpanAstarLeftIndex,
        scorer: &S,
        h: &H,
    ) -> Option<f64>
    where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        let entry = frontier.generators[id].pending.pop()?;
        self.lazy_push_sibling_rules(
            &frontier.generators[id],
            &frontier.finder,
            entry.sibling_index as usize,
            span_left_index,
            scorer,
            h,
        );
        frontier.generators[id].pending.peek().map(|e| e.merit)
    }

    /// Lazy-frontier variant of [`Self::run_with_span_product_sibling_finder`].
    ///
    /// Interleaves, by merit, finalizing products off the parent agenda against
    /// lazily generating binary candidates off the frontier. A product is
    /// finalized only when its best realized edge dominates every generator's
    /// best unrealized candidate, so the result is bit-identical to eager.
    fn run_with_lazy_span_frontier<H, S, OnFin>(
        &mut self,
        h: &H,
        scorer: &S,
        span_left_index: &SpanAstarLeftIndex,
        stop_at_first_goal: bool,
        mut on_finalize: OnFin,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
        OnFin: FnMut(&mut Self, StateId, &EmitEdge, f64),
    {
        let mut frontier = SpanLazyFrontier::new();

        loop {
            let merit_a = self.heap.peek_merit();
            let merit_f = frontier.frontier.peek_merit();
            let take_parent = match (merit_a, merit_f) {
                (None, None) => break,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (Some(a), Some(f)) => a >= f,
            };

            if take_parent {
                let Some(item) = self.pop_next_finalized(scorer, false) else {
                    continue;
                };
                let span = *self.right_interner.resolve(item.right_state);
                // Record the finalized product as an available sibling before
                // expanding, matching the eager path's activate-then-expand order.
                span_left_index.activate_product(
                    &mut frontier.finder,
                    item.product,
                    item.left_state,
                    item.right_state,
                    span,
                );

                on_finalize(self, item.product, &item.edge, item.inside);
                if item.is_goal && stop_at_first_goal {
                    break;
                }

                self.lazy_spawn_generators(
                    &mut frontier,
                    item.product,
                    item.left_state,
                    item.right_state,
                    span,
                    span_left_index,
                    scorer,
                    h,
                );
                self.lazy_expand_unary(item.product, item.left_state, span, span_left_index, scorer, h);
            } else {
                let Some(id) = frontier.frontier.pop() else {
                    continue;
                };
                self.stats.frontier_pops += 1;
                if let Some(next_merit) =
                    self.lazy_realize_generator(&mut frontier, id, span_left_index, scorer, h)
                {
                    frontier.frontier.update_or_push(id, next_merit);
                }
            }
        }
    }

    /// Expand the unary rules of a finalized product directly onto the parent
    /// agenda (unary edges have no sibling, so they never enter the frontier).
    /// Mirrors the unary block of
    /// [`Self::expand_from_finalized_with_span_product_siblings`].
    fn lazy_expand_unary<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        product: StateId,
        left_state: StateId,
        raw_trigger: Span,
        span_left_index: &SpanAstarLeftIndex,
        scorer: &S,
        h: &H,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        let Some(unary_rules) = span_left_index.unary_rules(left_state) else {
            return;
        };
        for &rule_idx in unary_rules {
            let (parent_left, symbol, weight) = {
                let rule = &self.left_rules[rule_idx];
                (rule.result, rule.symbol, rule.weight)
            };
            let raw_children = [raw_trigger];
            self.stats.right_step_calls += 1;
            let Some(parent) = self.right.step_det(symbol, &raw_children) else {
                continue;
            };
            self.stats.right_step_results += 1;
            let parent_right = RightStateInterner::intern(&mut self.right_interner, parent);
            self.stats.candidate_edges += 1;
            self.push_candidate_with_child_score(
                parent_left,
                parent_right,
                symbol,
                weight,
                &[product],
                self.best_inside[product.index()],
                scorer,
                h,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point 1: chart materializer
// ---------------------------------------------------------------------------

/// Materialize the intersection of an explicit grammar automaton with a
/// condensed right automaton using A*.
///
/// The returned [`Explicit`] automaton contains the subset of the intersection
/// explored and finalized by A*.  When `options.stop_at_first_goal` is `true`
/// the chart contains exactly the rules needed to derive the single best tree.
/// When `options.beam` is set (and `stop_at_first_goal` is `false`) only items
/// with `merit >= beam` are emitted.
///
/// Returns the chart, the right-state interner, and statistics.
pub fn materialize_astar_intersection<R, H>(
    left: &Explicit,
    right: &R,
    h: &H,
    options: AstarOptions,
) -> (Explicit, Interner<R::State>, AstarStats)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
{
    materialize_astar_intersection_with(left, right, h, options, &ProbabilityScorer)
}

/// Materialize the intersection using A* and `scorer`.
pub fn materialize_astar_intersection_with<R, H, S>(
    left: &Explicit,
    right: &R,
    h: &H,
    options: AstarOptions,
    scorer: &S,
) -> (Explicit, Interner<R::State>, AstarStats)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    materialize_astar_intersection_with_index(left, right, h, options, scorer)
}

pub(crate) fn materialize_astar_string_intersection_with<'h, H, S>(
    left: &Explicit,
    right: &InvHom<'h, StringDecompositionAutomaton>,
    h: &H,
    options: AstarOptions,
    scorer: &S,
) -> (Explicit, Interner<Span>, AstarStats)
where
    H: IntersectionHeuristic<InvHom<'h, StringDecompositionAutomaton>>,
    S: WeightScorer,
{
    let prepared = PreparedAstarGrammar::new(left);
    materialize_astar_string_intersection_with_prepared(left, &prepared, right, h, options, scorer)
}

pub fn materialize_astar_string_intersection_with_prepared<'h, H, S>(
    left: &Explicit,
    prepared: &PreparedAstarGrammar,
    right: &InvHom<'h, StringDecompositionAutomaton>,
    h: &H,
    options: AstarOptions,
    scorer: &S,
) -> (Explicit, Interner<Span>, AstarStats)
where
    H: IntersectionHeuristic<InvHom<'h, StringDecompositionAutomaton>>,
    S: WeightScorer,
{
    materialize_astar_intersection_with_span_sibling(
        left,
        prepared,
        right,
        h,
        options,
        scorer,
        right.inner().len(),
        string_product_heap_bound(left, right.inner().len()),
        lazy_frontier_enabled(),
    )
}

#[allow(clippy::too_many_arguments)]
fn materialize_astar_intersection_with_span_sibling<R, H, S>(
    left: &Explicit,
    prepared: &PreparedAstarGrammar,
    right: &R,
    h: &H,
    options: AstarOptions,
    scorer: &S,
    sentence_len: usize,
    heap_index_bound: usize,
    lazy: bool,
) -> (Explicit, Interner<Span>, AstarStats)
where
    R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    let mut ctx = AstarContext::new(
        left,
        right,
        &prepared.left_rules,
        &prepared.left_index,
        SpanInterner::new(sentence_len),
        true,
        heap_index_bound,
    );
    ctx.seed_nullary_edges(h, scorer);

    let stop_at_first_goal = options.stop_at_first_goal;
    let beam = options.beam;

    let on_finalize = |ctx: &mut AstarContext<'_, R, SpanInterner>,
                       product: StateId,
                       edge: &EmitEdge,
                       inside: f64| {
        let emit = stop_at_first_goal || beam.is_none_or(|threshold| inside >= threshold);
        if emit {
            let builder = ctx
                .builder
                .as_mut()
                .expect("chart mode always has a builder");
            ctx.rule_tracker.add_rule(
                builder,
                edge.symbol,
                edge.children.clone(),
                product,
                edge.weight,
            );
            ctx.stats.emitted_rules += 1;
        }
    };

    let use_lazy =
        lazy && !prepared.span_left_index.has_any_higher_arity();
    if use_lazy {
        ctx.run_with_lazy_span_frontier(
            h,
            scorer,
            &prepared.span_left_index,
            stop_at_first_goal,
            on_finalize,
        );
    } else {
        ctx.run_with_span_product_sibling_finder(
            h,
            scorer,
            &prepared.span_left_index,
            stop_at_first_goal,
            on_finalize,
        );
    }

    ctx.stats.output_states = ctx.product_pairs.len();
    ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;

    let builder = ctx.builder.take().unwrap_or_default();
    let explicit = builder.build_trusted();
    (
        explicit,
        ctx.right_interner.into_generic_interner(),
        ctx.stats,
    )
}

fn materialize_astar_intersection_with_index<R, H, S>(
    left: &Explicit,
    right: &R,
    h: &H,
    options: AstarOptions,
    scorer: &S,
) -> (Explicit, Interner<R::State>, AstarStats)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
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

    let mut ctx = AstarContext::new(
        left,
        right,
        &left_rules,
        &left_index,
        Interner::new(),
        true,
        16 * 1024,
    );
    ctx.seed_nullary_edges(h, scorer);

    let stop_at_first_goal = options.stop_at_first_goal;
    let beam = options.beam;

    ctx.run(
        h,
        scorer,
        stop_at_first_goal,
        |ctx, _product, edge, inside| {
            // Emit a rule if in beam mode or one-best mode.
            let emit = stop_at_first_goal || beam.is_none_or(|threshold| inside >= threshold);
            if emit {
                let builder = ctx
                    .builder
                    .as_mut()
                    .expect("chart mode always has a builder");
                // Find the product state for the parent (it was just finalized, so
                // it must be in product_pairs — but we need the parent_id, which is
                // `_product` itself).
                ctx.rule_tracker.add_rule(
                    builder,
                    edge.symbol,
                    edge.children.clone(),
                    _product,
                    edge.weight,
                );
                ctx.stats.emitted_rules += 1;
            }
        },
    );

    ctx.stats.output_states = ctx.product_pairs.len();
    ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;

    let builder = ctx.builder.take().unwrap_or_default();
    let explicit = builder.build_trusted();
    (explicit, ctx.right_interner, ctx.stats)
}

// ---------------------------------------------------------------------------
// Entry point 2: direct one-best
// ---------------------------------------------------------------------------

/// Run A* in one-best mode and return the highest-weighted accepted tree.
///
/// No chart is built; backpointers are used directly to reconstruct the tree.
/// Returns `None` if the intersection language is empty (heap exhausts without
/// reaching a goal state).
pub fn astar_one_best<R, H>(left: &Explicit, right: &R, h: &H) -> Option<ViterbiTree>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
{
    astar_one_best_with_stats(left, right, h, &ProbabilityScorer).0
}

/// Run A* in one-best mode using `scorer`.
pub fn astar_one_best_with<R, H, S>(
    left: &Explicit,
    right: &R,
    h: &H,
    scorer: &S,
) -> Option<ViterbiTree>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    astar_one_best_with_stats(left, right, h, scorer).0
}

/// Run A* in one-best mode using `scorer`, returning statistics.
pub fn astar_one_best_with_stats<R, H, S>(
    left: &Explicit,
    right: &R,
    h: &H,
    scorer: &S,
) -> (Option<ViterbiTree>, AstarStats)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    astar_one_best_with_stats_and_index(left, right, h, scorer)
}

pub(crate) fn astar_string_one_best_with_stats<'h, H, S>(
    left: &Explicit,
    right: &InvHom<'h, StringDecompositionAutomaton>,
    h: &H,
    scorer: &S,
) -> (Option<ViterbiTree>, AstarStats)
where
    H: IntersectionHeuristic<InvHom<'h, StringDecompositionAutomaton>>,
    S: WeightScorer,
{
    let prepared = PreparedAstarGrammar::new(left);
    astar_string_one_best_with_stats_prepared(left, &prepared, right, h, scorer)
}

pub fn astar_string_one_best_with_stats_prepared<'h, H, S>(
    left: &Explicit,
    prepared: &PreparedAstarGrammar,
    right: &InvHom<'h, StringDecompositionAutomaton>,
    h: &H,
    scorer: &S,
) -> (Option<ViterbiTree>, AstarStats)
where
    H: IntersectionHeuristic<InvHom<'h, StringDecompositionAutomaton>>,
    S: WeightScorer,
{
    astar_one_best_with_stats_and_span_sibling(
        left,
        prepared,
        right,
        h,
        scorer,
        right.inner().len(),
        string_product_heap_bound(left, right.inner().len()),
        lazy_frontier_enabled(),
    )
}

#[allow(clippy::too_many_arguments)]
fn astar_one_best_with_stats_and_span_sibling<R, H, S>(
    left: &Explicit,
    prepared: &PreparedAstarGrammar,
    right: &R,
    h: &H,
    scorer: &S,
    sentence_len: usize,
    heap_index_bound: usize,
    lazy: bool,
) -> (Option<ViterbiTree>, AstarStats)
where
    R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    let mut ctx = AstarContext::new(
        left,
        right,
        &prepared.left_rules,
        &prepared.left_index,
        SpanInterner::new(sentence_len),
        false,
        heap_index_bound,
    );
    ctx.seed_nullary_edges(h, scorer);

    let mut goal_state: Option<(StateId, f64)> = None;

    let on_finalize = |ctx: &mut AstarContext<'_, R, SpanInterner>,
                       product: StateId,
                       _edge: &EmitEdge,
                       inside: f64| {
        if goal_state.is_none() && ctx.is_accepting_product(product) {
            goal_state = Some((product, inside));
        }
    };

    let use_lazy =
        lazy && !prepared.span_left_index.has_any_higher_arity();
    if use_lazy {
        ctx.run_with_lazy_span_frontier(h, scorer, &prepared.span_left_index, true, on_finalize);
    } else {
        ctx.run_with_span_product_sibling_finder(
            h,
            scorer,
            &prepared.span_left_index,
            true,
            on_finalize,
        );
    }

    let Some((goal, best_score)) = goal_state else {
        ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;
        return (None, ctx.stats);
    };
    ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;

    let mut arena = TreeArena::new();
    let Some(root) = build_tree(goal, &ctx.back, &mut arena) else {
        return (None, ctx.stats);
    };
    let tree =
        ViterbiTree::new_with_score(arena, root, best_score, scorer.score_to_weight(best_score));
    (Some(tree), ctx.stats)
}

fn astar_one_best_with_stats_and_index<R, H, S>(
    left: &Explicit,
    right: &R,
    h: &H,
    scorer: &S,
) -> (Option<ViterbiTree>, AstarStats)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
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

    let mut ctx = AstarContext::new(
        left,
        right,
        &left_rules,
        &left_index,
        Interner::new(),
        false,
        16 * 1024,
    );
    ctx.seed_nullary_edges(h, scorer);

    let mut goal_state: Option<(StateId, f64)> = None;

    ctx.run(h, scorer, true, |ctx, product, _edge, inside| {
        if goal_state.is_none() && ctx.is_accepting_product(product) {
            goal_state = Some((product, inside));
        }
    });

    let Some((goal, best_score)) = goal_state else {
        ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;
        return (None, ctx.stats);
    };
    ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;

    let mut arena = TreeArena::new();
    let Some(root) = build_tree(goal, &ctx.back, &mut arena) else {
        return (None, ctx.stats);
    };
    let tree =
        ViterbiTree::new_with_score(arena, root, best_score, scorer.score_to_weight(best_score));
    (Some(tree), ctx.stats)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ExplicitBuilder, Homomorphism, Symbol,
        heuristic::{OutsideHeuristic, ZeroHeuristic},
        materialize::{
            materialize_indexed_condensed_intersection, materialize_topdown_condensed_intersection,
        },
    };

    /// Build a small grammar/automaton suitable for self-intersection tests.
    ///
    /// Grammar:
    ///   a() -> s0  w=0.6
    ///   b() -> s1  w=0.4
    ///   f(s0, s1) -> s2  w=0.8   (accepting)
    ///   f(s1, s0) -> s2  w=0.5   (lower-weight alternative)
    fn build_small_grammar() -> Explicit {
        let a = Symbol(0);
        let b = Symbol(1);
        let f = Symbol(2);

        let mut builder = ExplicitBuilder::new();
        let s0 = builder.new_state();
        let s1 = builder.new_state();
        let s2 = builder.new_state();

        builder.add_weighted_rule(a, vec![], s0, 0.6);
        builder.add_weighted_rule(b, vec![], s1, 0.4);
        builder.add_weighted_rule(f, vec![s0, s1], s2, 0.8);
        builder.add_weighted_rule(f, vec![s1, s0], s2, 0.5);
        builder.add_accepting(s2);

        builder.build()
    }

    /// Build a grammar with a unary self-loop on the accepting state.
    fn build_grammar_with_self_loop() -> Explicit {
        let a = Symbol(0);
        let f = Symbol(1);

        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let root = builder.new_state();

        builder.add_weighted_rule(a, vec![], leaf, 0.9);
        builder.add_weighted_rule(f, vec![leaf], root, 0.7);
        // Self-loop with a very high weight to ensure termination is still correct.
        builder.add_weighted_rule(f, vec![root], root, 100.0);
        builder.add_accepting(root);

        builder.build()
    }

    fn add_word_hom(hom: &mut Homomorphism, source: Symbol, word: Symbol) {
        let term = hom.add_symbol(word, Vec::new());
        hom.add(source, 0, term).unwrap();
    }

    fn add_identity_hom(hom: &mut Homomorphism, source: Symbol) {
        let child = hom.add_var(0);
        hom.add(source, 1, child).unwrap();
    }

    fn add_binary_concat_hom(hom: &mut Homomorphism, source: Symbol, concat: Symbol) {
        let left = hom.add_var(0);
        let right = hom.add_var(1);
        let term = hom.add_symbol(concat, vec![left, right]);
        hom.add(source, 2, term).unwrap();
    }

    fn add_ternary_concat_hom(hom: &mut Homomorphism, source: Symbol, concat: Symbol) {
        let left = hom.add_var(0);
        let middle = hom.add_var(1);
        let first = hom.add_symbol(concat, vec![left, middle]);
        let right = hom.add_var(2);
        let term = hom.add_symbol(concat, vec![first, right]);
        hom.add(source, 3, term).unwrap();
    }

    #[test]
    fn string_sibling_astar_matches_old_index_and_topdown_for_binary_unary_rules() {
        let concat = Symbol(0);
        let word_a = Symbol(1);
        let word_b = Symbol(2);
        let g_a = Symbol(10);
        let g_b = Symbol(11);
        let g_ab = Symbol(12);
        let g_id = Symbol(13);

        let mut hom = Homomorphism::new();
        add_word_hom(&mut hom, g_a, word_a);
        add_word_hom(&mut hom, g_b, word_b);
        add_binary_concat_hom(&mut hom, g_ab, concat);
        add_identity_hom(&mut hom, g_id);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let q_ab = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(g_a, vec![], qa, 0.8);
        builder.add_weighted_rule(g_b, vec![], qb, 0.7);
        builder.add_weighted_rule(g_ab, vec![qa, qb], q_ab, 0.9);
        builder.add_weighted_rule(g_id, vec![q_ab], root, 0.95);
        builder.add_accepting(root);
        let grammar = builder.build();

        let right = InvHom::new(
            StringDecompositionAutomaton::new(concat, vec![word_a, word_b]),
            &hom,
        );
        let h = ZeroHeuristic;

        let (new_best, new_stats) =
            astar_string_one_best_with_stats(&grammar, &right, &h, &ProbabilityScorer);
        let (old_best, _) =
            astar_one_best_with_stats_and_index(&grammar, &right, &h, &ProbabilityScorer);
        let (topdown_chart, _, _) = materialize_topdown_condensed_intersection(&grammar, &right);

        let new_best = new_best.expect("sibling-finder A* should find a tree");
        let old_best = old_best.expect("old indexed A* should find a tree");
        let topdown_best = topdown_chart
            .viterbi()
            .expect("topdown should find the same tree");

        assert!((new_best.weight() - old_best.weight()).abs() < 1e-10);
        assert!((new_best.weight() - topdown_best.weight()).abs() < 1e-10);
        assert!(new_stats.sibling_tuple_queries > 0);
        assert!(new_stats.sibling_tuples_returned > 0);
        assert!(new_stats.right_step_calls > 0);
        assert!(new_stats.right_step_results > 0);
        assert_eq!(new_stats.sibling_fallback_expansions, 0);
    }

    #[test]
    fn span_interner_round_trips_dense_span_ids() {
        let mut interner = span::SpanInterner::new(4);
        let expected = [
            Span::new(0, 1),
            Span::new(0, 2),
            Span::new(0, 3),
            Span::new(0, 4),
            Span::new(1, 2),
            Span::new(1, 3),
            Span::new(1, 4),
            Span::new(2, 3),
            Span::new(2, 4),
            Span::new(3, 4),
        ];
        for (index, span) in expected.into_iter().enumerate() {
            let id = interner.intern(span);
            assert_eq!(id.index(), index);
            assert_eq!(*interner.resolve(id), span);
        }
    }

    #[test]
    fn string_sibling_astar_falls_back_for_higher_arity_rules() {
        let concat = Symbol(0);
        let word_a = Symbol(1);
        let word_b = Symbol(2);
        let word_c = Symbol(3);
        let g_a = Symbol(10);
        let g_b = Symbol(11);
        let g_c = Symbol(12);
        let g_abc = Symbol(13);

        let mut hom = Homomorphism::new();
        add_word_hom(&mut hom, g_a, word_a);
        add_word_hom(&mut hom, g_b, word_b);
        add_word_hom(&mut hom, g_c, word_c);
        add_ternary_concat_hom(&mut hom, g_abc, concat);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let qc = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(g_a, vec![], qa, 0.8);
        builder.add_weighted_rule(g_b, vec![], qb, 0.7);
        builder.add_weighted_rule(g_c, vec![], qc, 0.6);
        builder.add_weighted_rule(g_abc, vec![qa, qb, qc], root, 0.9);
        builder.add_accepting(root);
        let grammar = builder.build();

        let right = InvHom::new(
            StringDecompositionAutomaton::new(concat, vec![word_a, word_b, word_c]),
            &hom,
        );
        let h = ZeroHeuristic;

        let (new_best, new_stats) =
            astar_string_one_best_with_stats(&grammar, &right, &h, &ProbabilityScorer);
        let (old_best, _) =
            astar_one_best_with_stats_and_index(&grammar, &right, &h, &ProbabilityScorer);

        let new_best = new_best.expect("sibling-finder A* fallback should find a tree");
        let old_best = old_best.expect("old indexed A* should find a tree");

        assert!((new_best.weight() - old_best.weight()).abs() < 1e-10);
        assert!(new_stats.sibling_fallback_expansions > 0);
    }

    /// Ambiguous purely-binary grammar over three tokens with two root
    /// derivations (`((ab)c)` vs `(a(bc))`) and several binary groups, so the
    /// lazy frontier actually interleaves generation against finalization.
    fn build_ambiguous_binary_string_grammar() -> (Explicit, Homomorphism, Vec<Symbol>) {
        let concat = Symbol(0);
        let word_a = Symbol(1);
        let word_b = Symbol(2);
        let word_c = Symbol(3);
        let g_a = Symbol(10);
        let g_b = Symbol(11);
        let g_c = Symbol(12);
        let g_cat = Symbol(13);

        let mut hom = Homomorphism::new();
        add_word_hom(&mut hom, g_a, word_a);
        add_word_hom(&mut hom, g_b, word_b);
        add_word_hom(&mut hom, g_c, word_c);
        add_binary_concat_hom(&mut hom, g_cat, concat);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let qc = builder.new_state();
        let q_ab = builder.new_state();
        let q_bc = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(g_a, vec![], qa, 0.9);
        builder.add_weighted_rule(g_b, vec![], qb, 0.8);
        builder.add_weighted_rule(g_c, vec![], qc, 0.7);
        builder.add_weighted_rule(g_cat, vec![qa, qb], q_ab, 0.6);
        builder.add_weighted_rule(g_cat, vec![qb, qc], q_bc, 0.5);
        builder.add_weighted_rule(g_cat, vec![q_ab, qc], root, 0.95);
        builder.add_weighted_rule(g_cat, vec![qa, q_bc], root, 0.85);
        builder.add_accepting(root);

        (builder.build(), hom, vec![word_a, word_b, word_c])
    }

    #[test]
    fn lazy_span_frontier_one_best_matches_eager() {
        let (grammar, hom, sentence) = build_ambiguous_binary_string_grammar();
        let concat = Symbol(0);
        let right = InvHom::new(StringDecompositionAutomaton::new(concat, sentence), &hom);
        let h = ZeroHeuristic;
        let prepared = PreparedAstarGrammar::new(&grammar);
        let n = right.inner().len();
        let bound = string_product_heap_bound(&grammar, n);

        let (eager, eager_stats) = astar_one_best_with_stats_and_span_sibling(
            &grammar,
            &prepared,
            &right,
            &h,
            &ProbabilityScorer,
            n,
            bound,
            false,
        );
        let (lazy, lazy_stats) = astar_one_best_with_stats_and_span_sibling(
            &grammar,
            &prepared,
            &right,
            &h,
            &ProbabilityScorer,
            n,
            bound,
            true,
        );

        let eager = eager.expect("eager span A* should find a tree");
        let lazy = lazy.expect("lazy span A* should find a tree");
        // Bit-identical, not just close: lazy reuses push_candidate verbatim.
        assert_eq!(eager.weight(), lazy.weight());
        assert_eq!(eager_stats.finalized_states, lazy_stats.finalized_states);
        // The lazy path actually exercised the frontier.
        assert!(lazy_stats.generators_created > 0);
        assert!(lazy_stats.frontier_pops > 0);
        assert!(lazy_stats.candidates_realized > 0);
    }

    #[test]
    fn lazy_span_frontier_full_chart_matches_eager() {
        let (grammar, hom, sentence) = build_ambiguous_binary_string_grammar();
        let concat = Symbol(0);
        let right = InvHom::new(StringDecompositionAutomaton::new(concat, sentence), &hom);
        let h = ZeroHeuristic;
        let prepared = PreparedAstarGrammar::new(&grammar);
        let n = right.inner().len();
        let bound = string_product_heap_bound(&grammar, n);
        let options = || AstarOptions {
            stop_at_first_goal: false,
            beam: None,
        };

        let (eager_chart, _, eager_stats) = materialize_astar_intersection_with_span_sibling(
            &grammar,
            &prepared,
            &right,
            &h,
            options(),
            &ProbabilityScorer,
            n,
            bound,
            false,
        );
        let (lazy_chart, _, lazy_stats) = materialize_astar_intersection_with_span_sibling(
            &grammar,
            &prepared,
            &right,
            &h,
            options(),
            &ProbabilityScorer,
            n,
            bound,
            true,
        );

        // Full chart: same finalized states, same emitted rules, same best tree.
        assert_eq!(eager_stats.finalized_states, lazy_stats.finalized_states);
        assert_eq!(eager_stats.output_states, lazy_stats.output_states);
        assert_eq!(eager_stats.emitted_rules, lazy_stats.emitted_rules);
        let eager_best = eager_chart.viterbi().expect("eager chart has a tree");
        let lazy_best = lazy_chart.viterbi().expect("lazy chart has a tree");
        assert_eq!(eager_best.weight(), lazy_best.weight());
    }

    // -----------------------------------------------------------------------
    // Test 1: Equivalence oracle — A* chart + viterbi() == indexed materializer + viterbi()
    // -----------------------------------------------------------------------

    #[test]
    fn astar_chart_viterbi_matches_indexed_materializer() {
        let grammar = build_small_grammar();

        // Reference: indexed materializer.
        let (indexed_chart, _, _) = materialize_indexed_condensed_intersection(&grammar, &grammar);
        let indexed_best = indexed_chart.viterbi().expect("indexed should find a tree");

        // A* with ZeroHeuristic (= exact Knuth order), one-best mode.
        let h = ZeroHeuristic;
        let options = AstarOptions {
            stop_at_first_goal: true,
            beam: None,
        };
        let (astar_chart, _, _) = materialize_astar_intersection(&grammar, &grammar, &h, options);
        let astar_best = astar_chart.viterbi().expect("A* should find a tree");

        let diff = (indexed_best.weight() - astar_best.weight()).abs();
        assert!(
            diff < 1e-10,
            "weight mismatch: indexed={} astar={}",
            indexed_best.weight(),
            astar_best.weight()
        );
    }

    // -----------------------------------------------------------------------
    // Test 2: astar_one_best with OutsideHeuristic gives same weight as ZeroHeuristic
    // -----------------------------------------------------------------------

    #[test]
    fn outside_heuristic_one_best_matches_zero_heuristic() {
        let grammar = build_small_grammar();

        let h_zero = ZeroHeuristic;
        let h_outside = OutsideHeuristic::from_grammar(&grammar);

        let zero_result =
            astar_one_best(&grammar, &grammar, &h_zero).expect("zero heuristic should find tree");

        let outside_result = astar_one_best(&grammar, &grammar, &h_outside)
            .expect("outside heuristic should find tree");

        let diff = (zero_result.weight() - outside_result.weight()).abs();
        assert!(
            diff < 1e-10,
            "weight mismatch: zero={} outside={}",
            zero_result.weight(),
            outside_result.weight()
        );
    }

    // -----------------------------------------------------------------------
    // Test 3: OutsideHeuristic uses <= finalized states compared to ZeroHeuristic
    // -----------------------------------------------------------------------

    #[test]
    fn outside_heuristic_expands_no_more_than_zero() {
        let grammar = build_small_grammar();

        let h_zero = ZeroHeuristic;
        let h_outside = OutsideHeuristic::from_grammar(&grammar);

        // Run both in one-best mode via the chart API to obtain stats.
        let (_, _, stats_zero) = materialize_astar_intersection(
            &grammar,
            &grammar,
            &h_zero,
            AstarOptions {
                stop_at_first_goal: true,
                beam: None,
            },
        );
        let (_, _, stats_outside) = materialize_astar_intersection(
            &grammar,
            &grammar,
            &h_outside,
            AstarOptions {
                stop_at_first_goal: true,
                beam: None,
            },
        );

        assert!(
            stats_outside.finalized_states <= stats_zero.finalized_states,
            "outside heuristic finalized {} states but zero heuristic only {}",
            stats_outside.finalized_states,
            stats_zero.finalized_states
        );
    }

    // -----------------------------------------------------------------------
    // Test 4: reopen_attempts == 0 for both heuristics (consistent h)
    // -----------------------------------------------------------------------

    #[test]
    fn no_reopen_attempts_for_consistent_heuristics() {
        let grammar = build_small_grammar();

        let h_zero = ZeroHeuristic;
        let h_outside = OutsideHeuristic::from_grammar(&grammar);

        let (_, _, stats_zero) = materialize_astar_intersection(
            &grammar,
            &grammar,
            &h_zero,
            AstarOptions {
                stop_at_first_goal: false,
                beam: None,
            },
        );
        let (_, _, stats_outside) = materialize_astar_intersection(
            &grammar,
            &grammar,
            &h_outside,
            AstarOptions {
                stop_at_first_goal: false,
                beam: None,
            },
        );

        assert_eq!(
            stats_zero.reopen_attempts, 0,
            "ZeroHeuristic had {} reopen attempts",
            stats_zero.reopen_attempts
        );
        assert_eq!(
            stats_outside.reopen_attempts, 0,
            "OutsideHeuristic had {} reopen attempts",
            stats_outside.reopen_attempts
        );
    }

    // -----------------------------------------------------------------------
    // Test 5: Self-loop grammar terminates with correct answer
    // -----------------------------------------------------------------------

    #[test]
    fn self_loop_grammar_terminates_correctly() {
        let grammar = build_grammar_with_self_loop();

        let h = ZeroHeuristic;
        let result = astar_one_best(&grammar, &grammar, &h);
        assert!(result.is_some(), "should find a tree even with self-loop");
        // The best tree should use f(a()) -> root without the self-loop.
        // Weight: a()=0.9, f(leaf)=0.7 → product inside = 0.9*0.7 = 0.63
        // (intersection product: both sides contribute 0.9 and 0.7 each)
        // Actual weight: 0.9 * 0.9 (leaf×leaf) * 0.7 * 0.7 (rule×rule) = 0.81 * 0.49 = 0.3969
        let weight = result.unwrap().weight();
        assert!(
            weight > 0.0,
            "best tree should have positive weight, got {}",
            weight
        );
    }

    #[test]
    fn partner_set_expansion_handles_orders_repeats_and_missing_siblings() {
        let a = Symbol(0);
        let b = Symbol(1);
        let f = Symbol(2);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let root_ab = builder.new_state();
        let root_ba = builder.new_state();
        let root_aa = builder.new_state();

        builder.add_weighted_rule(a, vec![], qa, 0.9);
        builder.add_weighted_rule(b, vec![], qb, 0.8);
        builder.add_weighted_rule(f, vec![qa, qb], root_ab, 0.95);
        builder.add_weighted_rule(f, vec![qb, qa], root_ba, 0.94);
        builder.add_weighted_rule(f, vec![qa, qa], root_aa, 0.1);
        builder.add_accepting(root_ab);
        builder.add_accepting(root_ba);
        builder.add_accepting(root_aa);
        let grammar = builder.build();

        let h = ZeroHeuristic;
        let (best, stats) = astar_one_best_with_stats(&grammar, &grammar, &h, &ProbabilityScorer);
        let best = best.expect("A* should find a tree");

        let expected = 0.9 * 0.8 * 0.95;
        assert!(
            (best.weight() - expected).abs() < 1e-10,
            "expected {expected}, got {}",
            best.weight()
        );
        assert!(stats.finalized_states >= 3);
        assert_eq!(stats.reopen_attempts, 0);
    }

    // -----------------------------------------------------------------------
    // Test 6: materialize_astar_intersection one-best chart + viterbi() == astar_one_best
    // -----------------------------------------------------------------------

    #[test]
    fn astar_chart_one_best_matches_astar_direct() {
        let grammar = build_small_grammar();

        let h = ZeroHeuristic;

        let (chart, _, _) = materialize_astar_intersection(
            &grammar,
            &grammar,
            &h,
            AstarOptions {
                stop_at_first_goal: true,
                beam: None,
            },
        );
        let chart_best = chart.viterbi().expect("chart should have a tree");

        let direct_best =
            astar_one_best(&grammar, &grammar, &h).expect("direct should find a tree");

        let diff = (chart_best.weight() - direct_best.weight()).abs();
        assert!(
            diff < 1e-10,
            "weight mismatch: chart={} direct={}",
            chart_best.weight(),
            direct_best.weight()
        );
    }
}
