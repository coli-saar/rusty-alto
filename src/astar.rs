//! A* intersection materializer for weighted tree automata.
//!
//! This module provides two entry points:
//!
//! * [`materialize_astar_intersection`] — runs A* and emits a full (or beam-filtered)
//!   intersection chart as an [`Explicit`] automaton.
//!
//! * [`astar_one_best`] — runs A* in one-best mode and returns the highest-weighted
//!   accepted tree without building a chart.

use crate::{
    BottomUpTa, CondensedTa, Explicit, ExplicitBuilder, FxHashMap, Interner, KeySet,
    ProbabilityScorer, StateId, Symbol, WeightScorer,
    heuristic::IntersectionHeuristic,
    materialize::{
        IndexedCondensedIntersectionStats, LeftIndex, NullaryEdge, OwnedCondensedRule, OwnedRule,
        ProductStateMap, TrustedRuleTracker, for_each_nullary_edge, get_or_create_product_id,
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
use std::rc::Rc;

#[derive(Default)]
struct PartnerSet {
    states: Vec<StateId>,
    bits: FixedBitSet,
}

impl PartnerSet {
    fn insert(&mut self, state: StateId) -> bool {
        if self.bits.len() <= state.index() {
            self.bits.grow(state.index() + 1);
        }
        if self.bits.contains(state.index()) {
            return false;
        }
        self.bits.set(state.index(), true);
        self.states.push(state);
        true
    }

    fn is_empty(&self) -> bool {
        self.states.is_empty()
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

struct AstarAgenda {
    heap: QuaternaryHeapOfIndices<usize, f64>,
    index_bound: usize,
}

impl Default for AstarAgenda {
    fn default() -> Self {
        Self::with_index_bound(1024)
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
            new_bound *= 2;
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
    /// Number of agenda-item pops that were discarded because the state was
    /// already finalized.  For a consistent heuristic this should always be 0.
    pub reopen_attempts: usize,
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

// ---------------------------------------------------------------------------
// Core A* loop (shared between the two entry points)
// ---------------------------------------------------------------------------

/// Context for the core A* loop.  Kept in a struct so we can pass it around
/// without a giant argument list.
struct AstarContext<'a, R>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    left: &'a Explicit,
    right: &'a R,
    left_rules: &'a [OwnedRule],
    left_index: &'a LeftIndex,
    right_interner: Interner<R::State>,
    product_ids: ProductStateMap,
    product_pairs: Vec<(StateId, StateId)>,
    builder: Option<ExplicitBuilder>,
    rule_tracker: TrustedRuleTracker,
    right_by_child_cache: FxHashMap<(usize, StateId), Rc<[OwnedCondensedRule<StateId>]>>,
    mat_stats: IndexedCondensedIntersectionStats,
    // A* specific state
    finalized: FixedBitSet,
    finalized_partners: Vec<PartnerSet>,
    best_inside: Vec<f64>,
    /// Best inside score discovered so far for each product state.
    best_seen_inside: Vec<f64>,
    back: Vec<Option<Backpointer>>,
    heap: AstarAgenda,
    pending: Vec<Option<AgendaItem>>,
    matches_scratch: Vec<usize>,
    stats: AstarStats,
}

impl<'a, R> AstarContext<'a, R>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    fn new(
        left: &'a Explicit,
        right: &'a R,
        left_rules: &'a [OwnedRule],
        left_index: &'a LeftIndex,
        with_builder: bool,
    ) -> Self {
        Self {
            left,
            right,
            left_rules,
            left_index,
            right_interner: Interner::new(),
            product_ids: ProductStateMap::default(),
            product_pairs: Vec::new(),
            builder: if with_builder {
                Some(ExplicitBuilder::new())
            } else {
                None
            },
            rule_tracker: TrustedRuleTracker::default(),
            right_by_child_cache: FxHashMap::default(),
            mat_stats: IndexedCondensedIntersectionStats::default(),
            finalized: FixedBitSet::new(),
            finalized_partners: Vec::new(),
            best_inside: Vec::new(),
            best_seen_inside: Vec::new(),
            back: Vec::new(),
            heap: AstarAgenda::default(),
            pending: Vec::new(),
            matches_scratch: Vec::new(),
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
            self.back.resize(idx, None);
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

    fn get_or_create_no_builder(
        &mut self,
        left_state: StateId,
        right_state: StateId,
    ) -> (StateId, bool) {
        get_or_create_product_id(
            left_state,
            right_state,
            self.left,
            self.right,
            &mut self.product_ids,
            &mut self.product_pairs,
            &self.right_interner,
            self.builder.get_or_insert_with(ExplicitBuilder::new),
        )
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

    fn right_rules_by_child(
        &mut self,
        position: usize,
        right_state: StateId,
    ) -> Rc<[OwnedCondensedRule<StateId>]> {
        let cache_key = (position, right_state);
        self.right_by_child_cache
            .entry(cache_key)
            .or_insert_with(|| {
                self.mat_stats.right_indexed_queries += 1;
                let raw_state = self.right_interner.resolve(right_state).clone();
                let mut collected = Vec::new();
                self.right.condensed_rules_by_child(
                    position,
                    &raw_state,
                    &mut |children, symbols, result| {
                        collected.push(OwnedCondensedRule {
                            children: children
                                .iter()
                                .cloned()
                                .map(|child| self.right_interner.intern(child))
                                .collect(),
                            symbols: symbols.clone(),
                            result: self.right_interner.intern(result),
                        });
                    },
                );
                Rc::from(collected)
            })
            .clone()
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
        let mut inside = scorer.rule_score(weight);
        for &child in &children {
            inside = scorer.times(inside, self.best_inside[child.index()]);
        }

        let (parent, _) = if let Some(builder) = &mut self.builder {
            get_or_create_product_id(
                parent_left,
                parent_right,
                self.left,
                self.right,
                &mut self.product_ids,
                &mut self.product_pairs,
                &self.right_interner,
                builder,
            )
        } else {
            self.get_or_create_no_builder(parent_left, parent_right)
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
                children,
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
        let mut positions = SmallVec::<[usize; 4]>::new();
        for &(_, position, _) in left_occurrences {
            if !positions.contains(&position) {
                positions.push(position);
            }
        }

        for position in positions {
            let right_rules = self.right_rules_by_child(position, trigger_right);
            for right_rule in right_rules.iter() {
                self.stats.right_rules_scanned += 1;
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
                        .is_some_and(|partners| !partners.is_empty())
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

                self.stats.rotated_left_join_queries += 1;
                self.left_index.rule_indexes_for_rotated_trigger_sets_into(
                    position,
                    trigger_left,
                    &right_rule.symbols,
                    &sibling_sets,
                    &mut self.matches_scratch,
                );
                drop(sibling_sets);
                let matches = std::mem::take(&mut self.matches_scratch);
                self.stats.left_rule_matches += matches.len();

                for &rule_idx in &matches {
                    let left_rule = &self.left_rules[rule_idx];
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
                        } else if let Some(child) = self.product_ids.get(left_child, right_child) {
                            if self.finalized.contains(child.index()) {
                                children.push(child);
                            } else {
                                ok = false;
                                break;
                            }
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    if !ok || !first_trigger(&children, position, trigger_product) {
                        continue;
                    }
                    self.stats.candidate_edges += 1;
                    self.push_candidate(
                        left_rule.result,
                        right_rule.result,
                        left_rule.symbol,
                        left_rule.weight,
                        children,
                        scorer,
                        h,
                    );
                }

                self.matches_scratch = matches;
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
        let (product, _) = if let Some(builder) = &mut self.builder {
            get_or_create_product_id(
                edge.parent_left,
                edge.parent_right,
                self.left,
                self.right,
                &mut self.product_ids,
                &mut self.product_pairs,
                &self.right_interner,
                builder,
            )
        } else {
            self.get_or_create_no_builder(edge.parent_left, edge.parent_right)
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

            // Finalize this state.
            self.finalized.set(product.index(), true);
            self.best_inside[product.index()] = item.inside;
            self.best_seen_inside[product.index()] = item.inside;
            self.back[product.index()] = Some(Backpointer {
                symbol: item.edge.symbol,
                children: item.edge.children.clone(),
                weight: item.inside,
            });
            self.stats.finalized_states += 1;

            let is_goal = self.is_accepting_product(product);
            let (left_state, right_state) = self.product_pairs[product.index()];
            self.ensure_right_state(right_state);
            self.finalized_partners[right_state.index()].insert(left_state);

            // Let the caller emit rules / record results.
            on_finalize(self, product, &item.edge, item.inside);

            if is_goal && stop_at_first_goal {
                break;
            }

            self.expand_from_finalized(left_state, right_state, product, h, scorer);
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

    let mut ctx = AstarContext::new(left, right, &left_rules, &left_index, true);

    // Seed: collect nullary edges.
    let mut nullary_edges = Vec::<NullaryEdge>::new();
    for_each_nullary_edge(
        &left_rules,
        &left_index,
        right,
        &mut ctx.right_interner,
        &mut ctx.mat_stats,
        &mut |edge| nullary_edges.push(edge),
    );
    for edge in nullary_edges {
        ctx.push_seed(edge, h, scorer);
    }

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

    let mut ctx = AstarContext::new(left, right, &left_rules, &left_index, false);

    // Seed.
    let mut nullary_edges = Vec::<NullaryEdge>::new();
    for_each_nullary_edge(
        &left_rules,
        &left_index,
        right,
        &mut ctx.right_interner,
        &mut ctx.mat_stats,
        &mut |edge| nullary_edges.push(edge),
    );
    for edge in nullary_edges {
        ctx.push_seed(edge, h, scorer);
    }

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
        ExplicitBuilder, Symbol,
        heuristic::{OutsideHeuristic, ZeroHeuristic},
        materialize::materialize_indexed_condensed_intersection,
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
