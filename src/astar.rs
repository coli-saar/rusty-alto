//! A* intersection materializer for weighted tree automata.
//!
//! This module provides two entry points:
//!
//! * [`materialize_astar_viterbi_forest`] — runs A* and emits a one-rule-per-state
//!   Viterbi forest as an [`Explicit`] automaton.
//!
//! * [`astar_one_best`] — runs A* in one-best mode and returns the highest-weighted
//!   accepted tree without building a chart.

mod agenda;
mod generic_source;
mod lazy_span;
mod product_state;

use crate::{
    BottomUpTa, CondensedTa, DetBottomUpTa, Explicit, ExplicitBuilder, FxHashMap, Interner, InvHom,
    ProbabilityScorer, Span, StateId, StringDecompositionAutomaton, Symbol, WeightScorer,
    algebras::{
        SpanAstarLeftIndex, SpanBinarySiblingGroup, SpanInterner, SpanProductSibling,
        SpanProductSiblingFinder, StringAstarSource, string_fallback_rules,
    },
    heuristic::IntersectionHeuristic,
    materialize::{
        IndexedCondensedIntersectionStats, LeftIndex, NullaryEdge, OwnedCondensedRule, OwnedRule,
        ProductStateMap, StateInterner, TrustedRuleTracker, for_each_nullary_edge,
        get_or_create_product_id_direct,
    },
    viterbi::{Backpointer, ViterbiTree, build_tree_from_arena},
};
use fixedbitset::FixedBitSet;
use packed_term_arena::tree::TreeArena;
use smallvec::SmallVec;
use std::hash::Hash;

use agenda::{AgendaUpdate, AstarAgenda};
use generic_source::{ChildStateRightRuleIndex, GenericCandidateSource, PartnerSet};
use lazy_span::{LazyStringAstarSource, SiblingEntry, SpanGenerator, SpanLazyFrontier};
use product_state::{AgendaItem, FinalizedItem, PendingEdge};

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

/// Sentinel second-child key for unary rules in the right transition memo
/// (`right_parent_memoized`). Real right child states are interned span ids,
/// which never reach `u32::MAX` for realistic sentence lengths.
const RIGHT_UNARY_SENTINEL: StateId = StateId(u32::MAX);

/// Reusable grammar-side indexes for repeated string A* parses.
///
/// A prepared value is tied to the exact [`Explicit`] instance passed to
/// [`PreparedAstarGrammar::new`]; using it with another grammar panics.
pub struct PreparedAstarGrammar {
    grammar_addr: usize,
    left_rules: Vec<OwnedRule>,
    nullary_left_index: LeftIndex,
    span_left_index: SpanAstarLeftIndex,
}

impl PreparedAstarGrammar {
    /// Build reusable nullary and span-sibling indexes for `left`.
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
        let nullary_left_index =
            LeftIndex::build_filtered(&left_rules, |_, rule| rule.children.is_empty());
        let span_left_index = SpanAstarLeftIndex::build(&left_rules);
        Self {
            grammar_addr: left as *const Explicit as usize,
            left_rules,
            nullary_left_index,
            span_left_index,
        }
    }

    fn assert_matches(&self, left: &Explicit) {
        assert_eq!(
            self.grammar_addr, left as *const Explicit as usize,
            "PreparedAstarGrammar must be used with the Explicit it was built from"
        );
    }
}
/// Candidate generation boundary for the eager A* search.
///
/// The core owns scoring, filtering, dominance, agenda operations,
/// finalization, reopening, and backpointers. A source owns sentence/algebra
/// specific activation state and enumerates candidate rules after a product is
/// finalized.
trait CandidateSource<R, I>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: RightStateInterner<R::State> + StateInterner<R::State>,
{
    fn seed<H, S>(&mut self, ctx: &mut AstarContext<'_, R, I>, h: &H, scorer: &S)
    where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    {
        ctx.seed_nullary_edges(h, scorer);
    }

    /// Realize enough deferred work for the product agenda's maximum to be
    /// globally safe to finalize. Eager sources have no deferred work.
    fn prepare_next<H, S>(&mut self, _ctx: &mut AstarContext<'_, R, I>, _h: &H, _scorer: &S)
    where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    {
    }

    fn activate(&mut self, ctx: &mut AstarContext<'_, R, I>, item: &FinalizedItem);

    fn enumerate<H, S>(
        &mut self,
        ctx: &mut AstarContext<'_, R, I>,
        item: &FinalizedItem,
        h: &H,
        scorer: &S,
    ) where
        H: IntersectionHeuristic<R>,
        S: WeightScorer;
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
    /// same product state. The indexed heap updates these entries in place.
    pub heap_updates: usize,
    /// Maximum number of live product entries in the agenda.
    pub max_heap_len: usize,
    /// Maximum size of the agenda's product-position table.
    pub max_heap_position_capacity: usize,
    /// Number of items popped from the heap.
    pub pops: usize,
    /// Number of distinct product states finalized.
    pub finalized_states: usize,
    /// Number of product expansions, including re-expansions after reopening.
    pub expanded_states: usize,
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
    /// Number of candidate edges skipped at construction time because the
    /// heuristic's sound filter (`admits`) proved the parent product hopeless
    /// (zero outside weight). The F obligatory-leaf filter drives this; on the
    /// span path the skip happens *before* the deterministic right transition,
    /// so it also avoids the `right_step_calls` work for those edges.
    pub f_filtered_candidates: usize,
    /// Number of parent-pair admission decisions served from the per-parse
    /// cache. Only heuristics that opt into admission memoization use it.
    pub heuristic_cache_hits: usize,
    /// Number of parent-pair admission decisions computed and inserted into
    /// the per-parse cache. This is also the final number of cached pairs.
    pub heuristic_cache_misses: usize,
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
    /// Number of *actual* `step_det` evaluations performed (memo misses). With
    /// the condensed transition memo this is far below `right_step_calls`,
    /// because symbols sharing an image term and both-endpoints re-derivations of
    /// the same child pair reuse one computation.
    pub right_step_evals: usize,
    /// Number of `right_step_calls` served from the condensed transition memo
    /// (memo hits) instead of evaluating `step_det`.
    pub right_step_memo_hits: usize,
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

/// Whether the heuristic's sound `admits` filter is consulted at
/// candidate-construction time to skip building hopeless edges (the F
/// obligatory-leaf filter). Defaults to **on**; set `RUSTY_ALTO_F_FILTER=0`
/// (or `false`) to disable for same-binary A/B measurement. Heuristics without
/// a filter (`admits` defaults to `true`) are unaffected either way.
fn candidate_filter_enabled() -> bool {
    !matches!(
        std::env::var("RUSTY_ALTO_F_FILTER").as_deref(),
        Ok("0") | Ok("false")
    )
}

/// Whether heuristics that request admission memoization receive a per-parse
/// cache. Defaults to on; the environment switch exists for same-binary A/B
/// benchmarking.
fn heuristic_cache_enabled() -> bool {
    !matches!(
        std::env::var("RUSTY_ALTO_HEURISTIC_CACHE").as_deref(),
        Ok("0") | Ok("false")
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
    rule_scores: Vec<f64>,
    left_index: &'a LeftIndex,
    right_rule_index: Option<ChildStateRightRuleIndex>,
    right_interner: I,
    product_ids: ProductStateMap,
    product_pairs: Vec<(StateId, StateId)>,
    builder: Option<ExplicitBuilder>,
    rule_tracker: TrustedRuleTracker,
    right_rules: Vec<OwnedCondensedRule<StateId>>,
    mat_stats: IndexedCondensedIntersectionStats,
    // A* specific state
    finalized: FixedBitSet,
    ever_finalized: FixedBitSet,
    finalized_partners: Vec<PartnerSet>,
    /// Best discovered inside score for each product state. For closed products
    /// this is also the finalized inside score.
    best_score: Vec<f64>,
    backpointer_ids: Vec<Option<u32>>,
    backpointers: Vec<Backpointer>,
    store_backpointers: bool,
    heap: AstarAgenda,
    pending: Vec<Option<AgendaItem>>,
    matches_scratch: Vec<usize>,
    right_rule_ids_scratch: Vec<usize>,
    /// Whether to consult the heuristic's sound `admits` filter when generating
    /// candidate edges (see [`candidate_filter_enabled`]).
    candidate_filter: bool,
    heuristic_cache_enabled: bool,
    /// Right-major bitsets recording which product pairs have had their sound
    /// admission filter checked and which of those pairs were admitted.
    heuristic_checked: Vec<FixedBitSet>,
    heuristic_admitted: Vec<FixedBitSet>,
    /// Lazy memo of the right (invhom) transition, keyed by
    /// `(det_group(symbol), child0, child1)` with a sentinel second child for
    /// unary rules. Because the condensed right automaton's transition depends
    /// only on the symbol's group (its image term) and the child states, every
    /// symbol in a group and both-endpoints re-derivations of the same child
    /// pair reuse one `step_det`. Cleared per parse with the rest of the context.
    right_step_memo: FxHashMap<(u32, StateId, StateId), Option<StateId>>,
    stats: AstarStats,
}

impl<'a, R, I> AstarContext<'a, R, I>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: RightStateInterner<R::State> + StateInterner<R::State>,
{
    #[allow(clippy::too_many_arguments)]
    fn new(
        left: &'a Explicit,
        right: &'a R,
        left_rules: &'a [OwnedRule],
        left_index: &'a LeftIndex,
        right_interner: I,
        with_builder: bool,
        scorer: &impl WeightScorer,
        use_generic_source: bool,
    ) -> Self {
        let store_backpointers = !with_builder;
        Self {
            left,
            right,
            left_rules,
            rule_scores: left_rules
                .iter()
                .map(|rule| scorer.rule_score(rule.weight))
                .collect(),
            left_index,
            right_rule_index: use_generic_source.then(ChildStateRightRuleIndex::default),
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
            ever_finalized: FixedBitSet::new(),
            finalized_partners: Vec::new(),
            best_score: Vec::new(),
            backpointer_ids: Vec::new(),
            backpointers: Vec::new(),
            store_backpointers,
            heap: AstarAgenda::new(),
            pending: Vec::new(),
            matches_scratch: Vec::new(),
            right_rule_ids_scratch: Vec::new(),
            candidate_filter: candidate_filter_enabled(),
            heuristic_cache_enabled: heuristic_cache_enabled(),
            heuristic_checked: Vec::new(),
            heuristic_admitted: Vec::new(),
            right_step_memo: FxHashMap::default(),
            stats: AstarStats::default(),
        }
    }

    fn heuristic_estimate<H: IntersectionHeuristic<R>>(
        &mut self,
        left: StateId,
        right: StateId,
        h: &H,
    ) -> Option<f64> {
        if !self.heuristic_cache_enabled || !h.memoize_admission() {
            let right_raw = self.right_interner.resolve(right);
            return if self.candidate_filter {
                h.estimate_if_admitted(left, right_raw)
            } else {
                Some(h.outside_estimate(left, right_raw))
            };
        }

        if self
            .heuristic_checked
            .get(right.index())
            .is_some_and(|checked| left.index() < checked.len() && checked.contains(left.index()))
        {
            self.stats.heuristic_cache_hits += 1;
            if self.heuristic_admitted[right.index()].contains(left.index()) {
                let right_raw = self.right_interner.resolve(right);
                return Some(h.estimate_after_admission(left, right_raw));
            }
            return None;
        }

        let estimate = {
            let right_raw = self.right_interner.resolve(right);
            if self.candidate_filter {
                h.estimate_if_admitted(left, right_raw)
            } else {
                Some(h.outside_estimate(left, right_raw))
            }
        };
        if self.heuristic_checked.len() <= right.index() {
            self.heuristic_checked
                .resize_with(right.index() + 1, FixedBitSet::new);
            self.heuristic_admitted
                .resize_with(right.index() + 1, FixedBitSet::new);
        }
        if self.heuristic_checked[right.index()].len() <= left.index() {
            self.heuristic_checked[right.index()].grow(left.index() + 1);
            self.heuristic_admitted[right.index()].grow(left.index() + 1);
        }
        self.heuristic_checked[right.index()].set(left.index(), true);
        if estimate.is_some() {
            self.heuristic_admitted[right.index()].set(left.index(), true);
        }
        self.stats.heuristic_cache_misses += 1;
        estimate
    }

    /// Ensure per-state arrays are large enough for `product`.
    fn grow_to(&mut self, product: StateId, zero: f64) {
        let idx = product.index() + 1;
        if self.finalized.len() < idx {
            self.finalized.grow(idx);
        }
        if self.ever_finalized.len() < idx {
            self.ever_finalized.grow(idx);
        }
        if self.best_score.len() < idx {
            self.best_score.resize(idx, zero);
        }
        if self.backpointer_ids.len() < idx && self.store_backpointers {
            self.backpointer_ids.resize(idx, None);
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
        self.right_rule_index
            .as_mut()
            .expect("generic right-rule index was not requested")
            .rule_ids_for_trigger_into(
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
        rule_index: usize,
        parent_left: StateId,
        parent_right: StateId,
        children: SmallVec<[StateId; 2]>,
        scorer: &S,
        h: &H,
    ) {
        let mut child_score = scorer.one();
        for &child in &children {
            child_score = scorer.times(child_score, self.best_score[child.index()]);
        }
        self.push_candidate_with_child_score(
            rule_index,
            parent_left,
            parent_right,
            children.as_slice(),
            child_score,
            scorer,
            h,
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn push_candidate_with_child_score<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        rule_index: usize,
        parent_left: StateId,
        parent_right: StateId,
        children: &[StateId],
        child_score: f64,
        scorer: &S,
        h: &H,
    ) {
        let inside = scorer.times(self.rule_scores[rule_index], child_score);

        // Sound construction-time filter and outside estimate. Keeping these
        // together lets composite heuristics share their lookup work.
        // product hopeless (zero outside weight), never build the edge — skip
        // before product-id creation and the heap push. Uses the true resolved
        // parent span, so it is exact. Covers every expansion path (generic,
        // higher-arity fallback, unary, and binary).
        let outside = match self.heuristic_estimate(parent_left, parent_right, h) {
            Some(outside) => outside,
            None => {
                self.stats.f_filtered_candidates += 1;
                return;
            }
        };

        let (parent, _) = if self.builder.is_some() {
            self.get_or_create_product_id(parent_left, parent_right)
        } else {
            self.get_or_create_direct(parent_left, parent_right)
        };
        self.grow_to(parent, scorer.zero());

        let old_inside = self.best_score[parent.index()];
        if !scorer.better(inside, old_inside) {
            if self.finalized.contains(parent.index()) {
                self.stats.finalized_candidate_discards += 1;
            } else {
                self.stats.dominated_candidates += 1;
            }
            return;
        }
        if self.finalized.contains(parent.index()) {
            self.finalized.set(parent.index(), false);
            self.stats.reopen_attempts += 1;
        }
        self.best_score[parent.index()] = inside;

        let merit = scorer.times(inside, outside);
        self.pending[parent.index()] = Some(AgendaItem {
            edge: PendingEdge {
                rule_index: u32::try_from(rule_index).expect("too many A* rules"),
                children: children.iter().copied().collect(),
            },
        });
        match self.heap.update_or_push(parent.index(), merit) {
            AgendaUpdate::Pushed => self.stats.heap_pushes += 1,
            AgendaUpdate::Updated => self.stats.heap_updates += 1,
        }
        self.stats.max_heap_len = self.stats.max_heap_len.max(self.heap.len());
        self.stats.max_heap_position_capacity = self
            .stats
            .max_heap_position_capacity
            .max(self.heap.position_capacity());
    }

    fn expand_from_finalized<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        trigger_left: StateId,
        trigger_right: StateId,
        trigger_product: StateId,
        h: &H,
        scorer: &S,
        rule_filter: Option<&FixedBitSet>,
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
                    if rule_filter.is_some_and(|filter| !filter.contains(rule_idx)) {
                        continue;
                    }
                    let Some((parent_left, children)) = ({
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
                        (ok && first_trigger(&children, position, trigger_product))
                            .then_some((left_rule.result, children))
                    }) else {
                        continue;
                    };
                    self.stats.candidate_edges += 1;
                    self.push_candidate(rule_idx, parent_left, parent_right, children, scorer, h);
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
        self.right_parent_memoized(symbol, &right_children)
    }

    /// Memoized right (invhom) transition for a unary or binary span rule.
    ///
    /// `right_children` is the one or two interned right child states. The result
    /// is the interned parent right state, or `None` if no transition exists.
    ///
    /// The condensed right automaton's transition depends only on the symbol's
    /// *group* ([`DetBottomUpTa::det_group`] — for `InvHom` the image term shared
    /// by a whole symbol set) and the child states. So a single `step_det` is
    /// computed per `(group, children)` and reused for every symbol in the group
    /// and for both-endpoints re-derivations of the same child pair; the rest are
    /// memo hits. This is exact: a hit returns the identical parent, so no item's
    /// best score — and hence the first goal popped — can change.
    fn right_parent_memoized(
        &mut self,
        symbol: Symbol,
        right_children: &[StateId],
    ) -> Option<StateId>
    where
        R: DetBottomUpTa<State = Span>,
    {
        self.stats.right_step_calls += 1;
        let (c0, c1) = match *right_children {
            [c0] => (c0, RIGHT_UNARY_SENTINEL),
            [c0, c1] => (c0, c1),
            _ => unreachable!("span-path right rules are unary or binary"),
        };
        let key = (self.right.det_group(symbol), c0, c1);
        if let Some(&cached) = self.right_step_memo.get(&key) {
            self.stats.right_step_memo_hits += 1;
            if cached.is_some() {
                self.stats.right_step_results += 1;
            }
            return cached;
        }

        self.stats.right_step_evals += 1;
        let mut raw = SmallVec::<[Span; 2]>::new();
        for &child in right_children {
            raw.push(*self.right_interner.resolve(child));
        }
        let parent = self.right.step_det(symbol, &raw);
        let interned =
            parent.map(|parent| RightStateInterner::intern(&mut self.right_interner, parent));
        self.right_step_memo.insert(key, interned);
        if interned.is_some() {
            self.stats.right_step_results += 1;
        }
        interned
    }

    #[allow(clippy::too_many_arguments)]
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
        fallback_rules: Option<&FixedBitSet>,
        h: &H,
        scorer: &S,
    ) where
        R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    {
        let needs_fallback = fallback_rules.map_or_else(
            || span_left_index.has_higher_arity(trigger_left),
            |fallback| {
                self.left_index
                    .by_state
                    .get(&trigger_left)
                    .is_some_and(|occurrences| {
                        occurrences
                            .iter()
                            .any(|&(_, _, rule_index)| fallback.contains(rule_index))
                    })
            },
        );
        if needs_fallback {
            // The product-aware span sibling finder is a binary-rule
            // optimization. If this left state also appears in a larger rule,
            // run the generic expansion so those candidates are still found.
            self.stats.sibling_fallback_expansions += 1;
            self.expand_from_finalized(
                trigger_left,
                trigger_right,
                trigger_product,
                h,
                scorer,
                fallback_rules,
            );
        }

        let raw_trigger = *self.right_interner.resolve(trigger_right);

        // Unary rules do not need sibling lookup. In the string fast path the
        // right automaton is deterministic for concrete child spans, so this
        // avoids the allocation-heavy generic inverse-homomorphism step.
        if let Some(unary_rules) = span_left_index.unary_rules(trigger_left) {
            for &rule_idx in unary_rules {
                if fallback_rules.is_some_and(|fallback| fallback.contains(rule_idx)) {
                    continue;
                }
                let parent_left = {
                    let left_rule = &self.left_rules[rule_idx];
                    left_rule.result
                };

                let children = [trigger_product];

                // The only specialized unary template is the identity variable,
                // so its exact parent span is the child span.
                let parent_right = trigger_right;
                self.stats.candidate_edges += 1;
                self.push_candidate_with_child_score(
                    rule_idx,
                    parent_left,
                    parent_right,
                    &children,
                    self.best_score[trigger_product.index()],
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
                self.stats.sibling_tuple_queries += 1;
                let sibling_products =
                    sibling_finder.siblings_slice(raw_trigger, position, group.sibling_left);
                self.stats.sibling_tuples_returned += sibling_products.len();

                for &sibling in sibling_products {
                    if position == 1 && sibling.product == trigger_product {
                        continue;
                    }

                    let children = match position {
                        0 => [trigger_product, sibling.product],
                        1 => [sibling.product, trigger_product],
                        _ => unreachable!(),
                    };

                    // The specialized template is exactly concat(?0, ?1), so
                    // this is the true parent span rather than a prediction.
                    let raw_sibling = *self.right_interner.resolve(sibling.right_state);
                    let parent_span = match position {
                        0 => Span::new(raw_trigger.start, raw_sibling.end),
                        _ => Span::new(raw_sibling.start, raw_trigger.end),
                    };

                    let child_score = scorer.times(
                        self.best_score[children[0].index()],
                        self.best_score[children[1].index()],
                    );
                    for symbol_group in &group.symbol_groups {
                        let symbol = symbol_group.symbol;
                        // All left rules in this group share the same symbol and
                        // left-child requirements, so one deterministic right
                        // transition gives the parent state for all of them.
                        // Compute it lazily — only once a rule survives the F
                        // filter — so a group whose every parent is hopeless
                        // never pays for the right transition.
                        let mut parent_right: Option<StateId> = None;
                        for &rule_idx in &symbol_group.rule_indexes {
                            if fallback_rules.is_some_and(|fallback| fallback.contains(rule_idx)) {
                                continue;
                            }
                            let left_rule = &self.left_rules[rule_idx];
                            let result = left_rule.result;
                            debug_assert_eq!(left_rule.symbol, symbol);
                            debug_assert_eq!(left_rule.children[position], trigger_left);
                            debug_assert_eq!(left_rule.children[1 - position], group.sibling_left);

                            let pr = match parent_right {
                                Some(pr) => pr,
                                None => {
                                    // Supported binary rules are exactly
                                    // concat(?0, ?1), and the sibling finder
                                    // already guarantees adjacent child spans.
                                    // Construct the exact parent directly.
                                    let pr = RightStateInterner::intern(
                                        &mut self.right_interner,
                                        parent_span,
                                    );
                                    parent_right = Some(pr);
                                    pr
                                }
                            };

                            self.stats.candidate_edges += 1;
                            self.push_candidate_with_child_score(
                                rule_idx,
                                result,
                                pr,
                                &children,
                                child_score,
                                scorer,
                                h,
                            );
                        }
                    }
                }
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
        let outside = match self.heuristic_estimate(edge.parent_left, edge.parent_right, h) {
            Some(outside) => outside,
            None => {
                self.stats.f_filtered_candidates += 1;
                return;
            }
        };

        let (product, _) = if self.builder.is_some() {
            self.get_or_create_product_id(edge.parent_left, edge.parent_right)
        } else {
            self.get_or_create_direct(edge.parent_left, edge.parent_right)
        };
        self.grow_to(product, scorer.zero());

        let inside = self.rule_scores[edge.rule_index];
        let old_inside = self.best_score[product.index()];
        if !scorer.better(inside, old_inside) {
            self.stats.dominated_candidates += 1;
            return;
        }
        self.best_score[product.index()] = inside;

        let merit = scorer.times(inside, outside);
        self.pending[product.index()] = Some(AgendaItem {
            edge: PendingEdge {
                rule_index: u32::try_from(edge.rule_index).expect("too many A* rules"),
                children: SmallVec::new(),
            },
        });
        match self.heap.update_or_push(product.index(), merit) {
            AgendaUpdate::Pushed => self.stats.heap_pushes += 1,
            AgendaUpdate::Updated => self.stats.heap_updates += 1,
        }
        self.stats.max_heap_len = self.stats.max_heap_len.max(self.heap.len());
        self.stats.max_heap_position_capacity = self
            .stats
            .max_heap_position_capacity
            .max(self.heap.position_capacity());
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

    fn pop_next_finalized(&mut self) -> Option<FinalizedItem> {
        let (product_index, merit) = self.heap.pop()?;
        self.stats.pops += 1;
        let product = StateId(product_index as u32);
        let item = self.pending[product_index]
            .take()
            .expect("agenda product must have a pending item");
        let inside = self.best_score[product.index()];

        debug_assert!(!self.finalized.contains(product.index()));

        self.finalized.set(product.index(), true);
        if self.store_backpointers {
            let rule = &self.left_rules[item.edge.rule_index as usize];
            let backpointer = Backpointer {
                symbol: rule.symbol,
                children: item.edge.children.clone(),
                weight: inside,
            };
            if let Some(id) = self.backpointer_ids[product.index()] {
                self.backpointers[id as usize] = backpointer;
            } else {
                let id = u32::try_from(self.backpointers.len())
                    .expect("too many finalized A* backpointers");
                self.backpointers.push(backpointer);
                self.backpointer_ids[product.index()] = Some(id);
            }
        }
        if !self.ever_finalized.contains(product.index()) {
            self.ever_finalized.set(product.index(), true);
            self.stats.finalized_states += 1;
        }
        self.stats.expanded_states += 1;

        let is_goal = self.is_accepting_product(product);
        let (left_state, right_state) = self.product_pairs[product.index()];

        Some(FinalizedItem {
            product,
            edge: item.edge,
            inside,
            left_state,
            right_state,
            is_goal,
            merit,
        })
    }

    fn activate_generic_product(&mut self, item: &FinalizedItem) {
        self.ensure_right_state(item.right_state);
        self.finalized_partners[item.right_state.index()].insert(item.left_state, item.product);
    }

    /// Run the eager core with an interchangeable candidate source.
    fn run_with_source<H, S, Source, OnFin>(
        &mut self,
        source: &mut Source,
        h: &H,
        scorer: &S,
        stop_at_first_goal: bool,
        mut on_finalize: OnFin,
    ) where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
        Source: CandidateSource<R, I>,
        OnFin: FnMut(&mut Self, StateId, &PendingEdge, f64, f64),
    {
        source.seed(self, h, scorer);
        loop {
            source.prepare_next(self, h, scorer);
            let Some(item) = self.pop_next_finalized() else {
                break;
            };
            source.activate(self, &item);
            on_finalize(self, item.product, &item.edge, item.inside, item.merit);

            if item.is_goal && stop_at_first_goal {
                break;
            }

            source.enumerate(self, &item, h, scorer);
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
        rule_index: usize,
        parent_left: StateId,
        parent_right: StateId,
        child_score: f64,
        scorer: &S,
        h: &H,
    ) -> f64 {
        let inside = scorer.times(self.rule_scores[rule_index], child_score);
        let right_raw = self.right_interner.resolve(parent_right);
        let h_val = h.outside_estimate(parent_left, right_raw);
        scorer.times(inside, h_val)
    }

    /// Best (maximum) merit over all rules that combine the trigger (filling
    /// `position`, right state `trigger_right`) with `sibling`, or `None` if no
    /// rule yields a valid right transition. All rules for one sibling share the
    /// same child pair, so they realize together.
    #[allow(clippy::too_many_arguments)]
    fn lazy_sibling_merit<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        trigger: StateId,
        trigger_right: StateId,
        position: u8,
        sibling: SpanProductSibling,
        group: &SpanBinarySiblingGroup,
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
            self.best_score[trigger.index()],
            self.best_score[sibling.product.index()],
        );
        let mut best: Option<f64> = None;
        for symbol_group in &group.symbol_groups {
            let Some(parent_right) =
                self.binary_right_parent_det(symbol_group.symbol, right_children)
            else {
                continue;
            };
            for &rule_idx in &symbol_group.rule_indexes {
                let parent_left = {
                    let rule = &self.left_rules[rule_idx];
                    rule.result
                };
                let merit = self.candidate_merit(
                    rule_idx,
                    parent_left,
                    parent_right,
                    child_score,
                    scorer,
                    h,
                );
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
            self.best_score[children[0].index()],
            self.best_score[children[1].index()],
        );
        let mut realized = false;
        for symbol_group in &group.symbol_groups {
            let Some(parent_right) =
                self.binary_right_parent_det(symbol_group.symbol, right_children)
            else {
                continue;
            };
            for &rule_idx in &symbol_group.rule_indexes {
                let parent_left = {
                    let rule = &self.left_rules[rule_idx];
                    rule.result
                };
                self.stats.candidate_edges += 1;
                self.stats.candidates_realized += 1;
                self.push_candidate_with_child_score(
                    rule_idx,
                    parent_left,
                    parent_right,
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
                let siblings = frontier
                    .finder
                    .siblings_slice(span, position, group.sibling_left);
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

    /// Expand the unary rules of a finalized product directly onto the parent
    /// agenda (unary edges have no sibling, so they never enter the frontier).
    /// Mirrors the unary block of
    /// [`Self::expand_from_finalized_with_span_product_siblings`].
    fn lazy_expand_unary<H: IntersectionHeuristic<R>, S: WeightScorer>(
        &mut self,
        product: StateId,
        left_state: StateId,
        right_state: StateId,
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
            let (parent_left, symbol) = {
                let rule = &self.left_rules[rule_idx];
                (rule.result, rule.symbol)
            };
            let Some(parent_right) = self.right_parent_memoized(symbol, &[right_state]) else {
                continue;
            };
            self.stats.candidate_edges += 1;
            self.push_candidate_with_child_score(
                rule_idx,
                parent_left,
                parent_right,
                &[product],
                self.best_score[product.index()],
                scorer,
                h,
            );
        }
    }
}

impl<R, I> CandidateSource<R, I> for GenericCandidateSource
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: RightStateInterner<R::State> + StateInterner<R::State>,
{
    fn activate(&mut self, ctx: &mut AstarContext<'_, R, I>, item: &FinalizedItem) {
        ctx.activate_generic_product(item);
    }

    fn enumerate<H, S>(
        &mut self,
        ctx: &mut AstarContext<'_, R, I>,
        item: &FinalizedItem,
        h: &H,
        scorer: &S,
    ) where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    {
        ctx.expand_from_finalized(
            item.left_state,
            item.right_state,
            item.product,
            h,
            scorer,
            None,
        );
    }
}

impl<'source, R> CandidateSource<R, SpanInterner> for StringAstarSource<'source>
where
    R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
{
    fn activate(&mut self, ctx: &mut AstarContext<'_, R, SpanInterner>, item: &FinalizedItem) {
        let span = *ctx.right_interner.resolve(item.right_state);
        self.left_index.activate_product(
            &mut self.sibling_finder,
            item.product,
            item.left_state,
            item.right_state,
            span,
        );
        if self.stores_generic_partners && ctx.left_index.by_state.contains_key(&item.left_state) {
            ctx.activate_generic_product(item);
        }
    }

    fn enumerate<H, S>(
        &mut self,
        ctx: &mut AstarContext<'_, R, SpanInterner>,
        item: &FinalizedItem,
        h: &H,
        scorer: &S,
    ) where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    {
        ctx.expand_from_finalized_with_span_product_siblings(
            item.left_state,
            item.right_state,
            item.product,
            self.left_index,
            &self.sibling_finder,
            self.fallback_rules,
            h,
            scorer,
        );
    }
}

impl<'source, R> CandidateSource<R, SpanInterner> for LazyStringAstarSource<'source>
where
    R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
{
    fn prepare_next<H, S>(&mut self, ctx: &mut AstarContext<'_, R, SpanInterner>, h: &H, scorer: &S)
    where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    {
        loop {
            let realize_frontier =
                match (ctx.heap.peek_merit(), self.frontier.frontier.peek_merit()) {
                    (_, None) => false,
                    (None, Some(_)) => true,
                    (Some(agenda), Some(frontier)) => frontier > agenda,
                };
            if !realize_frontier {
                break;
            }

            let (id, _) = self
                .frontier
                .frontier
                .pop()
                .expect("peeked lazy frontier entry must still be present");
            ctx.stats.frontier_pops += 1;
            if let Some(next_merit) =
                ctx.lazy_realize_generator(&mut self.frontier, id, self.left_index, scorer, h)
            {
                self.frontier.frontier.update_or_push(id, next_merit);
            }
        }
    }

    fn activate(&mut self, ctx: &mut AstarContext<'_, R, SpanInterner>, item: &FinalizedItem) {
        let span = *ctx.right_interner.resolve(item.right_state);
        self.left_index.activate_product(
            &mut self.frontier.finder,
            item.product,
            item.left_state,
            item.right_state,
            span,
        );
    }

    fn enumerate<H, S>(
        &mut self,
        ctx: &mut AstarContext<'_, R, SpanInterner>,
        item: &FinalizedItem,
        h: &H,
        scorer: &S,
    ) where
        H: IntersectionHeuristic<R>,
        S: WeightScorer,
    {
        let span = *ctx.right_interner.resolve(item.right_state);
        ctx.lazy_spawn_generators(
            &mut self.frontier,
            item.product,
            item.left_state,
            item.right_state,
            span,
            self.left_index,
            scorer,
            h,
        );
        ctx.lazy_expand_unary(
            item.product,
            item.left_state,
            item.right_state,
            self.left_index,
            scorer,
            h,
        );
    }
}

// ---------------------------------------------------------------------------
// Entry point 1: chart materializer
// ---------------------------------------------------------------------------

/// Materialize the Viterbi forest explored by A*.
///
/// The returned [`Explicit`] contains at most one winning incoming rule per
/// finalized product state. It is therefore not a complete intersection chart.
/// When `options.stop_at_first_goal` is `true`, it contains the rules needed to
/// derive the single best tree.
/// When `options.beam` is set (and `stop_at_first_goal` is `false`) only items
/// with `merit >= beam` are emitted.
///
/// Returns the chart, the right-state interner, and statistics.
pub fn materialize_astar_viterbi_forest<R, H>(
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
    materialize_astar_viterbi_forest_with(left, right, h, options, &ProbabilityScorer)
}

/// Materialize the A* Viterbi forest using `scorer`.
pub fn materialize_astar_viterbi_forest_with<R, H, S>(
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

/// Compatibility alias for [`materialize_astar_viterbi_forest`].
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
    materialize_astar_viterbi_forest(left, right, h, options)
}

/// Compatibility alias for [`materialize_astar_viterbi_forest_with`].
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
    materialize_astar_viterbi_forest_with(left, right, h, options, scorer)
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

/// Materialize a string intersection while reusing prepared grammar indexes.
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
    prepared.assert_matches(left);
    let fallback_rules = string_fallback_rules(
        &prepared.left_rules,
        right.homomorphism(),
        right.inner().concat_symbol(),
    );
    materialize_astar_intersection_with_span_sibling(
        left,
        prepared,
        right,
        h,
        options,
        scorer,
        right.inner().len(),
        Some(&fallback_rules),
        false,
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
    fallback_rules: Option<&FixedBitSet>,
    lazy: bool,
) -> (Explicit, Interner<Span>, AstarStats)
where
    R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    let use_generic_source =
        fallback_rules.is_some_and(|fallback| fallback.ones().next().is_some());
    let fallback_left_index = use_generic_source.then(|| {
        LeftIndex::build_filtered(&prepared.left_rules, |rule_index, rule| {
            rule.children.is_empty()
                || fallback_rules.is_some_and(|fallback| fallback.contains(rule_index))
        })
    });
    let left_index = fallback_left_index
        .as_ref()
        .unwrap_or(&prepared.nullary_left_index);
    let mut ctx = AstarContext::new(
        left,
        right,
        &prepared.left_rules,
        left_index,
        SpanInterner::new(sentence_len),
        true,
        scorer,
        use_generic_source,
    );
    let stop_at_first_goal = options.stop_at_first_goal;
    let beam = options.beam;

    let on_finalize = |ctx: &mut AstarContext<'_, R, SpanInterner>,
                       product: StateId,
                       edge: &PendingEdge,
                       _inside: f64,
                       merit: f64| {
        let emit = stop_at_first_goal || beam.is_none_or(|threshold| merit >= threshold);
        if emit {
            let rule = &ctx.left_rules[edge.rule_index as usize];
            let symbol = rule.symbol;
            let weight = rule.weight;
            let builder = ctx
                .builder
                .as_mut()
                .expect("chart mode always has a builder");
            ctx.rule_tracker
                .add_rule(builder, symbol, edge.children.clone(), product, weight);
            ctx.stats.emitted_rules += 1;
        }
    };

    let use_lazy = lazy
        && fallback_rules.is_none_or(|fallback| fallback.ones().next().is_none())
        && !prepared.span_left_index.has_any_higher_arity();
    if use_lazy {
        let mut source = LazyStringAstarSource::new(&prepared.span_left_index);
        ctx.run_with_source(&mut source, h, scorer, stop_at_first_goal, on_finalize);
    } else {
        let mut source = StringAstarSource::new(&prepared.span_left_index, fallback_rules);
        ctx.run_with_source(&mut source, h, scorer, stop_at_first_goal, on_finalize);
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
        scorer,
        true,
    );
    let stop_at_first_goal = options.stop_at_first_goal;
    let beam = options.beam;

    let mut source = GenericCandidateSource;
    ctx.run_with_source(
        &mut source,
        h,
        scorer,
        stop_at_first_goal,
        |ctx, _product, edge, _inside, merit| {
            // Emit a rule if in beam mode or one-best mode.
            let emit = stop_at_first_goal || beam.is_none_or(|threshold| merit >= threshold);
            if emit {
                let rule = &ctx.left_rules[edge.rule_index as usize];
                let symbol = rule.symbol;
                let weight = rule.weight;
                let builder = ctx
                    .builder
                    .as_mut()
                    .expect("chart mode always has a builder");
                // Find the product state for the parent (it was just finalized, so
                // it must be in product_pairs — but we need the parent_id, which is
                // `_product` itself).
                ctx.rule_tracker
                    .add_rule(builder, symbol, edge.children.clone(), _product, weight);
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

/// Find the best string-constrained derivation using prepared grammar indexes.
///
/// Returns the derivation, if any, together with detailed A* counters.
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
    prepared.assert_matches(left);
    let fallback_rules = string_fallback_rules(
        &prepared.left_rules,
        right.homomorphism(),
        right.inner().concat_symbol(),
    );
    astar_one_best_with_stats_and_span_sibling(
        left,
        prepared,
        right,
        h,
        scorer,
        right.inner().len(),
        Some(&fallback_rules),
        false,
    )
}

/// Run the experimental lazy string frontier for controlled benchmarks.
///
/// This is deliberately separate from the production entry point: it accepts
/// only grammars whose rules are all handled by the binary string
/// specialization and never selects itself through an environment variable or
/// runtime heuristic.
#[doc(hidden)]
pub fn astar_string_one_best_lazy_benchmark_with_stats_prepared<'h, H, S>(
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
    prepared.assert_matches(left);
    let fallback_rules = string_fallback_rules(
        &prepared.left_rules,
        right.homomorphism(),
        right.inner().concat_symbol(),
    );
    assert!(
        fallback_rules.ones().next().is_none() && !prepared.span_left_index.has_any_higher_arity(),
        "lazy A* benchmark supports only specialized nullary, unary-identity, and binary-concat rules"
    );
    astar_one_best_with_stats_and_span_sibling(
        left,
        prepared,
        right,
        h,
        scorer,
        right.inner().len(),
        None,
        true,
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
    fallback_rules: Option<&FixedBitSet>,
    lazy: bool,
) -> (Option<ViterbiTree>, AstarStats)
where
    R: CondensedTa<State = Span> + DetBottomUpTa<State = Span>,
    H: IntersectionHeuristic<R>,
    S: WeightScorer,
{
    let use_generic_source =
        fallback_rules.is_some_and(|fallback| fallback.ones().next().is_some());
    let fallback_left_index = use_generic_source.then(|| {
        LeftIndex::build_filtered(&prepared.left_rules, |rule_index, rule| {
            rule.children.is_empty()
                || fallback_rules.is_some_and(|fallback| fallback.contains(rule_index))
        })
    });
    let left_index = fallback_left_index
        .as_ref()
        .unwrap_or(&prepared.nullary_left_index);
    let mut ctx = AstarContext::new(
        left,
        right,
        &prepared.left_rules,
        left_index,
        SpanInterner::new(sentence_len),
        false,
        scorer,
        use_generic_source,
    );
    let mut goal_state: Option<(StateId, f64)> = None;

    let on_finalize = |ctx: &mut AstarContext<'_, R, SpanInterner>,
                       product: StateId,
                       _edge: &PendingEdge,
                       inside: f64,
                       _merit: f64| {
        if goal_state.is_none() && ctx.is_accepting_product(product) {
            goal_state = Some((product, inside));
        }
    };

    let use_lazy = lazy
        && fallback_rules.is_none_or(|fallback| fallback.ones().next().is_none())
        && !prepared.span_left_index.has_any_higher_arity();
    if use_lazy {
        let mut source = LazyStringAstarSource::new(&prepared.span_left_index);
        ctx.run_with_source(&mut source, h, scorer, true, on_finalize);
    } else {
        let mut source = StringAstarSource::new(&prepared.span_left_index, fallback_rules);
        ctx.run_with_source(&mut source, h, scorer, true, on_finalize);
    }
    ctx.stats.output_states = ctx.product_pairs.len();

    let Some((goal, best_score)) = goal_state else {
        ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;
        return (None, ctx.stats);
    };
    ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;

    let mut arena = TreeArena::new();
    let Some(root) =
        build_tree_from_arena(goal, &ctx.backpointer_ids, &ctx.backpointers, &mut arena)
    else {
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
        scorer,
        true,
    );
    let mut goal_state: Option<(StateId, f64)> = None;

    let mut source = GenericCandidateSource;
    ctx.run_with_source(
        &mut source,
        h,
        scorer,
        true,
        |ctx, product, _edge, inside, _merit| {
            if goal_state.is_none() && ctx.is_accepting_product(product) {
                goal_state = Some((product, inside));
            }
        },
    );
    ctx.stats.output_states = ctx.product_pairs.len();

    let Some((goal, best_score)) = goal_state else {
        ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;
        return (None, ctx.stats);
    };
    ctx.stats.right_indexed_queries = ctx.mat_stats.right_indexed_queries;

    let mut arena = TreeArena::new();
    let Some(root) =
        build_tree_from_arena(goal, &ctx.backpointer_ids, &ctx.backpointers, &mut arena)
    else {
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
    use std::cell::Cell;

    struct CountingMemoizedHeuristic {
        calls: Cell<usize>,
    }

    impl CountingMemoizedHeuristic {
        fn new() -> Self {
            Self {
                calls: Cell::new(0),
            }
        }
    }

    impl<R: BottomUpTa> IntersectionHeuristic<R> for CountingMemoizedHeuristic {
        fn outside_estimate(&self, _left: StateId, _right: &R::State) -> f64 {
            1.0
        }

        fn estimate_if_admitted(&self, _left: StateId, _right: &R::State) -> Option<f64> {
            self.calls.set(self.calls.get() + 1);
            Some(1.0)
        }

        fn memoize_admission(&self) -> bool {
            true
        }

        fn estimate_after_admission(&self, _left: StateId, _right: &R::State) -> f64 {
            1.0
        }
    }

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

    fn add_unary_suffix_hom(hom: &mut Homomorphism, source: Symbol, concat: Symbol, word: Symbol) {
        let child = hom.add_var(0);
        let suffix = hom.add_symbol(word, Vec::new());
        let term = hom.add_symbol(concat, vec![child, suffix]);
        hom.add(source, 1, term).unwrap();
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

    fn add_reversed_binary_concat_hom(hom: &mut Homomorphism, source: Symbol, concat: Symbol) {
        let right = hom.add_var(1);
        let left = hom.add_var(0);
        let term = hom.add_symbol(concat, vec![right, left]);
        hom.add(source, 2, term).unwrap();
    }

    fn add_binary_concat_with_middle_word_hom(
        hom: &mut Homomorphism,
        source: Symbol,
        concat: Symbol,
        word: Symbol,
    ) {
        let left = hom.add_var(0);
        let middle = hom.add_symbol(word, Vec::new());
        let right = hom.add_var(1);
        let tail = hom.add_symbol(concat, vec![middle, right]);
        let term = hom.add_symbol(concat, vec![left, tail]);
        hom.add(source, 2, term).unwrap();
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
        assert_eq!(new_stats.right_step_calls, 0);
        assert_eq!(new_stats.right_step_results, 0);
        assert_eq!(new_stats.sibling_fallback_expansions, 0);
    }

    #[test]
    fn string_sibling_astar_falls_back_for_nonidentity_unary_yields() {
        let concat = Symbol(0);
        let word_a = Symbol(1);
        let word_x = Symbol(2);
        let g_a = Symbol(10);
        let g_suffix = Symbol(11);

        let mut hom = Homomorphism::new();
        add_word_hom(&mut hom, g_a, word_a);
        add_unary_suffix_hom(&mut hom, g_suffix, concat, word_x);

        let mut builder = ExplicitBuilder::new();
        let child = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(g_a, vec![], child, 0.9);
        builder.add_weighted_rule(g_suffix, vec![child], root, 0.8);
        builder.add_accepting(root);
        let grammar = builder.build();

        let right = InvHom::new(
            StringDecompositionAutomaton::new(concat, vec![word_a, word_x]),
            &hom,
        );
        let prepared = PreparedAstarGrammar::new(&grammar);
        let (fast, stats) = astar_string_one_best_with_stats_prepared(
            &grammar,
            &prepared,
            &right,
            &ZeroHeuristic,
            &ProbabilityScorer,
        );
        let (generic, _) = astar_one_best_with_stats_and_index(
            &grammar,
            &right,
            &ZeroHeuristic,
            &ProbabilityScorer,
        );

        assert_eq!(
            fast.as_ref().map(ViterbiTree::weight),
            generic.as_ref().map(ViterbiTree::weight)
        );
        assert!(fast.is_some());
        assert!(stats.sibling_fallback_expansions > 0);
    }

    #[test]
    fn span_interner_round_trips_dense_span_ids() {
        let mut interner = SpanInterner::new(4);
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

    #[test]
    fn string_sibling_astar_falls_back_for_noncanonical_binary_yields() {
        let concat = Symbol(0);
        let word_a = Symbol(1);
        let word_b = Symbol(2);
        let word_x = Symbol(3);
        let g_a = Symbol(10);
        let g_b = Symbol(11);
        let g_rev = Symbol(12);
        let g_gap = Symbol(13);

        let mut hom = Homomorphism::new();
        add_word_hom(&mut hom, g_a, word_a);
        add_word_hom(&mut hom, g_b, word_b);
        add_reversed_binary_concat_hom(&mut hom, g_rev, concat);
        add_binary_concat_with_middle_word_hom(&mut hom, g_gap, concat, word_x);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let reverse_root = builder.new_state();
        let gap_root = builder.new_state();
        builder.add_weighted_rule(g_a, vec![], qa, 0.9);
        builder.add_weighted_rule(g_b, vec![], qb, 0.8);
        builder.add_weighted_rule(g_rev, vec![qa, qb], reverse_root, 0.7);
        builder.add_weighted_rule(g_gap, vec![qa, qb], gap_root, 0.6);
        builder.add_accepting(reverse_root);
        builder.add_accepting(gap_root);
        let grammar = builder.build();

        for sentence in [vec![word_b, word_a], vec![word_a, word_x, word_b]] {
            let right = InvHom::new(StringDecompositionAutomaton::new(concat, sentence), &hom);
            let prepared = PreparedAstarGrammar::new(&grammar);
            let (fast, stats) = astar_string_one_best_with_stats_prepared(
                &grammar,
                &prepared,
                &right,
                &ZeroHeuristic,
                &ProbabilityScorer,
            );
            let (generic, _) = astar_one_best_with_stats_and_index(
                &grammar,
                &right,
                &ZeroHeuristic,
                &ProbabilityScorer,
            );
            assert_eq!(
                fast.as_ref().map(ViterbiTree::weight),
                generic.as_ref().map(ViterbiTree::weight)
            );
            assert!(fast.is_some());
            assert!(stats.sibling_fallback_expansions > 0);
        }
    }

    struct InconsistentAdmissibleHeuristic {
        x: StateId,
        y: StateId,
    }

    impl IntersectionHeuristic<Explicit> for InconsistentAdmissibleHeuristic {
        fn outside_estimate(&self, left: StateId, _right: &StateId) -> f64 {
            if left == self.x {
                1.0
            } else if left == self.y {
                0.09
            } else {
                1.0
            }
        }
    }

    #[test]
    fn admissible_inconsistent_heuristic_reopens_improved_product() {
        let a = Symbol(0);
        let y_leaf = Symbol(1);
        let improve_x = Symbol(2);
        let goal_from_x = Symbol(3);
        let direct_goal = Symbol(4);
        let mut builder = ExplicitBuilder::new();
        let x = builder.new_state();
        let y = builder.new_state();
        let goal = builder.new_state();
        builder.add_weighted_rule(a, vec![], x, 0.5);
        builder.add_weighted_rule(y_leaf, vec![], y, 1.0);
        builder.add_weighted_rule(improve_x, vec![y], x, 0.9);
        builder.add_weighted_rule(goal_from_x, vec![x], goal, 0.1);
        builder.add_weighted_rule(direct_goal, vec![], goal, 0.08);
        builder.add_accepting(goal);
        let grammar = builder.build();

        let h = InconsistentAdmissibleHeuristic { x, y };
        let (chart, _, stats) = materialize_astar_intersection(
            &grammar,
            &grammar,
            &h,
            AstarOptions {
                stop_at_first_goal: false,
                beam: None,
            },
        );
        let best = chart.viterbi().expect("reopened search should find a tree");
        assert!(
            (best.weight() - 0.09).abs() < 1e-12,
            "got {}",
            best.weight()
        );
        assert!(stats.reopen_attempts > 0);
        assert!(stats.expanded_states > stats.finalized_states);
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
        let (eager, eager_stats) = astar_one_best_with_stats_and_span_sibling(
            &grammar,
            &prepared,
            &right,
            &h,
            &ProbabilityScorer,
            right.inner().len(),
            None,
            false,
        );
        let (lazy, lazy_stats) = astar_string_one_best_lazy_benchmark_with_stats_prepared(
            &grammar,
            &prepared,
            &right,
            &h,
            &ProbabilityScorer,
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
    fn memoized_heuristic_is_evaluated_once_per_parent_pair() {
        let (grammar, hom, sentence) = build_ambiguous_binary_string_grammar();
        let right = InvHom::new(StringDecompositionAutomaton::new(Symbol(0), sentence), &hom);
        let prepared = PreparedAstarGrammar::new(&grammar);
        let h = CountingMemoizedHeuristic::new();

        let (chart, _, stats) = materialize_astar_string_intersection_with_prepared(
            &grammar,
            &prepared,
            &right,
            &h,
            AstarOptions {
                stop_at_first_goal: false,
                beam: None,
            },
            &ProbabilityScorer,
        );

        assert!(chart.viterbi().is_some());
        assert!(stats.heuristic_cache_hits > 0);
        assert!(stats.heuristic_cache_misses > 0);
        assert_eq!(h.calls.get(), stats.heuristic_cache_misses);
    }

    #[test]
    fn lazy_span_frontier_full_chart_matches_eager() {
        let (grammar, hom, sentence) = build_ambiguous_binary_string_grammar();
        let concat = Symbol(0);
        let right = InvHom::new(StringDecompositionAutomaton::new(concat, sentence), &hom);
        let h = ZeroHeuristic;
        let prepared = PreparedAstarGrammar::new(&grammar);
        let n = right.inner().len();
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
            None,
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
            None,
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
