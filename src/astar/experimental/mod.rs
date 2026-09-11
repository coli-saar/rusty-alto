//! Lazy candidate generation for the deterministic binary string-span A* path
//! (perf item N10), `Θ(n³ log n)` heap-successor variant.
//!
//! The eager span path, on each finalized product, immediately enumerates every
//! `siblings × rules` combination, resolves each parent product id, and offers it
//! to the per-product agenda. Most of those candidates are dominated or belong to
//! products that never finalize before the goal, yet each still pays a product-id
//! hash and a sift on the large parent agenda.
//!
//! The lazy frontier keeps the eager combination rule unchanged — the
//! later-finalized child is the trigger, combined with already-finalized siblings
//! recorded in the shared [`SpanProductSiblingFinder`] — but defers
//! *realization*. When a product finalizes it spawns one [`SpanGenerator`] per
//! `(position, sibling-left group)`. Each generator computes its candidates'
//! merits once and stores them in a **binary heap ordered by merit**, so its
//! next-best is a heap pop in `O(log siblings)` rather than a rescan in
//! `O(siblings)` — the difference between `Θ(n³ log n)` and `Θ(n⁴)` over the
//! chart (see `docs/n10-asymptotics.md`). Only when a generator is popped (its
//! best beats the parent agenda's best realized edge) does it resolve product ids
//! and push that sibling's rules onto the parent agenda.
//!
//! The cost of the heap successor is memory: each generator stores one entry per
//! sibling product in its snapshot (`Θ(n³)` live entries worst case), versus the
//! `O(1)` consumed-mask of the earlier rescan variant.

use super::*;
use crate::StateId;
use crate::algebras::{
    SpanAstarLeftIndex, SpanBinarySiblingGroup, SpanProductSibling, SpanProductSiblingFinder,
};
use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// One sibling of a generator, keyed by the best merit achievable by combining
/// the generator's trigger with this sibling (the max over the group's rules).
/// `BinaryHeap` is a max-heap, so the top is the highest-merit unrealized sibling.
#[derive(Clone, Copy, Debug)]
pub(super) struct SiblingEntry {
    pub(super) merit: f64,
    /// Index of the sibling within the generator's snapshot prefix of the shared
    /// finder slice (stable: the finder's per-`[boundary][left]` vectors only
    /// grow, so this index keeps pointing at the same product).
    pub(super) sibling_index: u32,
}

impl PartialEq for SiblingEntry {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for SiblingEntry {}
impl PartialOrd for SiblingEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SiblingEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher merit is greater (pops first). Ties broken toward the lower
        // sibling index for a deterministic, reproducible realization order.
        self.merit
            .total_cmp(&other.merit)
            .then_with(|| other.sibling_index.cmp(&self.sibling_index))
    }
}

/// A single binary combination site rooted at one finalized trigger product.
///
/// The generator computes the merit of every sibling once (at creation) and
/// holds them in `pending`, a max-heap by merit. Realizing pops the top sibling
/// and re-derives that sibling's rules from the shared finder; no rescan.
pub(super) struct SpanGenerator {
    /// The finalized trigger product (later-finalized child of the combination).
    pub(super) trigger: StateId,
    /// The trigger's right (span) state; resolves to the trigger span.
    pub(super) trigger_right: StateId,
    /// The trigger's left (grammar) state; selects the binary group list.
    pub(super) trigger_left: StateId,
    /// Child slot the trigger fills: `0` = left child, `1` = right child.
    pub(super) position: u8,
    /// Index into `binary_groups(trigger_left, position)`.
    pub(super) group_idx: u32,
    /// Unrealized siblings, ordered by merit (max-heap).
    pub(super) pending: BinaryHeap<SiblingEntry>,
}

/// Owns the shared sibling index, the generator arena, and the frontier heap.
///
/// Lives for the duration of one lazy candidate-source run, alongside the
/// existing per-product agenda in [`super::AstarContext`].
#[derive(Default)]
pub(super) struct SpanLazyFrontier {
    /// Shared per-`[boundary][left]` index of finalized products, reused exactly
    /// as on the eager span path (populated via `activate_product`).
    pub(super) finder: SpanProductSiblingFinder,
    /// Generator arena; a generator's id is its index here.
    pub(super) generators: Vec<SpanGenerator>,
    /// Frontier heap keyed by each active generator's best unrealized merit
    /// (reuses [`AstarAgenda`], which negates the key for max-merit order).
    pub(super) frontier: AstarAgenda,
}

impl SpanLazyFrontier {
    pub(super) fn new() -> Self {
        Self::default()
    }
}

/// Explicit experimental candidate source used only by lazy-frontier
/// equivalence tests and benchmark entry points.
pub(super) struct LazyStringAstarSource<'a> {
    pub(super) left_index: &'a SpanAstarLeftIndex,
    pub(super) frontier: SpanLazyFrontier,
}

impl<'a> LazyStringAstarSource<'a> {
    pub(super) fn new(left_index: &'a SpanAstarLeftIndex) -> Self {
        Self {
            left_index,
            frontier: SpanLazyFrontier::new(),
        }
    }
}

impl<'a, R, I> AstarContext<'a, R, I>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
    I: RightStateInterner<R::State> + StateInterner<R::State>,
{
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

/// Run the experimental lazy string frontier for controlled benchmarks.
///
/// This API is available only with the `experimental-lazy-astar` feature. It
/// accepts only grammars fully covered by the binary string specialization.
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

    let ctx = AstarContext::new(
        left,
        right,
        &prepared.left_rules,
        &prepared.nullary_left_index,
        SpanInterner::new(right.inner().len()),
        false,
        scorer,
        false,
    );
    let mut source = LazyStringAstarSource::new(&prepared.span_left_index);
    run_one_best_with_span_source(ctx, &mut source, h, scorer)
}
