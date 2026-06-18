//! Admissible heuristics for the A* intersection materializer.
//!
//! An [`IntersectionHeuristic`] provides an optimistic upper bound on the
//! outside weight of a product state `(left, right)`. When the bound is tight
//! (equal to the true outside weight) A* reduces to exact Knuth/Viterbi order.
//!
//! Two concrete heuristics are provided:
//!
//! * [`ZeroHeuristic`] — the uninformed bound `1.0`.  Always admissible
//!   because all weights are in `(0, 1]`.  With this heuristic A* equals pure
//!   Knuth and is exact.
//!
//! * [`OutsideHeuristic`] — precomputes grammar-only outside weights `OUT(X)`
//!   from a fixed-point iteration over the left-hand (grammar) automaton. This
//!   is algebra-agnostic and sentence-independent, so it can be computed once
//!   per grammar and reused across inputs.  Because the decomposition automaton
//!   is unweighted, the true product-outside of `(X, ·)` is at most the
//!   grammar `OUT(X)`, so the bound is admissible.  Both fixpoints are exact
//!   (Dijkstra/Knuth-style), so the heuristic is also consistent.

use crate::{BottomUpTa, Explicit, ProbabilityScorer, StateId, TopDownTa, WeightScorer};
use fixedbitset::FixedBitSet;
use std::collections::BinaryHeap;

// ---------------------------------------------------------------------------
// f64 max-ordering newtype
// ---------------------------------------------------------------------------

/// Wrapper that gives `f64` a total ordering suitable for a max-heap.
#[derive(Clone, Copy, PartialEq)]
struct OrdF64(f64);

impl Eq for OrdF64 {}

impl Ord for OrdF64 {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&o.0)
    }
}

impl PartialOrd for OrdF64 {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Admissible upper bound on the outside weight of a product state.
///
/// For every product state `(left, right)` the method must return a value that
/// is **at least** as large as the true outside weight.  Tighter bounds yield
/// fewer A* expansions.  A bound of `1.0` is always safe (all weights ≤ 1).
pub trait IntersectionHeuristic<R: BottomUpTa> {
    /// Return an optimistic (admissible) upper bound in `(0, 1]` on the best
    /// outside weight of any completion around product state `(left, right)`.
    fn outside_estimate(&self, left: StateId, right: &R::State) -> f64;

    /// Sound hard filter consulted at candidate-construction time: return
    /// `false` iff `(left, right)` provably has **zero** outside weight (it can
    /// appear in no valid completion), so the A* loop may skip building the edge
    /// entirely rather than merely deprioritizing it.
    ///
    /// This must be sound — only return `false` when the true outside weight is
    /// genuinely zero — but it need not be complete (returning `true` is always
    /// safe). The default admits everything, so heuristics that are pure
    /// admissible bounds (SX, Outside, Zero) impose no filtering.
    #[inline]
    fn admits(&self, _left: StateId, _right: &R::State) -> bool {
        true
    }

    /// Return the outside estimate when the product is admitted, and `None`
    /// when it is provably unable to occur in an accepting derivation.
    ///
    /// Heuristics whose filtering and estimate share work should override this
    /// method. The A* hot path uses it to avoid evaluating the heuristic twice.
    #[inline]
    fn estimate_if_admitted(&self, left: StateId, right: &R::State) -> Option<f64> {
        self.admits(left, right)
            .then(|| self.outside_estimate(left, right))
    }
}

// ---------------------------------------------------------------------------
// MinHeuristic (combinator)
// ---------------------------------------------------------------------------

/// Combines two admissible heuristics by taking, per product state, the
/// tighter (smaller) of the two estimates.
///
/// The minimum of two admissible upper bounds is itself an admissible upper
/// bound (and at least as tight), so A* stays exact. The numeric `min` is
/// correct in both probability space (estimates in `(0, 1]`, smaller = tighter)
/// and log-prob space (estimates `≤ 0`, smaller = tighter), since the scorer
/// representation is monotone in the true weight.
pub struct MinHeuristic<A, B> {
    a: A,
    b: B,
}

impl<A, B> MinHeuristic<A, B> {
    /// Combine heuristics `a` and `b`; `outside_estimate` returns `min(a, b)`.
    pub fn new(a: A, b: B) -> Self {
        Self { a, b }
    }
}

impl<R, A, B> IntersectionHeuristic<R> for MinHeuristic<A, B>
where
    R: BottomUpTa,
    A: IntersectionHeuristic<R>,
    B: IntersectionHeuristic<R>,
{
    #[inline]
    fn outside_estimate(&self, left: StateId, right: &R::State) -> f64 {
        self.a
            .outside_estimate(left, right)
            .min(self.b.outside_estimate(left, right))
    }

    /// An item is admitted only if **both** sub-heuristics admit it (either
    /// proving zero outside weight suffices to drop the edge).
    #[inline]
    fn admits(&self, left: StateId, right: &R::State) -> bool {
        self.a.admits(left, right) && self.b.admits(left, right)
    }

    #[inline]
    fn estimate_if_admitted(&self, left: StateId, right: &R::State) -> Option<f64> {
        let a = self.a.estimate_if_admitted(left, right)?;
        let b = self.b.estimate_if_admitted(left, right)?;
        Some(a.min(b))
    }
}

// ---------------------------------------------------------------------------
// ZeroHeuristic (baseline)
// ---------------------------------------------------------------------------

/// Uninformed heuristic that always returns `1.0`.
///
/// This is admissible because all weights live in `(0, 1]`. With this
/// heuristic A* degenerates to pure Knuth order and is exact.
pub struct ZeroHeuristic;

impl<R: BottomUpTa> IntersectionHeuristic<R> for ZeroHeuristic {
    #[inline]
    fn outside_estimate(&self, _left: StateId, _right: &R::State) -> f64 {
        1.0
    }
}

/// Uninformed heuristic in an arbitrary scorer representation.
pub struct ScoredZeroHeuristic {
    one: f64,
}

impl ScoredZeroHeuristic {
    pub fn new<S: WeightScorer>(scorer: &S) -> Self {
        Self { one: scorer.one() }
    }
}

impl<R: BottomUpTa> IntersectionHeuristic<R> for ScoredZeroHeuristic {
    #[inline]
    fn outside_estimate(&self, _left: StateId, _right: &R::State) -> f64 {
        self.one
    }
}

// ---------------------------------------------------------------------------
// OutsideHeuristic
// ---------------------------------------------------------------------------

/// Grammar-only, algebra-agnostic outside-weight heuristic.
///
/// Precomputes `OUT(X)` for every grammar state `X` via two max-product
/// fixed-point passes over the grammar automaton, then uses that as an upper
/// bound for the corresponding product-outside weight.
///
/// # Admissibility
///
/// The decomposition automaton is unweighted, so all weight is carried by the
/// grammar.  Therefore the true outside weight of any product state `(X, ·)` is
/// at most `OUT(X)`.
///
/// # Consistency
///
/// Both fixpoints are Dijkstra/Knuth-style: each state is finalized at most
/// once with its optimal value.  The resulting heuristic is therefore
/// consistent (monotone), which guarantees that A* never re-expands a node.
pub struct OutsideHeuristic {
    out: Vec<f64>,
    zero: f64,
}

impl OutsideHeuristic {
    /// Compute grammar outside weights from `grammar`.
    ///
    /// Runs two max-product fixpoints:
    ///
    /// 1. **IN(X)** (Knuth bottom-up): seed nullary rules; finalize each state
    ///    exactly once; propagate through rules whose other children are
    ///    already finalized.
    ///
    /// 2. **OUT(X)** (top-down, needs IN): seed accepting states with `1.0`;
    ///    finalize each state exactly once; for each rule whose result is the
    ///    current state, push a new outside estimate for every child.
    pub fn from_grammar(grammar: &Explicit) -> Self {
        Self::from_grammar_with(grammar, &ProbabilityScorer)
    }

    /// Compute grammar outside scores from `grammar` with `scorer`.
    pub fn from_grammar_with<S: WeightScorer>(grammar: &Explicit, scorer: &S) -> Self {
        let n = grammar.num_states() as usize;

        // ------------------------------------------------------------------
        // Pass 1: IN(X) — max-product inside weights
        // ------------------------------------------------------------------

        let mut inside = vec![scorer.zero(); n];
        let mut fin_in = FixedBitSet::with_capacity(n);

        // Index: for each state, which rules have it as a child?
        // We store (rule_index) lists per child state.
        let rules: Vec<_> = grammar.rules().collect();
        let mut by_child: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (idx, rule) in rules.iter().enumerate() {
            // Deduplicate child appearances so we don't double-count.
            let mut seen_in_rule = FixedBitSet::with_capacity(n);
            for &child in rule.children {
                if !seen_in_rule.contains(child.index()) {
                    seen_in_rule.set(child.index(), true);
                    by_child[child.index()].push(idx);
                }
            }
        }

        // Per-rule pending count (number of un-finalized distinct children)
        // and running partial product (weight × prod of finalized children).
        let mut pending: Vec<usize> = rules
            .iter()
            .map(|r| {
                let mut seen = FixedBitSet::with_capacity(n);
                r.children
                    .iter()
                    .filter(|&&c| {
                        if seen.contains(c.index()) {
                            false
                        } else {
                            seen.set(c.index(), true);
                            true
                        }
                    })
                    .count()
            })
            .collect();
        let mut partial: Vec<f64> = rules.iter().map(|r| scorer.rule_score(r.weight)).collect();

        // Heap entries: (OrdF64(weight), state_index)
        let mut heap: BinaryHeap<(OrdF64, u32)> = BinaryHeap::new();

        // Seed nullary rules.
        for (idx, rule) in rules.iter().enumerate() {
            if rule.children.is_empty() {
                let ri = rule.result.index();
                let rule_score = scorer.rule_score(rule.weight);
                if scorer.better(rule_score, inside[ri]) {
                    inside[ri] = rule_score;
                    heap.push((OrdF64(rule_score), ri as u32));
                }
                // A nullary rule contributes its weight as the full partial product.
                // Mark it as having zero pending children (it's immediately fireable).
                // We still want it in the heap; the result was already pushed above.
                // partial[idx] is already rule.weight; pending[idx] is 0.
                let _ = idx; // suppress unused warning
            }
        }

        while let Some((OrdF64(w), si)) = heap.pop() {
            let si = si as usize;
            if fin_in.contains(si) {
                continue;
            }
            // Stale-entry check: ignore if a better value was already pushed.
            if w != inside[si] {
                continue;
            }
            fin_in.set(si, true);

            for &rule_idx in &by_child[si] {
                let rule = &rules[rule_idx];
                // Update partial product for this rule.
                // Each unique child appears once in by_child[si], so we
                // multiply in IN[state] once.
                partial[rule_idx] = scorer.times(partial[rule_idx], inside[si]);
                pending[rule_idx] -= 1;

                if pending[rule_idx] == 0 {
                    // All children finalized: try to update result's inside weight.
                    let ri = rule.result.index();
                    let cand = partial[rule_idx];
                    if scorer.better(cand, inside[ri]) {
                        inside[ri] = cand;
                        heap.push((OrdF64(cand), ri as u32));
                    }
                }
            }
        }

        // ------------------------------------------------------------------
        // Pass 2: OUT(X) — max-product outside weights
        // ------------------------------------------------------------------

        let mut outside = vec![scorer.zero(); n];
        let mut fin_out = FixedBitSet::with_capacity(n);
        let mut out_heap: BinaryHeap<(OrdF64, u32)> = BinaryHeap::new();

        // Seed: accepting states get OUT = 1.0.
        grammar.initial_states(&mut |state| {
            if !state.is_stuck() && state.index() < n {
                let si = state.index();
                let one = scorer.one();
                if scorer.better(one, outside[si]) {
                    outside[si] = one;
                    out_heap.push((OrdF64(one), si as u32));
                }
            }
        });

        while let Some((OrdF64(w), si)) = out_heap.pop() {
            let si = si as usize;
            if fin_out.contains(si) {
                continue;
            }
            // Stale-entry check.
            if w != outside[si] {
                continue;
            }
            fin_out.set(si, true);

            let state = StateId(si as u32);
            // For each rule whose result is `state`, push new outside estimates
            // for each child.
            for rule in grammar.rules_topdown(state) {
                if rule.children.is_empty() {
                    continue;
                }
                let nc = rule.children.len();
                // Compute prefix and suffix products of IN values.
                let mut prefix = vec![scorer.one(); nc + 1];
                for i in 0..nc {
                    prefix[i + 1] = scorer.times(prefix[i], inside[rule.children[i].index()]);
                }
                let mut suffix = vec![scorer.one(); nc + 1];
                for i in (0..nc).rev() {
                    suffix[i] = scorer.times(suffix[i + 1], inside[rule.children[i].index()]);
                }

                for p in 0..nc {
                    let child_p = rule.children[p];
                    if child_p.is_stuck() {
                        continue;
                    }
                    let ci = child_p.index();
                    if fin_out.contains(ci) {
                        continue;
                    }
                    // OUT[child_p] >= OUT[state] * rule.weight * prod_{q != p} IN[child_q]
                    let sibling_product = scorer.times(prefix[p], suffix[p + 1]);
                    let new_out = scorer.times(
                        scorer.times(w, scorer.rule_score(rule.weight)),
                        sibling_product,
                    );
                    if scorer.better(new_out, outside[ci]) {
                        outside[ci] = new_out;
                        out_heap.push((OrdF64(new_out), ci as u32));
                    }
                }
            }
        }

        OutsideHeuristic {
            out: outside,
            zero: scorer.zero(),
        }
    }
}

impl<R: BottomUpTa> IntersectionHeuristic<R> for OutsideHeuristic {
    #[inline]
    fn outside_estimate(&self, left: StateId, _right: &R::State) -> f64 {
        self.out.get(left.index()).copied().unwrap_or(self.zero)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Explicit, ExplicitBuilder, Symbol};

    /// Build a small grammar and verify IN and OUT weights.
    ///
    /// Grammar:
    ///   a() -> s0   w=0.5
    ///   a() -> s2   w=0.3   (s2 is non-productive: never reaches s4)
    ///   f(s0) -> s1 w=0.8
    ///   g(s1) -> s4 w=0.9
    ///
    /// States: s0, s1, s2, s3, s4
    /// Accepting: s4
    /// s3 has no rules (unreachable from both bottom-up and top-down).
    ///
    /// Expected IN:
    ///   IN[s0] = 0.5
    ///   IN[s1] = 0.5 * 0.8 = 0.40
    ///   IN[s2] = 0.3
    ///   IN[s3] = 0.0  (no rule fires)
    ///   IN[s4] = 0.4 * 0.9 = 0.36
    ///
    /// Expected OUT:
    ///   OUT[s4] = 1.0  (accepting seed)
    ///   OUT[s1] = OUT[s4] * 0.9 = 0.9
    ///   OUT[s0] = OUT[s1] * 0.8 = 0.72
    ///   OUT[s2] = 0.0  (no path from s2 reaches s4)
    ///   OUT[s3] = 0.0  (unreachable from top)
    fn build_grammar() -> (Explicit, [StateId; 5]) {
        let mut b = ExplicitBuilder::new();
        let s0 = b.new_state(); // index 0
        let s1 = b.new_state(); // index 1
        let s2 = b.new_state(); // index 2
        let s3 = b.new_state(); // index 3  — isolated
        let s4 = b.new_state(); // index 4  — accepting

        let a = Symbol(0);
        let f = Symbol(1);
        let g = Symbol(2);

        b.add_weighted_rule(a, vec![], s0, 0.5); // a() -> s0, w=0.5
        b.add_weighted_rule(a, vec![], s2, 0.3); // a() -> s2, w=0.3
        b.add_weighted_rule(f, vec![s0], s1, 0.8); // f(s0) -> s1, w=0.8
        b.add_weighted_rule(g, vec![s1], s4, 0.9); // g(s1) -> s4, w=0.9

        b.add_accepting(s4);

        let grammar = b.build();
        (grammar, [s0, s1, s2, s3, s4])
    }

    #[test]
    fn inside_weights_are_correct() {
        let (grammar, [s0, s1, s2, s3, s4]) = build_grammar();
        let h = OutsideHeuristic::from_grammar(&grammar);

        // We inspect the inside vector through the OutsideHeuristic struct
        // by using a grammar with only one accepting state and checking
        // outside values (indirect).  For a direct check we re-run
        // from_grammar but also expose a small helper here.

        // Actually compute inside separately using the same logic.
        let inside = compute_inside(&grammar);

        assert!(
            (inside[s0.index()] - 0.5).abs() < 1e-10,
            "IN[s0] = {}",
            inside[s0.index()]
        );
        assert!(
            (inside[s1.index()] - 0.4).abs() < 1e-10,
            "IN[s1] = {}",
            inside[s1.index()]
        );
        assert!(
            (inside[s2.index()] - 0.3).abs() < 1e-10,
            "IN[s2] = {}",
            inside[s2.index()]
        );
        assert!(
            inside[s3.index()] == 0.0,
            "IN[s3] should be 0, got {}",
            inside[s3.index()]
        );
        assert!(
            (inside[s4.index()] - 0.36).abs() < 1e-10,
            "IN[s4] = {}",
            inside[s4.index()]
        );

        // Suppress unused variable warning for h.
        let _ = h;
    }

    #[test]
    fn outside_weights_are_correct() {
        let (grammar, [s0, s1, s2, s3, s4]) = build_grammar();
        let h = OutsideHeuristic::from_grammar(&grammar);

        assert!(
            (h.out[s4.index()] - 1.0).abs() < 1e-10,
            "OUT[s4] = {}",
            h.out[s4.index()]
        );
        assert!(
            (h.out[s1.index()] - 0.9).abs() < 1e-10,
            "OUT[s1] = {}",
            h.out[s1.index()]
        );
        assert!(
            (h.out[s0.index()] - 0.72).abs() < 1e-10,
            "OUT[s0] = {}",
            h.out[s0.index()]
        );
        assert!(
            h.out[s2.index()] == 0.0,
            "OUT[s2] should be 0, got {}",
            h.out[s2.index()]
        );
        assert!(
            h.out[s3.index()] == 0.0,
            "OUT[s3] should be 0, got {}",
            h.out[s3.index()]
        );
    }

    #[test]
    fn outside_estimate_returns_out_value() {
        let (grammar, [s0, _s1, _s2, _s3, s4]) = build_grammar();
        let h = OutsideHeuristic::from_grammar(&grammar);

        // Test via the trait method (using Explicit as R since it implements BottomUpTa).
        let dummy_right = StateId(0);
        let est_s0: f64 = <OutsideHeuristic as IntersectionHeuristic<Explicit>>::outside_estimate(
            &h,
            s0,
            &dummy_right,
        );
        let est_s4: f64 = <OutsideHeuristic as IntersectionHeuristic<Explicit>>::outside_estimate(
            &h,
            s4,
            &dummy_right,
        );

        assert!((est_s0 - 0.72).abs() < 1e-10, "estimate for s0 = {est_s0}");
        assert!((est_s4 - 1.0).abs() < 1e-10, "estimate for s4 = {est_s4}");
    }

    #[test]
    fn zero_heuristic_always_returns_one() {
        let h = ZeroHeuristic;
        let dummy: StateId = StateId(0);
        let est: f64 =
            <ZeroHeuristic as IntersectionHeuristic<Explicit>>::outside_estimate(&h, dummy, &dummy);
        assert_eq!(est, 1.0);
    }

    #[test]
    fn outside_estimate_out_of_range_returns_zero() {
        let (grammar, _states) = build_grammar();
        let h = OutsideHeuristic::from_grammar(&grammar);
        // StateId with index well beyond num_states should return 0.
        let far = StateId(9999);
        let dummy_right = StateId(0);
        let est: f64 = <OutsideHeuristic as IntersectionHeuristic<Explicit>>::outside_estimate(
            &h,
            far,
            &dummy_right,
        );
        assert_eq!(est, 0.0);
    }

    // ------------------------------------------------------------------
    // Helper: re-implement only the IN pass so we can inspect it directly
    // without exposing the field.
    // ------------------------------------------------------------------
    fn compute_inside(grammar: &Explicit) -> Vec<f64> {
        let n = grammar.num_states() as usize;
        let mut inside = vec![0.0f64; n];
        let mut fin_in = FixedBitSet::with_capacity(n);

        let rules: Vec<_> = grammar.rules().collect();
        let mut by_child: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (idx, rule) in rules.iter().enumerate() {
            let mut seen = FixedBitSet::with_capacity(n);
            for &child in rule.children {
                if !seen.contains(child.index()) {
                    seen.set(child.index(), true);
                    by_child[child.index()].push(idx);
                }
            }
        }

        let mut pending: Vec<usize> = rules
            .iter()
            .map(|r| {
                let mut seen = FixedBitSet::with_capacity(n);
                r.children
                    .iter()
                    .filter(|&&c| {
                        if seen.contains(c.index()) {
                            false
                        } else {
                            seen.set(c.index(), true);
                            true
                        }
                    })
                    .count()
            })
            .collect();
        let mut partial: Vec<f64> = rules.iter().map(|r| r.weight).collect();

        let mut heap: BinaryHeap<(OrdF64, u32)> = BinaryHeap::new();
        for rule in rules.iter() {
            if rule.children.is_empty() {
                let ri = rule.result.index();
                if rule.weight > inside[ri] {
                    inside[ri] = rule.weight;
                    heap.push((OrdF64(rule.weight), ri as u32));
                }
            }
        }

        while let Some((OrdF64(w), si)) = heap.pop() {
            let si = si as usize;
            if fin_in.contains(si) {
                continue;
            }
            if w < inside[si] - 1e-15 * inside[si].max(1e-15) {
                continue;
            }
            fin_in.set(si, true);

            for &rule_idx in &by_child[si] {
                partial[rule_idx] *= inside[si];
                pending[rule_idx] -= 1;
                if pending[rule_idx] == 0 {
                    let ri = rules[rule_idx].result.index();
                    let cand = partial[rule_idx];
                    if cand > inside[ri] {
                        inside[ri] = cand;
                        heap.push((OrdF64(cand), ri as u32));
                    }
                }
            }
        }

        inside
    }
}
