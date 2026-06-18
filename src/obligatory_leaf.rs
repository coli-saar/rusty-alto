//! Obligatory-leaf suffix filter — the **F** heuristic (Klein & Manning 2003,
//! adapted to the automaton-intersection setting; see `docs/f-heuristic-design.md`).
//!
//! An active constituent `(X, span)` is hopeless if the grammar *forces* `X`'s
//! completions to emit terminals strictly left/right of `span` that the actual
//! input cannot supply there. We precompute, per grammar state `X`, the
//! multisets of leaves every completion must emit on each side (`req_left`,
//! `req_right`); per input we count the available terminal supply on each side
//! of a span; and we prune (`outside_estimate = scorer.zero()`) when an
//! obligation exceeds the supply. This is admissible — we zero only when an
//! obligatory leaf is genuinely unavailable (true outside weight = 0) — and is
//! meant to be combined with the SX heuristic via [`crate::MinHeuristic`].
//!
//! This module is self-contained: it walks the homomorphism frontier directly
//! (capturing each leaf `Symbol`) rather than extending the SX builder's
//! `YieldToken`, so the pure SX path is untouched.

use crate::homomorphism::{HomLabel, Homomorphism};
use crate::score::WeightScorer;
use crate::{
    Explicit, FxHashMap, IntersectionHeuristic, Span, StateId, StringDecompositionAutomaton,
    Symbol, TopDownTa,
};
use crate::combinators::InvHom;
use rusty_tree::tree::{Tree, TreeArena};
use std::collections::BTreeMap;

/// Build-time sparse leaf multiset: leaf-symbol id -> count.
type Bag = BTreeMap<u32, u32>;
/// Frozen obligation: sorted `(leaf-symbol id, count)` pairs (small; median 1).
type ReqList = Box<[(u32, u32)]>;

#[derive(Clone, Debug)]
enum Tok {
    Word(u32),
    Child(usize),
}

struct FlatRule {
    result: usize,
    tokens: Vec<Tok>,
}

fn frontier(arena: &TreeArena<HomLabel>, node: Tree, children: &[StateId], out: &mut Vec<Tok>) {
    match *arena.get_label(node) {
        HomLabel::Var(i) => {
            if let Some(c) = children.get(i) {
                out.push(Tok::Child(c.index()));
            }
        }
        HomLabel::Symbol(s) => {
            let kids = arena.get_children(node);
            if kids.is_empty() {
                out.push(Tok::Word(s.0));
            } else {
                for &k in kids {
                    frontier(arena, k, children, out);
                }
            }
        }
    }
}

fn bag_add(acc: &mut Bag, other: &Bag) {
    for (&k, &v) in other {
        *acc.entry(k).or_insert(0) += v;
    }
}

/// Per-key min; drops keys whose min is 0 (= absent from one side).
fn bag_min(a: &Bag, b: &Bag) -> Bag {
    let mut out = Bag::new();
    for (&k, &av) in a {
        if let Some(&bv) = b.get(&k) {
            let m = av.min(bv);
            if m > 0 {
                out.insert(k, m);
            }
        }
    }
    out
}

fn meet_update(slot: &mut Option<Bag>, cand: Bag, changed: &mut bool) {
    let new = match slot.as_ref() {
        None => cand,
        Some(cur) => bag_min(cur, &cand),
    };
    if slot.as_ref() != Some(&new) {
        *slot = Some(new);
        *changed = true;
    }
}

fn freeze(slot: &Option<Bag>) -> Option<ReqList> {
    slot.as_ref()
        .map(|b| b.iter().map(|(&k, &v)| (k, v)).collect())
}

/// Grammar-only obligatory-leaf tables (`req_left`, `req_right`), cached per
/// grammar and reused across inputs. Build with [`ObligatoryLeafTables::from_grammar`].
pub struct ObligatoryLeafTables {
    /// `req_left[X]`: leaves every completion of `X` must emit left of its span.
    /// `None` = non-productive / root-unreachable (never an A* item; treated as
    /// no obligation).
    req_left: Vec<Option<ReqList>>,
    req_right: Vec<Option<ReqList>>,
}

impl ObligatoryLeafTables {
    /// Compute the obligatory-leaf tables from a grammar and its string
    /// homomorphism. Grammar-only and cheap (same fixpoint shape as `minwidth`).
    pub fn from_grammar(grammar: &Explicit, hom: &Homomorphism) -> Self {
        let num_states = grammar.num_states() as usize;
        let arena = hom.arena();

        // --- Phase A: flatten rules (mirrors how SX filters stuck children). ---
        let mut flat_rules: Vec<FlatRule> = Vec::new();
        for rule in grammar.rules() {
            let Some(term) = hom.get(rule.symbol) else {
                continue;
            };
            if rule
                .children
                .iter()
                .any(|c| c.is_stuck() || c.index() >= num_states)
                || rule.result.is_stuck()
                || rule.result.index() >= num_states
            {
                continue;
            }
            let mut tokens = Vec::new();
            frontier(arena, term, rule.children, &mut tokens);
            flat_rules.push(FlatRule {
                result: rule.result.index(),
                tokens,
            });
        }
        let mut accepting = Vec::new();
        grammar.initial_states(&mut |s: StateId| {
            if !s.is_stuck() && s.index() < num_states {
                accepting.push(s.index());
            }
        });

        // --- Phase B: mic (obligatory INSIDE leaves), MEET over a state's rules. ---
        let mut mic: Vec<Option<Bag>> = vec![None; num_states];
        loop {
            let mut changed = false;
            for r in &flat_rules {
                let mut acc = Bag::new();
                let mut feasible = true;
                for tok in &r.tokens {
                    match tok {
                        Tok::Word(s) => {
                            *acc.entry(*s).or_insert(0) += 1;
                        }
                        Tok::Child(c) => match &mic[*c] {
                            Some(m) => bag_add(&mut acc, m),
                            None => {
                                feasible = false;
                                break;
                            }
                        },
                    }
                }
                if feasible {
                    meet_update(&mut mic[r.result], acc, &mut changed);
                }
            }
            if !changed {
                break;
            }
        }

        // Only rules whose every child is productive can occur in a finite parse.
        let productive: Vec<&FlatRule> = flat_rules
            .iter()
            .filter(|r| {
                r.tokens.iter().all(|t| match t {
                    Tok::Child(c) => mic[*c].is_some(),
                    _ => true,
                })
            })
            .collect();

        // --- Phase C: req_left / req_right (obligatory OUTSIDE leaves). ---
        let mut req_left: Vec<Option<Bag>> = vec![None; num_states];
        let mut req_right: Vec<Option<Bag>> = vec![None; num_states];
        for &a in &accepting {
            req_left[a] = Some(Bag::new());
            req_right[a] = Some(Bag::new());
        }
        loop {
            let mut changed = false;
            for r in &productive {
                for (pos, tok) in r.tokens.iter().enumerate() {
                    let x = match tok {
                        Tok::Child(c) => *c,
                        _ => continue,
                    };
                    let mut left = Bag::new();
                    let mut right = Bag::new();
                    for (q, t2) in r.tokens.iter().enumerate() {
                        if q == pos {
                            continue;
                        }
                        let side = if q < pos { &mut left } else { &mut right };
                        match t2 {
                            Tok::Word(s) => {
                                *side.entry(*s).or_insert(0) += 1;
                            }
                            Tok::Child(c) => bag_add(side, mic[*c].as_ref().unwrap()),
                        }
                    }
                    if let Some(pr) = req_right[r.result].clone() {
                        let mut cand = pr;
                        bag_add(&mut cand, &right);
                        meet_update(&mut req_right[x], cand, &mut changed);
                    }
                    if let Some(pl) = req_left[r.result].clone() {
                        let mut cand = pl;
                        bag_add(&mut cand, &left);
                        meet_update(&mut req_left[x], cand, &mut changed);
                    }
                }
            }
            if !changed {
                break;
            }
        }

        ObligatoryLeafTables {
            req_left: req_left.iter().map(freeze).collect(),
            req_right: req_right.iter().map(freeze).collect(),
        }
    }

    /// Build a per-sentence F heuristic. `scorer` fixes the `pass` / `prune`
    /// values (`one()` / `zero()`) so the estimate lives in the same score
    /// space as the SX heuristic it is `min`-combined with.
    pub fn for_sentence<'a, S: WeightScorer>(
        &'a self,
        sentence: &[Symbol],
        scorer: &S,
    ) -> ObligatoryLeafHeuristic<'a> {
        // Sorted positions per terminal: count in a prefix/suffix via partition_point.
        let mut positions: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        for (i, sym) in sentence.iter().enumerate() {
            positions.entry(sym.0).or_default().push(i as u32);
        }
        ObligatoryLeafHeuristic {
            tables: self,
            positions,
            pass: scorer.one(),
            prune: scorer.zero(),
        }
    }
}

/// Per-input F heuristic: an [`ObligatoryLeafTables`] bound to one sentence's
/// terminal supply. Cheap to build (one pass over the sentence).
pub struct ObligatoryLeafHeuristic<'a> {
    tables: &'a ObligatoryLeafTables,
    positions: FxHashMap<u32, Vec<u32>>,
    pass: f64,
    prune: f64,
}

impl ObligatoryLeafHeuristic<'_> {
    /// Occurrences of terminal `t` strictly left of position `start`.
    #[inline]
    fn supply_left(&self, t: u32, start: usize) -> usize {
        self.positions
            .get(&t)
            .map_or(0, |p| p.partition_point(|&q| (q as usize) < start))
    }

    /// Occurrences of terminal `t` at or right of position `end`.
    #[inline]
    fn supply_right(&self, t: u32, end: usize) -> usize {
        self.positions
            .get(&t)
            .map_or(0, |p| p.len() - p.partition_point(|&q| (q as usize) < end))
    }

    /// `true` iff the grammar forces `left`'s completion to emit an obligatory
    /// leaf that the input cannot supply on the required side of `span` — i.e.
    /// the item has zero outside weight and is hopeless. This is the sound test
    /// shared by [`Self::estimate`] (priority) and `admits` (construction-time
    /// filter).
    #[inline]
    fn prunes(&self, left: StateId, span: &Span) -> bool {
        let idx = left.index();
        if let Some(Some(req)) = self.tables.req_left.get(idx).map(|o| o.as_deref()) {
            for &(t, need) in req {
                if self.supply_left(t, span.start) < need as usize {
                    return true;
                }
            }
        }
        if let Some(Some(req)) = self.tables.req_right.get(idx).map(|o| o.as_deref()) {
            for &(t, need) in req {
                if self.supply_right(t, span.end) < need as usize {
                    return true;
                }
            }
        }
        false
    }

    #[inline]
    fn estimate(&self, left: StateId, span: &Span) -> f64 {
        if self.prunes(left, span) {
            self.prune
        } else {
            self.pass
        }
    }
}

impl IntersectionHeuristic<StringDecompositionAutomaton> for ObligatoryLeafHeuristic<'_> {
    #[inline]
    fn outside_estimate(&self, left: StateId, span: &Span) -> f64 {
        self.estimate(left, span)
    }

    #[inline]
    fn admits(&self, left: StateId, span: &Span) -> bool {
        !self.prunes(left, span)
    }

    #[inline]
    fn estimate_if_admitted(&self, left: StateId, span: &Span) -> Option<f64> {
        (!self.prunes(left, span)).then_some(self.pass)
    }
}

impl IntersectionHeuristic<InvHom<'_, StringDecompositionAutomaton>>
    for ObligatoryLeafHeuristic<'_>
{
    #[inline]
    fn outside_estimate(&self, left: StateId, span: &Span) -> f64 {
        // InvHom<StringDecompositionAutomaton>::State = Span.
        self.estimate(left, span)
    }

    #[inline]
    fn admits(&self, left: StateId, span: &Span) -> bool {
        !self.prunes(left, span)
    }

    #[inline]
    fn estimate_if_admitted(&self, left: StateId, span: &Span) -> Option<f64> {
        (!self.prunes(left, span)).then_some(self.pass)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, LogProbabilityScorer, ProbabilityScorer};

    /// Build the Step-1 worked-example grammar + homomorphism through the real
    /// public APIs, then derive the obligatory-leaf tables via `from_grammar`.
    ///
    ///   states S=0, A=1, B=2 ; grammar symbols rS=0, rA=1, rB=2, rA2=3 ;
    ///   word leaves x=10, y=11, z=12 ; concat=99.
    ///   S -> *(A, B) ;  A -> "x" ;  B -> "y" ;  A -> "z"
    fn worked_example() -> (ObligatoryLeafTables, StateId, StateId, StateId) {
        let mut b = ExplicitBuilder::new();
        let s = b.new_state();
        let a = b.new_state();
        let bb = b.new_state();
        b.add_rule(Symbol(0), vec![a, bb], s);
        b.add_rule(Symbol(1), vec![], a);
        b.add_rule(Symbol(2), vec![], bb);
        b.add_rule(Symbol(3), vec![], a);
        b.add_accepting(s);
        let grammar = b.build();

        let mut hom = Homomorphism::new();
        let v0 = hom.add_var(0);
        let v1 = hom.add_var(1);
        let root = hom.add_symbol(Symbol(99), vec![v0, v1]);
        hom.add(Symbol(0), 2, root).unwrap();
        for (gsym, word) in [(1u32, 10u32), (2, 11), (3, 12)] {
            let leaf = hom.add_symbol(Symbol(word), vec![]);
            hom.add(Symbol(gsym), 0, leaf).unwrap();
        }

        let tables = ObligatoryLeafTables::from_grammar(&grammar, &hom);
        (tables, s, a, bb)
    }

    #[test]
    fn from_grammar_matches_worked_example() {
        let (tables, s, a, bb) = worked_example();
        // A always has a `y` (11) to its right; nothing forced to its left.
        assert_eq!(tables.req_right[a.index()].as_deref(), Some(&[(11u32, 1u32)][..]));
        assert_eq!(tables.req_left[a.index()].as_deref(), Some(&[][..]));
        // A forces nothing, so B's sides are empty; root has empty obligations.
        assert_eq!(tables.req_left[bb.index()].as_deref(), Some(&[][..]));
        assert_eq!(tables.req_right[bb.index()].as_deref(), Some(&[][..]));
        assert_eq!(tables.req_left[s.index()].as_deref(), Some(&[][..]));
        assert_eq!(tables.req_right[s.index()].as_deref(), Some(&[][..]));
    }

    #[test]
    fn prunes_when_required_leaf_missing_on_side() {
        let (tables, _s, a, _b) = worked_example();
        // sentence "x y" = [10, 11], log space (pass = one() = 0.0).
        let h = tables.for_sentence(&[Symbol(10), Symbol(11)], &LogProbabilityScorer);

        // A over [0,1): a `y` lies to its right -> pass.
        assert_eq!(
            IntersectionHeuristic::<StringDecompositionAutomaton>::outside_estimate(
                &h, a, &Span::new(0, 1)
            ),
            0.0
        );
        // A over [0,2): nothing to its right -> the required `y` is gone -> prune.
        assert_eq!(
            IntersectionHeuristic::<StringDecompositionAutomaton>::outside_estimate(
                &h, a, &Span::new(0, 2)
            ),
            f64::NEG_INFINITY
        );
    }

    #[test]
    fn admits_is_complement_of_prune() {
        let (tables, _s, a, _b) = worked_example();
        let h = tables.for_sentence(&[Symbol(10), Symbol(11)], &LogProbabilityScorer);
        // `admits` must agree with the priority sentinel: admit iff not pruned.
        for span in [Span::new(0, 1), Span::new(0, 2), Span::new(1, 2)] {
            let est = IntersectionHeuristic::<StringDecompositionAutomaton>::outside_estimate(
                &h, a, &span,
            );
            let admitted =
                IntersectionHeuristic::<StringDecompositionAutomaton>::admits(&h, a, &span);
            assert_eq!(admitted, est != f64::NEG_INFINITY, "span {span:?}");
        }
        // A over [0,1): `y` lies right -> admitted; over [0,2): gone -> rejected.
        assert!(IntersectionHeuristic::<StringDecompositionAutomaton>::admits(
            &h,
            a,
            &Span::new(0, 1)
        ));
        assert!(!IntersectionHeuristic::<StringDecompositionAutomaton>::admits(
            &h,
            a,
            &Span::new(0, 2)
        ));
    }

    #[test]
    fn pass_prune_track_the_scorer() {
        let (tables, _s, a, _b) = worked_example();
        // Probability space: pass = one() = 1.0, prune = zero() = 0.0.
        let h = tables.for_sentence(&[Symbol(10), Symbol(11)], &ProbabilityScorer);
        assert_eq!(
            IntersectionHeuristic::<StringDecompositionAutomaton>::outside_estimate(
                &h, a, &Span::new(0, 1)
            ),
            1.0
        );
        assert_eq!(
            IntersectionHeuristic::<StringDecompositionAutomaton>::outside_estimate(
                &h, a, &Span::new(0, 2)
            ),
            0.0
        );
    }
}
