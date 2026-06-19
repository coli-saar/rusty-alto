//! One-best Viterbi extraction for explicit weighted tree automata.

use crate::{Explicit, ProbabilityScorer, StateId, Symbol, TopDownTa, WeightScorer};
use rusty_tree::tree::{Tree, TreeArena};
use smallvec::SmallVec;

/// The highest-weighted tree found in an automaton language.
#[derive(Debug)]
pub struct ViterbiTree {
    arena: TreeArena<Symbol>,
    root: Tree,
    weight: f64,
    score: f64,
}

impl ViterbiTree {
    /// Construct a `ViterbiTree` with an algorithm score and display weight.
    pub(crate) fn new_with_score(
        arena: TreeArena<Symbol>,
        root: Tree,
        score: f64,
        weight: f64,
    ) -> Self {
        Self {
            arena,
            root,
            weight,
            score,
        }
    }

    /// Return the arena containing the tree.
    pub fn arena(&self) -> &TreeArena<Symbol> {
        &self.arena
    }

    /// Return the root handle in [`Self::arena`].
    pub fn root(&self) -> Tree {
        self.root
    }

    /// Return the product of rule weights for this tree.
    pub fn weight(&self) -> f64 {
        self.weight
    }

    /// Return the score used to rank this tree.
    ///
    /// For [`Explicit::viterbi`] this equals [`Self::weight`]. For
    /// [`Explicit::viterbi_with`] it is in the scorer's representation, e.g. a
    /// log probability when using [`crate::LogProbabilityScorer`].
    pub fn score(&self) -> f64 {
        self.score
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Backpointer {
    pub(crate) symbol: Symbol,
    pub(crate) children: SmallVec<[StateId; 2]>,
    pub(crate) weight: f64,
}

impl Explicit {
    /// Compute the highest-weighted accepted tree.
    ///
    /// This is a direct one-best dynamic program for acyclic parse charts. It
    /// deliberately avoids the k-best sorted-language machinery when callers
    /// only need the best derivation. Cyclic dependencies on the active DFS
    /// path are ignored: for PCFG-style rule weights below one, traversing a
    /// cycle cannot improve a finite derivation. Direct self-loops are skipped
    /// for the same reason, matching Alto's convention.
    pub fn viterbi(&self) -> Option<ViterbiTree> {
        self.viterbi_with(&ProbabilityScorer)
    }

    /// Compute the highest-scoring accepted tree under `scorer`.
    pub fn viterbi_with<S: WeightScorer>(&self, scorer: &S) -> Option<ViterbiTree> {
        let mut marks = vec![0u8; self.num_states() as usize];
        let mut best = vec![None::<Backpointer>; self.num_states() as usize];
        let mut stack = Vec::new();
        self.initial_states(&mut |state| {
            visit_and_score(self, state, scorer, &mut marks, &mut best, &mut stack);
        });
        finish_best(self, scorer, &best)
    }

    /// Previous Viterbi implementation, retained only for performance comparisons.
    #[cfg(feature = "viterbi-benchmark")]
    #[doc(hidden)]
    pub fn viterbi_old_benchmark(&self) -> Option<ViterbiTree> {
        let scorer = ProbabilityScorer;
        let mut order = Vec::new();
        let mut marks = vec![0u8; self.num_states() as usize];
        self.initial_states(&mut |state| visit_state_fast(self, state, &mut marks, &mut order));

        let mut best = vec![None::<Backpointer>; self.num_states() as usize];
        for state in order {
            best[state.index()] = score_state(self, state, &scorer, &best);
        }
        finish_best(self, &scorer, &best)
    }
}

fn visit_and_score<S: WeightScorer>(
    auto: &Explicit,
    start: StateId,
    scorer: &S,
    marks: &mut [u8],
    best: &mut [Option<Backpointer>],
    stack: &mut Vec<usize>,
) {
    if start.is_stuck() || start.index() >= marks.len() || marks[start.index()] != 0 {
        return;
    }

    stack.clear();
    stack.push(start.index() << 1);

    while let Some(frame) = stack.pop() {
        let state = StateId((frame >> 1) as u32);
        if frame & 1 != 0 {
            best[state.index()] = score_state(auto, state, scorer, best);
            marks[state.index()] = 2;
            continue;
        }
        if marks[state.index()] != 0 {
            continue;
        }

        marks[state.index()] = 1;
        stack.push((state.index() << 1) | 1);
        for &rule_idx in auto.rule_indexes_topdown(state).iter().rev() {
            let rule = auto.rule(rule_idx);
            if rule.children.contains(&state) {
                continue;
            }
            for &child in rule.children.iter().rev() {
                if !child.is_stuck() && child.index() < marks.len() && marks[child.index()] == 0 {
                    stack.push(child.index() << 1);
                }
            }
        }
    }
}

#[cfg(feature = "viterbi-benchmark")]
fn visit_state_fast(auto: &Explicit, start: StateId, marks: &mut [u8], order: &mut Vec<StateId>) {
    if start.is_stuck() || start.index() >= marks.len() || marks[start.index()] != 0 {
        return;
    }
    let mut stack = vec![(start, false)];
    marks[start.index()] = 1;
    while let Some((state, exiting)) = stack.pop() {
        if exiting {
            marks[state.index()] = 2;
            order.push(state);
            continue;
        }
        stack.push((state, true));
        for &rule_idx in auto.rule_indexes_topdown(state).iter().rev() {
            let rule = auto.rule(rule_idx);
            if rule.children.contains(&state) {
                continue;
            }
            for &child in rule.children.iter().rev() {
                if !child.is_stuck() && child.index() < marks.len() && marks[child.index()] == 0 {
                    marks[child.index()] = 1;
                    stack.push((child, false));
                }
            }
        }
    }
}

fn score_state<S: WeightScorer>(
    auto: &Explicit,
    state: StateId,
    scorer: &S,
    best: &[Option<Backpointer>],
) -> Option<Backpointer> {
    let mut best_here = None::<Backpointer>;
    for rule in auto.rules_topdown(state) {
        if rule.children.contains(&state) {
            continue;
        }

        let mut weight = scorer.rule_score(rule.weight);
        let mut all_children_available = true;
        for &child in rule.children {
            let Some(child_best) = best.get(child.index()).and_then(Option::as_ref) else {
                all_children_available = false;
                break;
            };
            weight = scorer.times(weight, child_best.weight);
        }
        if all_children_available
            && best_here
                .as_ref()
                .is_none_or(|old| scorer.better(weight, old.weight))
        {
            best_here = Some(Backpointer {
                symbol: rule.symbol,
                children: rule.children.iter().copied().collect(),
                weight,
            });
        }
    }
    best_here
}

fn finish_best<S: WeightScorer>(
    auto: &Explicit,
    scorer: &S,
    best: &[Option<Backpointer>],
) -> Option<ViterbiTree> {
    let mut best_final = None::<(StateId, f64)>;
    auto.initial_states(&mut |state| {
        if let Some(backpointer) = best.get(state.index()).and_then(Option::as_ref)
            && best_final
                .is_none_or(|(_, old_weight)| scorer.better(backpointer.weight, old_weight))
        {
            best_final = Some((state, backpointer.weight));
        }
    });

    let (state, score) = best_final?;
    let mut arena = TreeArena::new();
    let root = build_tree(state, best, &mut arena)?;
    Some(ViterbiTree::new_with_score(
        arena,
        root,
        score,
        scorer.score_to_weight(score),
    ))
}

pub(crate) fn build_tree(
    state: StateId,
    best: &[Option<Backpointer>],
    arena: &mut TreeArena<Symbol>,
) -> Option<Tree> {
    let backpointer = best.get(state.index())?.as_ref()?;
    let children = backpointer
        .children
        .iter()
        .map(|&child| build_tree(child, best, arena))
        .collect::<Option<Vec<_>>>()?;
    Some(arena.add_node(backpointer.symbol, children))
}

pub(crate) fn build_tree_from_arena(
    state: StateId,
    backpointer_ids: &[Option<u32>],
    backpointers: &[Backpointer],
    arena: &mut TreeArena<Symbol>,
) -> Option<Tree> {
    let id = backpointer_ids.get(state.index())?.as_ref()?;
    let backpointer = backpointers.get(*id as usize)?;
    let children = backpointer
        .children
        .iter()
        .map(|&child| build_tree_from_arena(child, backpointer_ids, backpointers, arena))
        .collect::<Option<Vec<_>>>()?;
    Some(arena.add_node(backpointer.symbol, children))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ExplicitBuilder;

    #[test]
    fn chooses_highest_weighted_tree() {
        let a = Symbol(0);
        let b = Symbol(1);
        let f = Symbol(2);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(a, vec![], qa, 0.3);
        builder.add_weighted_rule(b, vec![], qb, 0.8);
        builder.add_weighted_rule(f, vec![qa], root, 0.9);
        builder.add_weighted_rule(f, vec![qb], root, 0.4);
        builder.add_accepting(root);
        let automaton = builder.build();

        let best = automaton.viterbi().unwrap();
        assert!((best.weight() - 0.32).abs() < 1e-12);
        assert_eq!(*best.arena().get_label(best.root()), f);
        let child = best.arena().get_children(best.root())[0];
        assert_eq!(*best.arena().get_label(child), b);
    }

    #[test]
    fn returns_none_for_empty_language() {
        let mut builder = ExplicitBuilder::new();
        let root = builder.new_state();
        builder.add_accepting(root);
        let automaton = builder.build();

        assert!(automaton.viterbi().is_none());
    }

    #[test]
    fn preserves_binary_child_order() {
        let a = Symbol(0);
        let b = Symbol(1);
        let f = Symbol(2);

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(a, vec![], qa, 0.5);
        builder.add_weighted_rule(b, vec![], qb, 0.5);
        builder.add_weighted_rule(f, vec![qa, qb], root, 0.5);
        builder.add_accepting(root);
        let automaton = builder.build();

        let best = automaton.viterbi().unwrap();
        assert!((best.weight() - 0.125).abs() < 1e-12);
        let children = best.arena().get_children(best.root());
        assert_eq!(children.len(), 2);
        assert_eq!(*best.arena().get_label(children[0]), a);
        assert_eq!(*best.arena().get_label(children[1]), b);
    }

    #[test]
    fn skips_self_loop_rules_during_iterative_traversal() {
        let a = Symbol(0);
        let f = Symbol(1);

        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(a, vec![], leaf, 0.7);
        builder.add_weighted_rule(f, vec![leaf], root, 0.5);
        builder.add_weighted_rule(f, vec![root], root, 100.0);
        builder.add_accepting(root);
        let automaton = builder.build();

        let best = automaton.viterbi().unwrap();
        assert!((best.weight() - 0.35).abs() < 1e-12);
        assert_eq!(*best.arena().get_label(best.root()), f);
        let child = best.arena().get_children(best.root())[0];
        assert_eq!(*best.arena().get_label(child), a);
    }

    #[test]
    fn shared_dependency_is_scored_before_all_parents() {
        let leaf_symbol = Symbol(0);
        let unary_symbol = Symbol(1);
        let root_symbol = Symbol(2);

        let mut builder = ExplicitBuilder::new();
        let shared = builder.new_state();
        let left = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(leaf_symbol, vec![], shared, 0.8);
        builder.add_weighted_rule(unary_symbol, vec![shared], left, 0.7);
        builder.add_weighted_rule(root_symbol, vec![left, shared], root, 0.6);
        builder.add_accepting(root);
        let automaton = builder.build();

        let best = automaton.viterbi().expect("shared DAG has a derivation");
        assert!((best.weight() - 0.8 * 0.7 * 0.8 * 0.6).abs() < 1e-12);
    }

    #[test]
    fn unproductive_nontrivial_cycles_have_no_derivation() {
        let f = Symbol(0);
        let g = Symbol(1);
        let mut builder = ExplicitBuilder::new();
        let q0 = builder.new_state();
        let q1 = builder.new_state();
        builder.add_weighted_rule(f, vec![q1], q0, 0.5);
        builder.add_weighted_rule(g, vec![q0], q1, 0.5);
        builder.add_accepting(q0);
        let automaton = builder.build();

        assert!(automaton.viterbi().is_none());
    }

    #[test]
    fn productive_nontrivial_cycle_uses_acyclic_exit() {
        let leaf_symbol = Symbol(0);
        let forward = Symbol(1);
        let backward = Symbol(2);
        let mut builder = ExplicitBuilder::new();
        let q0 = builder.new_state();
        let q1 = builder.new_state();
        builder.add_weighted_rule(leaf_symbol, vec![], q1, 0.7);
        builder.add_weighted_rule(forward, vec![q1], q0, 0.8);
        builder.add_weighted_rule(backward, vec![q0], q1, 0.9);
        builder.add_accepting(q0);
        let automaton = builder.build();

        let best = automaton.viterbi().expect("cycle has a productive exit");
        assert!((best.weight() - 0.56).abs() < 1e-12);
        assert_eq!(*best.arena().get_label(best.root()), forward);
    }

    #[test]
    fn matches_sorted_language_on_shared_acyclic_automata() {
        for width in 2..8 {
            let mut builder = ExplicitBuilder::new();
            let mut states = Vec::new();
            for _ in 0..width {
                states.push(builder.new_state());
            }
            builder.add_weighted_rule(Symbol(0), vec![], states[0], 0.91);
            for i in 1..width {
                builder.add_weighted_rule(
                    Symbol((2 * i) as u32),
                    vec![states[i - 1]],
                    states[i],
                    0.8 - i as f64 * 0.01,
                );
                builder.add_weighted_rule(
                    Symbol((2 * i + 1) as u32),
                    vec![states[i - 1], states[0]],
                    states[i],
                    0.7 - i as f64 * 0.01,
                );
            }
            builder.add_accepting(states[width - 1]);
            if width > 3 {
                builder.add_accepting(states[width - 2]);
            }
            let automaton = builder.build();

            let viterbi = automaton.viterbi().unwrap();
            let sorted = automaton.sorted_language().next().unwrap();
            assert!((viterbi.weight() - sorted.weight()).abs() < 1e-12);
        }
    }

    #[test]
    fn log_scorer_keeps_underflowed_derivation_orderable() {
        let a = Symbol(0);
        let f = Symbol(1);

        let mut builder = ExplicitBuilder::new();
        let mut states = Vec::new();
        for _ in 0..220 {
            states.push(builder.new_state());
        }

        builder.add_weighted_rule(a, vec![], states[0], 0.01);
        for i in 1..states.len() {
            builder.add_weighted_rule(f, vec![states[i - 1]], states[i], 0.01);
        }
        builder.add_accepting(*states.last().unwrap());
        let automaton = builder.build();

        let best_prob = automaton.viterbi().unwrap();
        assert_eq!(best_prob.weight(), 0.0);

        let scorer = crate::LogProbabilityScorer;
        let best_log = automaton.viterbi_with(&scorer).unwrap();
        assert!(best_log.score().is_finite());
        assert_eq!(best_log.weight(), 0.0);
    }
}
