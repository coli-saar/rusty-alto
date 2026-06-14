//! One-best Viterbi extraction for explicit weighted tree automata.

use crate::{Explicit, StateId, Symbol, TopDownTa};
use rusty_tree::tree::{Tree, TreeArena};

/// The highest-weighted tree found in an automaton language.
#[derive(Debug)]
pub struct ViterbiTree {
    arena: TreeArena<Symbol>,
    root: Tree,
    weight: f64,
}

impl ViterbiTree {
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
}

#[derive(Clone, Debug)]
struct Backpointer {
    symbol: Symbol,
    children: Vec<StateId>,
    weight: f64,
}

impl Explicit {
    /// Compute the highest-weighted accepted tree.
    ///
    /// This is a direct one-best dynamic program for acyclic parse charts. It
    /// deliberately avoids the k-best sorted-language machinery when callers
    /// only need the best derivation. Self-loop rules are skipped, matching
    /// Alto's Viterbi convention for productive weighted charts.
    pub fn viterbi(&self) -> Option<ViterbiTree> {
        let mut order = Vec::new();
        let mut marks = vec![0u8; self.num_states() as usize];

        self.initial_states(&mut |state| {
            visit_state(self, state, &mut marks, &mut order);
        });

        let mut best = vec![None::<Backpointer>; self.num_states() as usize];
        for state in order {
            let mut best_here = None::<Backpointer>;

            for rule in self.rules_topdown(state) {
                if rule.children.contains(&state) {
                    continue;
                }

                let mut weight = rule.weight;
                let mut all_children_available = true;
                for &child in rule.children {
                    let Some(child_best) = best.get(child.index()).and_then(Option::as_ref) else {
                        all_children_available = false;
                        break;
                    };
                    weight *= child_best.weight;
                }
                if !all_children_available {
                    continue;
                }

                if best_here.as_ref().is_none_or(|old| weight > old.weight) {
                    best_here = Some(Backpointer {
                        symbol: rule.symbol,
                        children: rule.children.to_vec(),
                        weight,
                    });
                }
            }

            best[state.index()] = best_here;
        }

        let mut best_final = None::<(StateId, f64)>;
        self.initial_states(&mut |state| {
            if let Some(backpointer) = best.get(state.index()).and_then(Option::as_ref) {
                if best_final.is_none_or(|(_, old_weight)| backpointer.weight > old_weight) {
                    best_final = Some((state, backpointer.weight));
                }
            }
        });

        let (state, weight) = best_final?;
        let mut arena = TreeArena::new();
        let root = build_tree(state, &best, &mut arena)?;
        Some(ViterbiTree {
            arena,
            root,
            weight,
        })
    }
}

fn visit_state(auto: &Explicit, state: StateId, marks: &mut [u8], order: &mut Vec<StateId>) {
    if state.is_stuck() || state.index() >= marks.len() {
        return;
    }

    match marks[state.index()] {
        2 => return,
        1 => return,
        _ => {}
    }

    marks[state.index()] = 1;
    let child_tuples: Vec<Vec<StateId>> = auto
        .rules_topdown(state)
        .filter(|rule| !rule.children.contains(&state))
        .map(|rule| rule.children.to_vec())
        .collect();
    for children in child_tuples {
        for child in children {
            visit_state(auto, child, marks, order);
        }
    }
    marks[state.index()] = 2;
    order.push(state);
}

fn build_tree(
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
}
