//! Fast unsorted enumeration of finite explicit derivation languages.

use crate::{
    BottomUpTa, Explicit, StateId, Symbol,
    language_analysis::{LanguageAnalysis, analyze_explicit},
};
use thiserror::Error;

/// Error returned when a finite-language plan cannot be constructed.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum FiniteLanguageError {
    /// A productive cycle can participate in an accepting derivation.
    #[error("the accepting derivation language is infinite")]
    InfiniteLanguage,
}

#[derive(Clone, Debug)]
struct PlannedRule {
    original_index: usize,
    symbol: Symbol,
    children: Box<[StateId]>,
    weight: f64,
}

/// Reusable immutable plan for enumerating a finite derivation language.
///
/// Plan construction discards unproductive rules and components that cannot
/// occur below an accepting state. It rejects only productive cycles in that
/// relevant portion; irrelevant and unproductive cycles are harmless. The
/// plan owns the required rule data, so it may outlive the source automaton and
/// can create any number of independent iterators.
#[derive(Clone, Debug)]
pub struct FiniteLanguagePlan {
    accepting: Vec<StateId>,
    rules: Vec<PlannedRule>,
    rules_by_state: Vec<Vec<usize>>,
}

impl FiniteLanguagePlan {
    /// Analyze and copy the finite accepting portion of `automaton`.
    ///
    /// Enumeration concerns accepting derivations, not distinct labeled trees:
    /// ambiguous runs are retained separately. Rule weights are copied for
    /// inspection but do not affect completeness or order.
    pub fn new(automaton: &Explicit) -> Result<Self, FiniteLanguageError> {
        let analysis = analyze_explicit(automaton);
        if analysis.topological.is_none() {
            return Err(FiniteLanguageError::InfiniteLanguage);
        }
        Ok(Self::from_analysis(automaton, analysis))
    }

    fn from_analysis(automaton: &Explicit, analysis: LanguageAnalysis) -> Self {
        let accepting = (0..automaton.num_states())
            .map(StateId)
            .filter(|state| automaton.is_accepting(state) && analysis.productive[state.index()])
            .collect::<Vec<_>>();
        let mut rules = Vec::new();
        let mut rules_by_state = vec![Vec::new(); automaton.num_states() as usize];
        for original_index in 0..automaton.num_rules() {
            let rule = automaton.rule(original_index);
            if !analysis.productive_rules[original_index] || !analysis.relevant[rule.result.index()]
            {
                continue;
            }
            let plan_index = rules.len();
            rules.push(PlannedRule {
                original_index,
                symbol: rule.symbol,
                children: rule.children.into(),
                weight: rule.weight,
            });
            rules_by_state[rule.result.index()].push(plan_index);
        }
        Self {
            accepting,
            rules,
            rules_by_state,
        }
    }

    /// Create a fresh iterator with independent reusable traversal storage.
    pub fn iter(&self) -> FiniteLanguageIterator<'_> {
        FiniteLanguageIterator::new(self)
    }
}

/// One node in the currently selected accepting derivation.
///
/// Nodes are exposed in root-first, left-to-right pre-order. Rule indices refer
/// to the source automaton's stable [`Explicit::rule`] order.
#[derive(Clone, Debug, PartialEq)]
pub struct DerivationNode {
    state: StateId,
    rule_index: usize,
    symbol: Symbol,
    weight: f64,
    parent: Option<usize>,
    child_position: Option<usize>,
    arity: usize,
    choice: usize,
}

impl DerivationNode {
    /// State assigned to this occurrence.
    pub fn state(&self) -> StateId {
        self.state
    }

    /// Index of the selected rule in the source automaton.
    pub fn rule_index(&self) -> usize {
        self.rule_index
    }

    /// Symbol selected at this occurrence.
    pub fn symbol(&self) -> Symbol {
        self.symbol
    }

    /// Weight stored on the selected rule; enumeration itself ignores weights.
    pub fn weight(&self) -> f64 {
        self.weight
    }

    /// Pre-order index of the parent, or `None` at the root.
    pub fn parent(&self) -> Option<usize> {
        self.parent
    }

    /// Left-to-right position below the parent, or `None` at the root.
    pub fn child_position(&self) -> Option<usize> {
        self.child_position
    }

    /// Number of children selected by this node's rule.
    pub fn arity(&self) -> usize {
        self.arity
    }
}

/// Borrowed view of the current accepting derivation.
///
/// The view borrows storage reused by [`FiniteLanguageIterator::advance`] and
/// is therefore valid only until the iterator is mutably accessed again.
#[derive(Clone, Copy, Debug)]
pub struct Derivation<'a> {
    nodes: &'a [DerivationNode],
}

impl<'a> Derivation<'a> {
    /// Return all nodes in root-first, left-to-right pre-order.
    pub fn nodes(&self) -> &'a [DerivationNode] {
        self.nodes
    }

    /// Iterate over the pre-order node sequence.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &'a DerivationNode> {
        self.nodes.iter()
    }

    /// Return the number of nodes in this derivation.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Return whether this derivation contains no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

#[derive(Clone, Copy)]
struct ExpectedNode {
    state: StateId,
    parent: Option<usize>,
    child_position: Option<usize>,
    choice: usize,
}

/// Lending iterator over every derivation of a finite explicit language.
///
/// Output order is deliberately unspecified. Call [`Self::advance`], inspect
/// [`Self::current`], and finish before advancing again. The iterator reuses a
/// flat traversal buffer and rebuilds only the suffix affected by backtracking.
pub struct FiniteLanguageIterator<'a> {
    plan: &'a FiniteLanguagePlan,
    accepting_position: usize,
    nodes: Vec<DerivationNode>,
    alternatives: Vec<usize>,
    current: bool,
    exhausted: bool,
    changed_from: Option<usize>,
}

impl<'a> FiniteLanguageIterator<'a> {
    fn new(plan: &'a FiniteLanguagePlan) -> Self {
        Self {
            plan,
            accepting_position: 0,
            nodes: Vec::new(),
            alternatives: Vec::new(),
            current: false,
            exhausted: false,
            changed_from: None,
        }
    }

    /// Advance to the next accepting derivation.
    ///
    /// Returns `false` permanently after exhaustion. A successful call makes a
    /// complete borrowed derivation available through [`Self::current`].
    pub fn advance(&mut self) -> bool {
        if self.exhausted {
            return false;
        }
        if !self.current {
            return self.start_accepting_state();
        }

        if let Some(changed) = self.alternatives.pop() {
            let next_choice = self.nodes[changed].choice + 1;
            self.rebuild_suffix(changed, next_choice);
            self.changed_from = Some(changed);
            return true;
        }

        self.accepting_position += 1;
        self.start_accepting_state()
    }

    /// Return the current derivation, or `None` before advancement and after exhaustion.
    pub fn current(&self) -> Option<Derivation<'_>> {
        self.current.then_some(Derivation { nodes: &self.nodes })
    }

    /// Return the first changed pre-order position for the current derivation.
    ///
    /// The first derivation and every change of accepting root state return
    /// `Some(0)`. Everything before the returned position is identical to the
    /// preceding derivation. Returns `None` when there is no current derivation.
    pub fn changed_from(&self) -> Option<usize> {
        self.changed_from
    }

    fn start_accepting_state(&mut self) -> bool {
        let Some(&state) = self.plan.accepting.get(self.accepting_position) else {
            self.nodes.clear();
            self.alternatives.clear();
            self.current = false;
            self.exhausted = true;
            self.changed_from = None;
            return false;
        };
        self.nodes.clear();
        self.alternatives.clear();
        self.expand(vec![ExpectedNode {
            state,
            parent: None,
            child_position: None,
            choice: 0,
        }]);
        self.current = true;
        self.changed_from = Some(0);
        true
    }

    fn rebuild_suffix(&mut self, changed: usize, next_choice: usize) {
        let changed_node = &self.nodes[changed];
        let mut continuations = Vec::new();
        let mut cursor = changed;
        while let Some(parent_index) = self.nodes[cursor].parent {
            let child_position = self.nodes[cursor]
                .child_position
                .expect("non-root node must have a child position");
            let parent = &self.nodes[parent_index];
            let parent_rule_index = self.plan.rules_by_state[parent.state.index()][parent.choice];
            let parent_rule = &self.plan.rules[parent_rule_index];
            for position in child_position + 1..parent_rule.children.len() {
                continuations.push(ExpectedNode {
                    state: parent_rule.children[position],
                    parent: Some(parent_index),
                    child_position: Some(position),
                    choice: 0,
                });
            }
            cursor = parent_index;
        }

        let changed_expected = ExpectedNode {
            state: changed_node.state,
            parent: changed_node.parent,
            child_position: changed_node.child_position,
            choice: next_choice,
        };
        self.nodes.truncate(changed);
        self.alternatives.retain(|&index| index < changed);

        let mut pending = continuations.into_iter().rev().collect::<Vec<_>>();
        pending.push(changed_expected);
        self.expand(pending);
    }

    fn expand(&mut self, mut pending: Vec<ExpectedNode>) {
        while let Some(expected) = pending.pop() {
            let node_index = self.nodes.len();
            let rule_options = &self.plan.rules_by_state[expected.state.index()];
            let plan_rule_index = rule_options[expected.choice];
            let rule = &self.plan.rules[plan_rule_index];
            self.nodes.push(DerivationNode {
                state: expected.state,
                rule_index: rule.original_index,
                symbol: rule.symbol,
                weight: rule.weight,
                parent: expected.parent,
                child_position: expected.child_position,
                arity: rule.children.len(),
                choice: expected.choice,
            });
            if expected.choice + 1 < rule_options.len() {
                self.alternatives.push(node_index);
            }
            for (position, &child) in rule.children.iter().enumerate().rev() {
                pending.push(ExpectedNode {
                    state: child,
                    parent: Some(node_index),
                    child_position: Some(position),
                    choice: 0,
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, LanguageCardinality};
    use num_bigint::BigUint;
    use packed_term_arena::tree::{Tree, TreeArena};

    fn symbols(iterator: &FiniteLanguageIterator<'_>) -> Vec<u32> {
        iterator
            .current()
            .unwrap()
            .iter()
            .map(|node| node.symbol().0)
            .collect()
    }

    fn sorted_symbols(arena: &TreeArena<Symbol>, root: Tree, output: &mut Vec<u32>) {
        output.push(arena.get_label(root).0);
        for &child in arena.get_children(root) {
            sorted_symbols(arena, child, output);
        }
    }

    #[test]
    fn empty_protocol_is_stable() {
        let automaton = ExplicitBuilder::new().build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        assert!(iterator.current().is_none());
        assert_eq!(iterator.changed_from(), None);
        assert!(!iterator.advance());
        assert!(iterator.current().is_none());
        assert_eq!(iterator.changed_from(), None);
        assert!(!iterator.advance());
    }

    #[test]
    fn exposes_preorder_structure_and_rule_identity() {
        let mut builder = ExplicitBuilder::new();
        let left = builder.new_state();
        let right = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(Symbol(10), vec![], left, 0.0);
        builder.add_rule(Symbol(11), vec![], right);
        builder.add_weighted_rule(Symbol(12), vec![left, right], root, 0.25);
        builder.add_accepting(root);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        assert!(iterator.advance());
        assert_eq!(iterator.changed_from(), Some(0));
        let nodes = iterator.current().unwrap();
        assert_eq!(nodes.len(), 3);
        assert_eq!(nodes.nodes()[0].parent(), None);
        assert_eq!(nodes.nodes()[0].arity(), 2);
        assert_eq!(nodes.nodes()[0].rule_index(), 2);
        assert_eq!(nodes.nodes()[1].parent(), Some(0));
        assert_eq!(nodes.nodes()[1].child_position(), Some(0));
        assert_eq!(nodes.nodes()[2].parent(), Some(0));
        assert_eq!(nodes.nodes()[2].child_position(), Some(1));
        assert_eq!(nodes.nodes()[1].weight(), 0.0);
        assert!(!iterator.advance());
    }

    #[test]
    fn cartesian_repeated_children_and_changed_suffixes_are_exact() {
        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let root = builder.new_state();
        builder.add_rule(Symbol(0), vec![], leaf);
        builder.add_rule(Symbol(1), vec![], leaf);
        builder.add_rule(Symbol(2), vec![leaf, leaf], root);
        builder.add_accepting(root);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        let mut found = Vec::new();
        let mut changes = Vec::new();
        while iterator.advance() {
            changes.push(iterator.changed_from().unwrap());
            found.push(symbols(&iterator));
        }
        assert_eq!(
            found,
            vec![vec![2, 0, 0], vec![2, 0, 1], vec![2, 1, 0], vec![2, 1, 1]]
        );
        assert_eq!(changes, vec![0, 2, 1, 2]);
        assert_eq!(
            automaton.language_cardinality_as::<BigUint>(),
            LanguageCardinality::Finite(BigUint::from(4u8))
        );
    }

    #[test]
    fn handles_shape_changes_and_multiple_accepting_states() {
        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let first_root = builder.new_state();
        let second_root = builder.new_state();
        builder.add_rule(Symbol(0), vec![], leaf);
        builder.add_rule(Symbol(1), vec![], first_root);
        builder.add_rule(Symbol(2), vec![leaf], first_root);
        builder.add_rule(Symbol(3), vec![], second_root);
        builder.add_accepting(first_root);
        builder.add_accepting(second_root);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        let mut values = Vec::new();
        let mut changed = Vec::new();
        while iterator.advance() {
            values.push(symbols(&iterator));
            changed.push(iterator.changed_from());
        }
        assert_eq!(values, vec![vec![1], vec![2, 0], vec![3]]);
        assert_eq!(changed, vec![Some(0), Some(0), Some(0)]);
    }

    #[test]
    fn ambiguous_runs_are_not_deduplicated() {
        let mut builder = ExplicitBuilder::new();
        let left = builder.new_state();
        let right = builder.new_state();
        let root = builder.new_state();
        builder.add_rule(Symbol(0), vec![], left);
        builder.add_rule(Symbol(0), vec![], right);
        builder.add_rule(Symbol(1), vec![left], root);
        builder.add_rule(Symbol(1), vec![right], root);
        builder.add_accepting(root);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        let mut rule_runs = Vec::new();
        while iterator.advance() {
            rule_runs.push(
                iterator
                    .current()
                    .unwrap()
                    .iter()
                    .map(DerivationNode::rule_index)
                    .collect::<Vec<_>>(),
            );
        }
        assert_eq!(rule_runs, vec![vec![2, 0], vec![3, 1]]);
    }

    #[test]
    fn ignores_irrelevant_and_unproductive_cycles_but_rejects_relevant_cycle() {
        let mut builder = ExplicitBuilder::new();
        let accepted = builder.new_state();
        let irrelevant = builder.new_state();
        let unproductive = builder.new_state();
        builder.add_rule(Symbol(0), vec![], accepted);
        builder.add_rule(Symbol(1), vec![], irrelevant);
        builder.add_rule(Symbol(2), vec![irrelevant], irrelevant);
        builder.add_rule(Symbol(3), vec![unproductive], unproductive);
        builder.add_accepting(accepted);
        assert!(FiniteLanguagePlan::new(&builder.build()).is_ok());

        let mut builder = ExplicitBuilder::new();
        let state = builder.new_state();
        builder.add_rule(Symbol(0), vec![], state);
        builder.add_rule(Symbol(1), vec![state], state);
        builder.add_accepting(state);
        assert!(matches!(
            FiniteLanguagePlan::new(&builder.build()),
            Err(FiniteLanguageError::InfiniteLanguage)
        ));
    }

    #[test]
    fn iterators_from_one_plan_are_independent() {
        let mut builder = ExplicitBuilder::new();
        let state = builder.new_state();
        builder.add_rule(Symbol(0), vec![], state);
        builder.add_rule(Symbol(1), vec![], state);
        builder.add_accepting(state);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut first = plan.iter();
        let mut second = plan.iter();
        assert!(first.advance());
        assert!(first.advance());
        assert!(second.advance());
        assert_eq!(symbols(&first), vec![1]);
        assert_eq!(symbols(&second), vec![0]);
    }

    #[test]
    fn deep_and_wide_derivations_are_iterative() {
        let mut builder = ExplicitBuilder::new();
        let mut state = builder.new_state();
        builder.add_rule(Symbol(0), vec![], state);
        for _ in 0..20_000 {
            let parent = builder.new_state();
            builder.add_rule(Symbol(1), vec![state], parent);
            state = parent;
        }
        builder.add_accepting(state);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        assert!(iterator.advance());
        assert_eq!(iterator.current().unwrap().len(), 20_001);
        assert!(!iterator.advance());

        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let root = builder.new_state();
        builder.add_rule(Symbol(0), vec![], leaf);
        builder.add_rule(Symbol(1), vec![leaf; 1_000], root);
        builder.add_accepting(root);
        let automaton = builder.build();
        let plan = FiniteLanguagePlan::new(&automaton).unwrap();
        let mut iterator = plan.iter();
        assert!(iterator.advance());
        assert_eq!(iterator.current().unwrap().len(), 1_001);
    }

    #[test]
    fn trimming_cardinality_sorted_language_and_incremental_views_agree() {
        let mut builder = ExplicitBuilder::new();
        let dead = builder.new_state();
        let leaf = builder.new_state();
        let root = builder.new_state();
        builder.add_rule(Symbol(9), vec![], dead);
        builder.add_rule(Symbol(0), vec![], leaf);
        builder.add_rule(Symbol(1), vec![], leaf);
        builder.add_rule(Symbol(2), vec![leaf, leaf], root);
        builder.add_accepting(root);

        let original = builder.clone().build();
        let trimmed = builder.build_trimmed();
        let metadata = ["dead", "leaf", "root"];
        let transferred = (0..trimmed.automaton.num_states())
            .map(|index| metadata[trimmed.state_mapping.old_state(StateId(index)).index()])
            .collect::<Vec<_>>();
        assert_eq!(transferred, vec!["leaf", "root"]);
        assert_eq!(trimmed.state_mapping.new_state(dead), None);

        assert_eq!(
            original.language_cardinality_as::<BigUint>(),
            trimmed.automaton.language_cardinality_as::<BigUint>()
        );

        let mut expected = Vec::new();
        let original_plan = FiniteLanguagePlan::new(&original).unwrap();
        let mut original_iterator = original_plan.iter();
        while original_iterator.advance() {
            expected.push(symbols(&original_iterator));
        }
        expected.sort();

        let trimmed_plan = FiniteLanguagePlan::new(&trimmed.automaton).unwrap();
        let mut iterator = trimmed_plan.iter();
        let mut reconstructed = Vec::new();
        let mut actual = Vec::new();
        while iterator.advance() {
            let changed = iterator.changed_from().unwrap();
            reconstructed.truncate(changed);
            reconstructed.extend(
                iterator.current().unwrap().nodes()[changed..]
                    .iter()
                    .map(|node| node.symbol().0),
            );
            actual.push(reconstructed.clone());
        }
        actual.sort();
        assert_eq!(actual, expected);

        let mut sorted = Vec::new();
        let mut sorted_iterator = original.sorted_language();
        while let Some(tree) = sorted_iterator.next() {
            let mut labels = Vec::new();
            sorted_symbols(sorted_iterator.arena(), tree.tree(), &mut labels);
            sorted.push(labels);
        }
        sorted.sort();
        assert_eq!(sorted, expected);
        assert_eq!(expected.len(), 4);
    }

    #[test]
    fn generated_small_dags_agree_with_cardinality_and_trimming() {
        for seed in 0u32..64 {
            let mut builder = ExplicitBuilder::new();
            let q0 = builder.new_state();
            let q1 = builder.new_state();
            let q2 = builder.new_state();
            let q3 = builder.new_state();
            let dead = builder.new_state();
            builder.add_rule(Symbol(0), vec![], q0);
            if seed & 1 != 0 {
                builder.add_rule(Symbol(1), vec![], q0);
            }
            builder.add_rule(Symbol(2), vec![], q1);
            if seed & 2 != 0 {
                builder.add_rule(Symbol(3), vec![q0, q0], q1);
            }
            builder.add_rule(Symbol(4), vec![q0], q2);
            if seed & 4 != 0 {
                builder.add_rule(Symbol(5), vec![q0, q1], q2);
            }
            builder.add_rule(Symbol(6), vec![q1, q2], q3);
            if seed & 8 != 0 {
                builder.add_rule(Symbol(7), vec![], q3);
            }
            if seed & 16 != 0 {
                builder.add_rule(Symbol(8), vec![], dead);
            }
            builder.add_rule(Symbol(9), vec![dead], dead);
            builder.add_accepting(q2);
            if seed & 32 != 0 {
                builder.add_accepting(q3);
            }

            let original = builder.clone().build();
            let expected = match original.language_cardinality_as::<BigUint>() {
                LanguageCardinality::Finite(value) => value,
                other => panic!("generated DAG must be finite, got {other:?}"),
            };
            let plan = FiniteLanguagePlan::new(&original).unwrap();
            let mut iterator = plan.iter();
            let mut count = BigUint::from(0u8);
            while iterator.advance() {
                count += 1u8;
            }
            assert_eq!(count, expected, "seed {seed}");

            let trimmed = builder.build_trimmed();
            assert_eq!(trimmed.state_mapping.new_state(dead), None, "seed {seed}");
            assert_eq!(
                trimmed.automaton.language_cardinality_as::<BigUint>(),
                LanguageCardinality::Finite(expected),
                "seed {seed}"
            );
        }
    }
}
