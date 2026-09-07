//! Fast unsorted enumeration of finite explicit derivation languages.

use crate::{
    BottomUpTa, Explicit, LanguageCardinality, StateId, Symbol,
    language_analysis::{LanguageAnalysis, analyze_explicit},
};
use num_traits::{CheckedAdd, CheckedMul, One, Zero};
use thiserror::Error;

/// Error returned when a finite-language plan cannot be constructed.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum FiniteLanguageError {
    /// A productive cycle can participate in an accepting derivation.
    #[error("the accepting derivation language is infinite")]
    InfiniteLanguage,
}

#[derive(Clone, Debug, PartialEq)]
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
    topological: Vec<StateId>,
}

impl FiniteLanguagePlan {
    /// Analyze and copy the finite accepting portion of `automaton`.
    ///
    /// Enumeration concerns accepting derivations, not distinct labeled trees:
    /// ambiguous runs are retained separately. Rule weights are copied for
    /// inspection but do not affect completeness or order.
    pub fn new(automaton: &Explicit) -> Result<Self, FiniteLanguageError> {
        let mut analysis = analyze_explicit(automaton);
        let Some(topological) = analysis.topological.take() else {
            return Err(FiniteLanguageError::InfiniteLanguage);
        };
        Ok(Self::from_analysis(automaton, analysis, topological))
    }

    fn from_analysis(
        automaton: &Explicit,
        analysis: LanguageAnalysis,
        topological: Vec<StateId>,
    ) -> Self {
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
            topological,
        }
    }

    /// Count this plan's finite derivation language using checked arithmetic.
    ///
    /// This reuses the productivity, relevance, and topological analysis
    /// already performed when the plan was created.
    pub fn language_cardinality_as<N>(&self) -> LanguageCardinality<N>
    where
        N: Clone + Zero + One + CheckedAdd + CheckedMul,
    {
        let mut counts = vec![N::zero(); self.rules_by_state.len()];
        for &state in &self.topological {
            let mut state_total = N::zero();
            for &rule_index in &self.rules_by_state[state.index()] {
                let mut combinations = N::one();
                for child in &self.rules[rule_index].children {
                    let Some(next) = combinations.checked_mul(&counts[child.index()]) else {
                        return LanguageCardinality::TooLarge;
                    };
                    combinations = next;
                }
                let Some(next) = state_total.checked_add(&combinations) else {
                    return LanguageCardinality::TooLarge;
                };
                state_total = next;
            }
            counts[state.index()] = state_total;
        }

        let mut total = N::zero();
        for &state in &self.accepting {
            let Some(next) = total.checked_add(&counts[state.index()]) else {
                return LanguageCardinality::TooLarge;
            };
            total = next;
        }
        LanguageCardinality::Finite(total)
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
pub struct DerivationNode<'a> {
    rule: &'a PlannedRule,
    state: StateId,
    parent: u32,
    child_position: u32,
    choice: u32,
}

impl DerivationNode<'_> {
    /// State assigned to this occurrence.
    #[inline]
    pub fn state(&self) -> StateId {
        self.state
    }

    /// Index of the selected rule in the source automaton.
    #[inline]
    pub fn rule_index(&self) -> usize {
        self.rule.original_index
    }

    /// Symbol selected at this occurrence.
    #[inline]
    pub fn symbol(&self) -> Symbol {
        self.rule.symbol
    }

    /// Weight stored on the selected rule; enumeration itself ignores weights.
    #[inline]
    pub fn weight(&self) -> f64 {
        self.rule.weight
    }

    /// Pre-order index of the parent, or `None` at the root.
    #[inline]
    pub fn parent(&self) -> Option<usize> {
        (self.parent != NO_INDEX).then_some(self.parent as usize)
    }

    /// Left-to-right position below the parent, or `None` at the root.
    #[inline]
    pub fn child_position(&self) -> Option<usize> {
        (self.child_position != NO_INDEX).then_some(self.child_position as usize)
    }

    /// Number of children selected by this node's rule.
    #[inline]
    pub fn arity(&self) -> usize {
        self.rule.children.len()
    }
}

/// Borrowed view of the current accepting derivation.
///
/// The view borrows storage reused by [`FiniteLanguageIterator::advance`] and
/// is therefore valid only until the iterator is mutably accessed again.
#[derive(Clone, Copy, Debug)]
pub struct Derivation<'a> {
    nodes: &'a [DerivationNode<'a>],
}

impl<'a> Derivation<'a> {
    /// Return all nodes in root-first, left-to-right pre-order.
    #[inline]
    pub fn nodes(&self) -> &'a [DerivationNode<'a>] {
        self.nodes
    }

    /// Iterate over the pre-order node sequence.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &'a DerivationNode<'a>> {
        self.nodes.iter()
    }

    /// Return the number of nodes in this derivation.
    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Return whether this derivation contains no nodes.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

#[derive(Clone, Copy)]
struct ExpectedNode {
    state: StateId,
    parent: u32,
    child_position: u32,
    choice: u32,
}

const NO_INDEX: u32 = u32::MAX;

/// Lending iterator over every derivation of a finite explicit language.
///
/// Output order is deliberately unspecified. Call [`Self::advance`], inspect
/// [`Self::current`], and finish before advancing again. The iterator reuses a
/// flat traversal buffer and rebuilds only the suffix affected by backtracking.
pub struct FiniteLanguageIterator<'a> {
    plan: &'a FiniteLanguagePlan,
    accepting_position: usize,
    nodes: Vec<DerivationNode<'a>>,
    alternatives: Vec<u32>,
    pending: Vec<ExpectedNode>,
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
            pending: Vec::new(),
            current: false,
            exhausted: false,
            changed_from: None,
        }
    }

    /// Advance to the next accepting derivation.
    ///
    /// Returns `false` permanently after exhaustion. A successful call makes a
    /// complete borrowed derivation available through [`Self::current`].
    #[inline]
    pub fn advance(&mut self) -> bool {
        if self.exhausted {
            return false;
        }
        if !self.current {
            return self.start_accepting_state();
        }

        if let Some(changed) = self.alternatives.pop() {
            let changed = changed as usize;
            let next_choice = self.nodes[changed].choice + 1;
            self.rebuild_suffix(changed, next_choice);
            self.changed_from = Some(changed);
            return true;
        }

        self.start_accepting_state()
    }

    /// Return the current derivation, or `None` before advancement and after exhaustion.
    #[inline]
    pub fn current(&self) -> Option<Derivation<'_>> {
        self.current.then_some(Derivation { nodes: &self.nodes })
    }

    /// Return the first changed pre-order position for the current derivation.
    ///
    /// The first derivation and every change of accepting root state return
    /// `Some(0)`. Everything before the returned position is identical to the
    /// preceding derivation. Returns `None` when there is no current derivation.
    #[inline]
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
        self.accepting_position += 1;
        self.nodes.clear();
        self.alternatives.clear();
        self.pending.clear();
        self.pending.push(ExpectedNode {
            state,
            parent: NO_INDEX,
            child_position: NO_INDEX,
            choice: 0,
        });
        self.expand();
        self.current = true;
        self.changed_from = Some(0);
        true
    }

    fn rebuild_suffix(&mut self, changed: usize, next_choice: u32) {
        let changed_node = &self.nodes[changed];
        let changed_state = changed_node.state;
        let changed_parent = changed_node.parent;
        let changed_child_position = changed_node.child_position;
        self.pending.clear();
        let mut cursor = changed;
        while self.nodes[cursor].parent != NO_INDEX {
            let child_position = self.nodes[cursor].child_position as usize;
            let parent_index = self.nodes[cursor].parent as usize;
            let parent = &self.nodes[parent_index];
            let parent_rule = parent.rule;
            for position in child_position + 1..parent_rule.children.len() {
                self.pending.push(ExpectedNode {
                    state: parent_rule.children[position],
                    parent: parent_index as u32,
                    child_position: u32::try_from(position).expect("rule arity fits in u32"),
                    choice: 0,
                });
            }
            cursor = parent_index;
        }

        self.nodes.truncate(changed);
        self.pending.reverse();
        self.pending.push(ExpectedNode {
            state: changed_state,
            parent: changed_parent,
            child_position: changed_child_position,
            choice: next_choice,
        });
        self.expand();
    }

    fn expand(&mut self) {
        while let Some(expected) = self.pending.pop() {
            let node_index = self.nodes.len();
            let rule_options = &self.plan.rules_by_state[expected.state.index()];
            let rule = &self.plan.rules[rule_options[expected.choice as usize]];
            self.nodes.push(DerivationNode {
                rule,
                state: expected.state,
                parent: expected.parent,
                child_position: expected.child_position,
                choice: expected.choice,
            });
            if expected.choice as usize + 1 < rule_options.len() {
                self.alternatives
                    .push(u32::try_from(node_index).expect("a derivation fits in u32"));
            }
            let parent = u32::try_from(node_index).expect("a derivation fits in u32");
            for (position, &child) in rule.children.iter().enumerate().rev() {
                self.pending.push(ExpectedNode {
                    state: child,
                    parent,
                    child_position: u32::try_from(position).expect("rule arity fits in u32"),
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
    fn reuses_pending_storage_across_derivations() {
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

        assert!(iterator.advance());
        let capacity = iterator.pending.capacity();
        let allocation = iterator.pending.as_ptr();
        assert!(capacity > 0);

        while iterator.advance() {
            assert_eq!(iterator.pending.capacity(), capacity);
            assert_eq!(iterator.pending.as_ptr(), allocation);
        }
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
            assert_eq!(
                plan.language_cardinality_as::<BigUint>(),
                LanguageCardinality::Finite(expected.clone()),
                "seed {seed}"
            );
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
