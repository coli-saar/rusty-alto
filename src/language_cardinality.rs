//! Exact or checked cardinality of explicit derivation languages.

use crate::{BottomUpTa, Explicit, StateId, language_analysis::analyze_explicit};
use num_traits::{CheckedAdd, CheckedMul, One, Zero};

/// Cardinality of an explicit automaton's accepting derivation language.
///
/// This counts accepting runs, not distinct symbol-labeled trees. Consequently,
/// two different runs for the same labeled tree contribute two to the count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LanguageCardinality<N = usize> {
    /// The derivation language is finite and has exactly this cardinality.
    Finite(N),
    /// A productive cycle occurs in an accepting derivation.
    Infinite,
    /// The language is finite, but its exact count is not representable by `N`.
    TooLarge,
}

impl Explicit {
    /// Count accepting derivations using caller-selected checked arithmetic.
    ///
    /// Productive cycles matter only when reachable top-down from an accepting
    /// state through productive rules. Weights do not affect the result. Use an
    /// arbitrary-precision type such as `num_bigint::BigUint` for exact counts
    /// of any finite language.
    pub fn language_cardinality_as<N>(&self) -> LanguageCardinality<N>
    where
        N: Clone + Zero + One + CheckedAdd + CheckedMul,
    {
        let analysis = analyze_explicit(self);
        let Some(order) = analysis.topological else {
            return LanguageCardinality::Infinite;
        };
        let mut counts = vec![N::zero(); self.num_states() as usize];

        for state in order {
            let mut state_total = N::zero();
            for &rule_index in &analysis.rules_by_result[state.index()] {
                if !analysis.productive_rules[rule_index] {
                    continue;
                }
                let rule = self.rule(rule_index);
                let mut combinations = N::one();
                for child in rule.children {
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
        for (index, count) in counts.iter().enumerate() {
            let state = StateId(index as u32);
            if self.is_accepting(&state) && analysis.productive[index] {
                let Some(next) = total.checked_add(count) else {
                    return LanguageCardinality::TooLarge;
                };
                total = next;
            }
        }
        LanguageCardinality::Finite(total)
    }

    /// Count accepting derivations using checked `usize` arithmetic.
    ///
    /// This compatibility convenience method returns [`LanguageCardinality::TooLarge`]
    /// when the finite count exceeds the platform's `usize` range.
    pub fn language_cardinality(&self) -> LanguageCardinality {
        self.language_cardinality_as()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, Symbol};
    use num_bigint::BigUint;

    #[test]
    fn empty_and_unproductive_languages_have_zero_derivations() {
        assert_eq!(
            ExplicitBuilder::new().build().language_cardinality(),
            LanguageCardinality::Finite(0)
        );

        let mut builder = ExplicitBuilder::new();
        let state = builder.new_state();
        builder.add_accepting(state);
        assert_eq!(
            builder.build().language_cardinality(),
            LanguageCardinality::Finite(0)
        );
    }

    #[test]
    fn counts_rules_accepting_states_repeated_children_and_ambiguity() {
        let mut builder = ExplicitBuilder::new();
        let left = builder.new_state();
        let right = builder.new_state();
        let root = builder.new_state();
        let extra = builder.new_state();
        builder.add_weighted_rule(Symbol(0), vec![], left, 0.0);
        builder.add_rule(Symbol(0), vec![], right);
        builder.add_rule(Symbol(1), vec![left, left], root);
        builder.add_rule(Symbol(1), vec![right, right], root);
        builder.add_rule(Symbol(2), vec![], extra);
        builder.add_accepting(root);
        builder.add_accepting(extra);
        assert_eq!(
            builder.build().language_cardinality(),
            LanguageCardinality::Finite(3)
        );
    }

    #[test]
    fn classifies_only_relevant_productive_cycles_as_infinite() {
        let mut builder = ExplicitBuilder::new();
        let useful = builder.new_state();
        let irrelevant = builder.new_state();
        let unproductive = builder.new_state();
        builder.add_rule(Symbol(0), vec![], useful);
        builder.add_rule(Symbol(1), vec![], irrelevant);
        builder.add_rule(Symbol(2), vec![irrelevant], irrelevant);
        builder.add_rule(Symbol(3), vec![unproductive], unproductive);
        builder.add_accepting(useful);
        assert_eq!(
            builder.build().language_cardinality(),
            LanguageCardinality::Finite(1)
        );

        let mut builder = ExplicitBuilder::new();
        let first = builder.new_state();
        let second = builder.new_state();
        builder.add_rule(Symbol(0), vec![], first);
        builder.add_rule(Symbol(1), vec![first], second);
        builder.add_rule(Symbol(2), vec![second], first);
        builder.add_accepting(second);
        assert_eq!(
            builder.build().language_cardinality(),
            LanguageCardinality::Infinite
        );
    }

    #[test]
    fn checked_and_arbitrary_precision_counts_agree_until_overflow() {
        let mut builder = ExplicitBuilder::new();
        let mut state = builder.new_state();
        builder.add_rule(Symbol(0), vec![], state);
        builder.add_rule(Symbol(1), vec![], state);
        for depth in 0..7 {
            let parent = builder.new_state();
            builder.add_rule(Symbol(depth + 2), vec![state, state], parent);
            state = parent;
        }
        builder.add_accepting(state);
        let automaton = builder.build();
        assert_eq!(
            automaton.language_cardinality_as::<u8>(),
            LanguageCardinality::TooLarge
        );
        assert_eq!(
            automaton.language_cardinality_as::<BigUint>(),
            LanguageCardinality::Finite(BigUint::from(2u8).pow(128))
        );
    }

    #[test]
    fn deep_chain_and_wide_rule_do_not_use_the_call_stack() {
        let mut builder = ExplicitBuilder::new();
        let mut state = builder.new_state();
        builder.add_rule(Symbol(0), vec![], state);
        for _ in 0..20_000 {
            let parent = builder.new_state();
            builder.add_rule(Symbol(1), vec![state], parent);
            state = parent;
        }
        builder.add_accepting(state);
        assert_eq!(
            builder.build().language_cardinality(),
            LanguageCardinality::Finite(1)
        );

        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let root = builder.new_state();
        builder.add_rule(Symbol(0), vec![], leaf);
        builder.add_rule(Symbol(1), vec![leaf; 1_000], root);
        builder.add_accepting(root);
        assert_eq!(
            builder.build().language_cardinality(),
            LanguageCardinality::Finite(1)
        );
    }
}
