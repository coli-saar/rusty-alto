use crate::{BottomUpTa, DetBottomUpTa, Symbol, combinators::product::product_step_sets};
use std::collections::BTreeSet;

/// Lazy subset construction for a nondeterministic automaton.
///
/// `Determinized(a)` has states that are sets of `a`'s states. A deterministic
/// transition computes all possible underlying transitions and packages the
/// result as one set.
///
/// This generic version uses [`std::collections::BTreeSet`], so it favors
/// clarity and broad compatibility over raw speed. It is most useful for small
/// examples, tests, and as a baseline for denser bitset-based variants.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Determinized<A>(pub A);

impl<A> BottomUpTa for Determinized<A>
where
    A: BottomUpTa,
    A::State: Ord,
{
    type State = BTreeSet<A::State>;

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        let result = deterministic_result(&self.0, f, children);
        if !result.is_empty() {
            out(result);
        }
    }

    fn is_accepting(&self, qs: &Self::State) -> bool {
        qs.iter().any(|q| self.0.is_accepting(q))
    }
}

impl<A> DetBottomUpTa for Determinized<A>
where
    A: BottomUpTa,
    A::State: Ord,
{
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        let result = deterministic_result(&self.0, f, children);
        (!result.is_empty()).then_some(result)
    }
}

fn deterministic_result<A>(
    automaton: &A,
    f: Symbol,
    children: &[BTreeSet<A::State>],
) -> BTreeSet<A::State>
where
    A: BottomUpTa,
    A::State: Ord,
{
    let pools: Vec<Vec<A::State>> = children
        .iter()
        .map(|set| set.iter().cloned().collect())
        .collect();
    let mut result = BTreeSet::new();
    product_step_sets(&pools, |tuple| {
        automaton.step(f, tuple, &mut |q| {
            result.insert(q);
        });
    });
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, Symbol};

    #[test]
    fn determinizes_nullary_nondeterminism() {
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        b.add_rule(Symbol(0), vec![], q0);
        b.add_rule(Symbol(0), vec![], q1);
        b.add_accepting(q1);
        let det = Determinized(b.build());
        let state = det.step_det(Symbol(0), &[]).unwrap();
        assert_eq!(state.len(), 2);
        assert!(det.is_accepting(&state));
    }
}
