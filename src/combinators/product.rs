use crate::{BottomUpTa, DetBottomUpTa, Symbol, run::cartesian_product};
use smallvec::SmallVec;

/// Intersection product of two bottom-up automata.
///
/// `Product(a, b)` accepts exactly the trees accepted by both component
/// automata. Its state is a pair `(state_from_a, state_from_b)`.
///
/// The generic [`BottomUpTa`] implementation asks both sides for possible
/// parent states and emits their cartesian product. When both components are
/// deterministic, `Product` also implements [`DetBottomUpTa`] and avoids that
/// result-set enumeration. High-performance parsing workloads will still
/// usually want an indexed product in a later phase.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Product<A, B>(pub A, pub B);

impl<A, B> BottomUpTa for Product<A, B>
where
    A: BottomUpTa,
    B: BottomUpTa,
{
    type State = (A::State, B::State);

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        let mut a_children: SmallVec<[A::State; 4]> = SmallVec::new();
        let mut b_children: SmallVec<[B::State; 4]> = SmallVec::new();
        for (a, b) in children {
            a_children.push(a.clone());
            b_children.push(b.clone());
        }

        let mut a_results: SmallVec<[A::State; 2]> = SmallVec::new();
        self.0.step(f, &a_children, &mut |q| a_results.push(q));
        if a_results.is_empty() {
            return;
        }

        let mut b_results: SmallVec<[B::State; 2]> = SmallVec::new();
        self.1.step(f, &b_children, &mut |q| b_results.push(q));
        for qa in &a_results {
            for qb in &b_results {
                out((qa.clone(), qb.clone()));
            }
        }
    }

    fn is_accepting(&self, q: &Self::State) -> bool {
        self.0.is_accepting(&q.0) && self.1.is_accepting(&q.1)
    }
}

impl<A, B> DetBottomUpTa for Product<A, B>
where
    A: DetBottomUpTa,
    B: DetBottomUpTa,
{
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        let mut a_children: SmallVec<[A::State; 4]> = SmallVec::new();
        let mut b_children: SmallVec<[B::State; 4]> = SmallVec::new();
        for (a, b) in children {
            a_children.push(a.clone());
            b_children.push(b.clone());
        }

        let qa = self.0.step_det(f, &a_children)?;
        let qb = self.1.step_det(f, &b_children)?;
        Some((qa, qb))
    }
}

pub(crate) fn product_step_sets<S: Clone>(pools: &[Vec<S>], mut out: impl FnMut(&[S])) {
    let slices: SmallVec<[&[S]; 4]> = pools.iter().map(Vec::as_slice).collect();
    cartesian_product(&slices, |tuple| out(tuple));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BottomUpTa, DetBottomUpTa, ExplicitBuilder, Symbol};

    #[test]
    fn product_intersects_languages() {
        let a = Symbol(0);

        let mut left_b = ExplicitBuilder::new();
        let left_q = left_b.new_state();
        left_b.add_rule(a, vec![], left_q);
        left_b.add_accepting(left_q);
        let left = left_b.build();

        let mut right_b = ExplicitBuilder::new();
        let right_q = right_b.new_state();
        right_b.add_rule(a, vec![], right_q);
        right_b.add_accepting(right_q);
        let right = right_b.build();

        let product = Product(left, right);
        let mut out = Vec::new();
        product.step(a, &[], &mut |q| out.push(q));
        assert_eq!(out.len(), 1);
        assert!(product.is_accepting(&out[0]));
        assert_eq!(product.step_det(a, &[]), Some(out[0]));
    }

    #[test]
    fn product_rejects_when_one_side_lacks_rule() {
        let a = Symbol(0);
        let mut left_b = ExplicitBuilder::new();
        let left_q = left_b.new_state();
        left_b.add_rule(a, vec![], left_q);
        left_b.add_accepting(left_q);

        let mut right_b = ExplicitBuilder::new();
        right_b.new_state();

        let product = Product(left_b.build(), right_b.build());
        let mut out = Vec::new();
        product.step(a, &[], &mut |q| out.push(q));
        assert!(out.is_empty());
    }
}
