use crate::{
    BottomUpTa, DetBottomUpTa, IndexedBottomUpTa, Symbol, TopDownTa, run::cartesian_product,
};
use smallvec::SmallVec;

/// Intersection product of two bottom-up automata.
///
/// `Product(a, b)` accepts exactly the trees accepted by both component
/// automata. Its state is a pair `(state_from_a, state_from_b)`.
///
/// The generic [`BottomUpTa`] implementation asks both sides for possible
/// parent states and emits their cartesian product. When both components are
/// deterministic, `Product` also implements [`DetBottomUpTa`] and avoids that
/// result-set enumeration. If both components implement
/// [`IndexedBottomUpTa`], the product also supports indexed rule joins for
/// sibling-finder-style parsing algorithms.
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

impl<A, B> IndexedBottomUpTa for Product<A, B>
where
    A: IndexedBottomUpTa,
    B: IndexedBottomUpTa,
{
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &Self::State,
        out: &mut dyn FnMut(&[Self::State], Self::State),
    ) {
        self.0
            .step_partial(f, position, &state_at_position.0, &mut |a_children, qa| {
                self.1
                    .step_partial(f, position, &state_at_position.1, &mut |b_children, qb| {
                        if a_children.len() != b_children.len() {
                            return;
                        }

                        let mut children: SmallVec<[Self::State; 4]> =
                            SmallVec::with_capacity(a_children.len());
                        for (a_child, b_child) in a_children.iter().zip(b_children) {
                            children.push((a_child.clone(), b_child.clone()));
                        }
                        out(&children, (qa.clone(), qb));
                    });
            });
    }
}

impl<A, B> TopDownTa for Product<A, B>
where
    A: TopDownTa,
    B: TopDownTa,
{
    fn step_topdown(&self, parent: &Self::State, out: &mut dyn FnMut(Symbol, &[Self::State])) {
        self.0.step_topdown(&parent.0, &mut |a_symbol, a_children| {
            self.1.step_topdown(&parent.1, &mut |b_symbol, b_children| {
                if a_symbol != b_symbol || a_children.len() != b_children.len() {
                    return;
                }

                let mut children: SmallVec<[Self::State; 4]> =
                    SmallVec::with_capacity(a_children.len());
                for (a_child, b_child) in a_children.iter().zip(b_children) {
                    children.push((a_child.clone(), b_child.clone()));
                }
                out(a_symbol, &children);
            });
        });
    }

    fn initial_states(&self, out: &mut dyn FnMut(Self::State)) {
        let mut left = SmallVec::<[A::State; 4]>::new();
        let mut right = SmallVec::<[B::State; 4]>::new();
        self.0.initial_states(&mut |q| left.push(q));
        self.1.initial_states(&mut |q| right.push(q));
        for qa in &left {
            for qb in &right {
                out((qa.clone(), qb.clone()));
            }
        }
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

    #[test]
    fn indexed_product_joins_matching_partial_rules() {
        let a = Symbol(0);
        let f = Symbol(1);

        let mut left_b = ExplicitBuilder::new();
        let left_leaf = left_b.new_state();
        let left_root = left_b.new_state();
        left_b.add_rule(a, vec![], left_leaf);
        left_b.add_rule(f, vec![left_leaf, left_leaf], left_root);
        let left = left_b.build();

        let mut right_b = ExplicitBuilder::new();
        let right_leaf = right_b.new_state();
        let right_root = right_b.new_state();
        right_b.add_rule(a, vec![], right_leaf);
        right_b.add_rule(f, vec![right_leaf, right_leaf], right_root);
        let right = right_b.build();

        let product = Product(left, right);
        let child = (left_leaf, right_leaf);
        let mut found = Vec::new();
        product.step_partial(f, 0, &child, &mut |children, result| {
            found.push((children.to_vec(), result));
        });

        assert_eq!(found, vec![(vec![child, child], (left_root, right_root))]);
    }

    #[test]
    fn product_topdown_joins_by_parent_and_symbol() {
        let a = Symbol(0);

        let mut left_b = ExplicitBuilder::new();
        let left_q = left_b.new_state();
        left_b.add_rule(a, vec![], left_q);
        left_b.add_accepting(left_q);

        let mut right_b = ExplicitBuilder::new();
        let right_q = right_b.new_state();
        right_b.add_rule(a, vec![], right_q);
        right_b.add_accepting(right_q);

        let product = Product(left_b.build(), right_b.build());
        let parent = (left_q, right_q);
        let mut rules = Vec::new();
        product.step_topdown(&parent, &mut |symbol, children| {
            rules.push((symbol, children.to_vec()));
        });

        assert_eq!(rules, vec![(a, Vec::new())]);
    }
}
