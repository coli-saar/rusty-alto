use crate::Symbol;
use std::hash::Hash;

/// A bottom-up tree automaton queried as an oracle.
///
/// Implement this trait when you want the library to run or combine your
/// automaton. The method [`BottomUpTa::step`] receives a node symbol and the
/// states already assigned to the node's children. It reports every possible
/// state for the parent by calling the callback.
///
/// Implementations may be explicit table lookups, like [`crate::Explicit`], or
/// implicit computations, such as a type checker or derivative construction.
/// `step` should behave like a pure function: the same symbol and child states
/// should produce the same parent states, without duplicates.
pub trait BottomUpTa {
    /// State type carried by the automaton.
    ///
    /// Rich implicit automata can use application-level states here. Wrap them
    /// in [`crate::Memo`] when a dense [`crate::StateId`] representation is
    /// needed.
    type State: Clone + Eq + Hash;

    /// Report all possible parent states for `f(children...)`.
    ///
    /// Call `out(q)` once for each valid result state `q`. If no rule applies,
    /// do not call `out`. The order is not specified, but duplicate states
    /// should not be emitted.
    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State));

    /// Return whether `q` is an accepting state.
    ///
    /// A tree is accepted when the root receives at least one accepting state.
    fn is_accepting(&self, q: &Self::State) -> bool;
}

impl<A: BottomUpTa + ?Sized> BottomUpTa for &A {
    type State = A::State;

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        (**self).step(f, children, out);
    }

    fn is_accepting(&self, q: &Self::State) -> bool {
        (**self).is_accepting(q)
    }
}

/// Faster interface for deterministic bottom-up automata.
///
/// Deterministic automata have at most one parent state for each symbol and
/// child-state tuple. Implementing this trait lets [`crate::run_det`] avoid
/// allocating state sets and avoid callback overhead.
pub trait DetBottomUpTa: BottomUpTa {
    /// Return the unique result state, or `None` if no transition exists.
    ///
    /// This method must agree with [`BottomUpTa::step`]: if it returns
    /// `Some(q)`, then `step` should emit exactly `q`; if it returns `None`,
    /// then `step` should emit no states.
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State>;
}

impl<A: DetBottomUpTa + ?Sized> DetBottomUpTa for &A {
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        (**self).step_det(f, children)
    }
}
