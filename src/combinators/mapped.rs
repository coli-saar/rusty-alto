use crate::{BottomUpTa, DetBottomUpTa, IndexedBottomUpTa, Symbol};

/// Symbol-renaming view of an automaton.
///
/// `Mapped` is useful when an automaton should be queried under a different
/// external signature. The mapping is applied to every input symbol before the
/// wrapped automaton is queried. States are unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mapped<A, F> {
    /// Wrapped automaton.
    pub inner: A,
    /// Function from external symbol IDs to the wrapped automaton's symbol IDs.
    pub map: F,
}

impl<A, F> Mapped<A, F> {
    /// Create a mapped view.
    pub fn new(inner: A, map: F) -> Self {
        Self { inner, map }
    }
}

impl<A, F> BottomUpTa for Mapped<A, F>
where
    A: BottomUpTa,
    F: Fn(Symbol) -> Symbol,
{
    type State = A::State;

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        self.inner.step((self.map)(f), children, out);
    }

    fn is_accepting(&self, q: &Self::State) -> bool {
        self.inner.is_accepting(q)
    }
}

impl<A, F> DetBottomUpTa for Mapped<A, F>
where
    A: DetBottomUpTa,
    F: Fn(Symbol) -> Symbol,
{
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        self.inner.step_det((self.map)(f), children)
    }
}

impl<A, F> IndexedBottomUpTa for Mapped<A, F>
where
    A: IndexedBottomUpTa,
    F: Fn(Symbol) -> Symbol,
{
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &Self::State,
        out: &mut dyn FnMut(&[Self::State], Self::State),
    ) {
        self.inner
            .step_partial((self.map)(f), position, state_at_position, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, StateId};

    #[test]
    fn maps_symbols_for_deterministic_steps() {
        let external_a = Symbol(7);
        let inner_a = Symbol(0);
        let mut builder = ExplicitBuilder::new();
        let q = builder.new_state();
        builder.add_rule(inner_a, vec![], q);
        let mapped = Mapped::new(
            builder.build(),
            move |f| {
                if f == external_a { inner_a } else { f }
            },
        );

        assert_eq!(mapped.step_det(external_a, &[]), Some(q));
    }

    #[test]
    fn maps_symbols_for_indexed_steps() {
        let external_f = Symbol(8);
        let inner_f = Symbol(1);
        let mut builder = ExplicitBuilder::new();
        let q0 = builder.new_state();
        let q1 = builder.new_state();
        builder.add_rule(inner_f, vec![q0], q1);
        let mapped = Mapped::new(
            builder.build(),
            move |f| {
                if f == external_f { inner_f } else { f }
            },
        );

        let mut found = Vec::<(Vec<StateId>, StateId)>::new();
        mapped.step_partial(external_f, 0, &q0, &mut |children, result| {
            found.push((children.to_vec(), result));
        });

        assert_eq!(found, vec![(vec![q0], q1)]);
    }
}
