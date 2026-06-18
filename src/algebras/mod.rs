//! Algebra interfaces and decomposition automata.

mod string;
mod tree;

use crate::{BottomUpTa, DetBottomUpTa, Signature, Symbol};
use rusty_tree::tree::{Tree, TreeArena};
use std::hash::Hash;

pub use string::{
    SentenceSxHeuristic, Span, StringAlgebra, StringDecompositionAutomaton, UniversalSxHeuristic,
};
pub use tree::{APPEND_SYMBOL, Binarizing, TreeAlgebra, TreeValue};
pub(crate) use string::{SpanProductSibling, SpanProductSiblingFinder};

/// Algebra over a domain of values.
///
/// An algebra distinguishes two value types:
/// - [`InternalValue`](Self::InternalValue): the efficient, ID/handle-based representation the
///   algebra uses internally (for [`evaluate`](Self::evaluate) and decomposition);
/// - [`Value`](Self::Value): the standalone *public* value produced by
///   [`evaluate_term`](Self::evaluate_term) for output (e.g. `Vec<String>` rather than
///   `Vec<Symbol>`), hiding the auxiliary interners from consumers.
///
/// The default decomposition automaton uses internal values as states and computes parent
/// states by applying the algebra operation bottom-up.
pub trait Algebra {
    /// Efficient internal value domain used by [`evaluate`](Self::evaluate) and decomposition.
    type InternalValue: Clone + Eq + Hash;

    /// Standalone public value produced for output by [`evaluate_term`](Self::evaluate_term).
    type Value;

    /// Error returned when parsing a textual object representation.
    type ParseError;

    /// Return the operation signature used by this algebra.
    fn signature(&self) -> &Signature;

    /// Evaluate an operation over child internal values.
    ///
    /// Return `None` when the operation is undefined for the given children.
    fn evaluate(
        &self,
        symbol: Symbol,
        children: &[Self::InternalValue],
    ) -> Option<Self::InternalValue>;

    /// Parse a textual representation into an internal value.
    fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError>;

    /// Map an internal value to its standalone public form.
    fn to_external(&self, value: &Self::InternalValue) -> Self::Value;

    /// Evaluate a term tree bottom-up to an internal value, applying [`evaluate`](Self::evaluate)
    /// at every node (e.g. a homomorphic image produced from a derivation tree).
    ///
    /// Returns `None` if any node's operation is undefined for its children.
    fn evaluate_term_internal(
        &self,
        arena: &TreeArena<Symbol>,
        root: Tree,
    ) -> Option<Self::InternalValue> {
        let children: Vec<Self::InternalValue> = arena
            .get_children(root)
            .iter()
            .map(|&child| self.evaluate_term_internal(arena, child))
            .collect::<Option<_>>()?;
        self.evaluate(*arena.get_label(root), &children)
    }

    /// Evaluate a term tree to its public value (bottom-up [`evaluate`](Self::evaluate), then
    /// [`to_external`](Self::to_external)).
    fn evaluate_term(&self, arena: &TreeArena<Symbol>, root: Tree) -> Option<Self::Value> {
        Some(self.to_external(&self.evaluate_term_internal(arena, root)?))
    }

    /// Return whether `value` is a valid internal value.
    fn is_valid_value(&self, _value: &Self::InternalValue) -> bool {
        true
    }

    /// Build the default evaluating decomposition automaton for `value`.
    fn decompose_default(
        &self,
        value: Self::InternalValue,
    ) -> EvaluatingDecompositionAutomaton<'_, Self>
    where
        Self: Sized,
    {
        EvaluatingDecompositionAutomaton::new(self, value)
    }
}

/// Default decomposition automaton for an [`Algebra`].
pub struct EvaluatingDecompositionAutomaton<'a, A: Algebra> {
    algebra: &'a A,
    accepting: A::InternalValue,
}

impl<'a, A: Algebra> EvaluatingDecompositionAutomaton<'a, A> {
    /// Create a decomposition automaton accepting terms that evaluate to
    /// `accepting`.
    pub fn new(algebra: &'a A, accepting: A::InternalValue) -> Self {
        Self { algebra, accepting }
    }
}

impl<A: Algebra> BottomUpTa for EvaluatingDecompositionAutomaton<'_, A> {
    type State = A::InternalValue;

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        if self.algebra.signature().arity(f) != children.len() {
            return;
        }
        let Some(value) = self.algebra.evaluate(f, children) else {
            return;
        };
        if self.algebra.is_valid_value(&value) {
            out(value);
        }
    }

    fn is_accepting(&self, q: &Self::State) -> bool {
        q == &self.accepting
    }
}

impl<A: Algebra> DetBottomUpTa for EvaluatingDecompositionAutomaton<'_, A> {
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        if self.algebra.signature().arity(f) != children.len() {
            return None;
        }
        let value = self.algebra.evaluate(f, children)?;
        self.algebra.is_valid_value(&value).then_some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct Tiny {
        signature: Signature,
        zero: Symbol,
        inc: Symbol,
    }

    impl Tiny {
        fn new() -> Self {
            let mut signature = Signature::new();
            let zero = signature.intern("zero".to_owned(), 0).unwrap();
            let inc = signature.intern("inc".to_owned(), 1).unwrap();
            Self {
                signature,
                zero,
                inc,
            }
        }
    }

    impl Algebra for Tiny {
        type InternalValue = u8;
        type Value = u8;
        type ParseError = std::num::ParseIntError;

        fn signature(&self) -> &Signature {
            &self.signature
        }

        fn evaluate(
            &self,
            symbol: Symbol,
            children: &[Self::InternalValue],
        ) -> Option<Self::InternalValue> {
            match (symbol, children) {
                (s, []) if s == self.zero => Some(0),
                (s, [x]) if s == self.inc => Some(x + 1),
                _ => None,
            }
        }

        fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError> {
            input.parse()
        }

        fn to_external(&self, value: &Self::InternalValue) -> Self::Value {
            *value
        }
    }

    #[test]
    fn default_decomposition_evaluates_bottom_up() {
        let algebra = Tiny::new();
        let decomp = algebra.decompose_default(2);

        let zero = decomp.step_det(algebra.zero, &[]).unwrap();
        let one = decomp.step_det(algebra.inc, &[zero]).unwrap();
        let two = decomp.step_det(algebra.inc, &[one]).unwrap();

        assert!(!decomp.is_accepting(&one));
        assert!(decomp.is_accepting(&two));
        assert_eq!(decomp.step_det(algebra.zero, &[two]), None);
    }
}
