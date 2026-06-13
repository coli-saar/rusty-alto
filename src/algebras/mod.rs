//! Algebra interfaces and decomposition automata.

mod string;

use crate::{BottomUpTa, DetBottomUpTa, Signature, Symbol};
use std::hash::Hash;

pub use string::{Span, StringAlgebra, StringDecompositionAutomaton};

/// Algebra over a domain of values.
///
/// An algebra evaluates operation symbols over child values. Its default
/// decomposition automaton uses algebra values as states and computes parent
/// states by applying the algebra operation bottom-up.
pub trait Algebra {
    /// Value domain of the algebra.
    type Value: Clone + Eq + Hash;

    /// Error returned when parsing a textual object representation.
    type ParseError;

    /// Return the operation signature used by this algebra.
    fn signature(&self) -> &Signature;

    /// Evaluate an operation over child values.
    ///
    /// Return `None` when the operation is undefined for the given children.
    fn evaluate(&self, symbol: Symbol, children: &[Self::Value]) -> Option<Self::Value>;

    /// Parse a textual representation of an algebra value.
    fn parse_object(&mut self, input: &str) -> Result<Self::Value, Self::ParseError>;

    /// Return whether `value` is a valid algebra value.
    fn is_valid_value(&self, _value: &Self::Value) -> bool {
        true
    }

    /// Build the default evaluating decomposition automaton for `value`.
    fn decompose_default(&self, value: Self::Value) -> EvaluatingDecompositionAutomaton<'_, Self>
    where
        Self: Sized,
    {
        EvaluatingDecompositionAutomaton::new(self, value)
    }
}

/// Default decomposition automaton for an [`Algebra`].
pub struct EvaluatingDecompositionAutomaton<'a, A: Algebra> {
    algebra: &'a A,
    accepting: A::Value,
}

impl<'a, A: Algebra> EvaluatingDecompositionAutomaton<'a, A> {
    /// Create a decomposition automaton accepting terms that evaluate to
    /// `accepting`.
    pub fn new(algebra: &'a A, accepting: A::Value) -> Self {
        Self { algebra, accepting }
    }
}

impl<A: Algebra> BottomUpTa for EvaluatingDecompositionAutomaton<'_, A> {
    type State = A::Value;

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
        type Value = u8;
        type ParseError = std::num::ParseIntError;

        fn signature(&self) -> &Signature {
            &self.signature
        }

        fn evaluate(&self, symbol: Symbol, children: &[Self::Value]) -> Option<Self::Value> {
            match (symbol, children) {
                (s, []) if s == self.zero => Some(0),
                (s, [x]) if s == self.inc => Some(x + 1),
                _ => None,
            }
        }

        fn parse_object(&mut self, input: &str) -> Result<Self::Value, Self::ParseError> {
            input.parse()
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
