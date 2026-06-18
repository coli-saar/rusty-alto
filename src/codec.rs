//! Output codecs: render algebra values back to their textual representation.
//!
//! An [`OutputCodec`] is keyed on the *value type* and takes an immutable
//! [`Signature`] (every algebra exposes one via [`Algebra::signature`](crate::Algebra::signature)),
//! so codecs are decoupled from any concrete algebra. This mirrors Alto's output-codec layer.

use crate::{Signature, Symbol};
use std::fmt;

/// Render an algebra value of type `V` as text.
pub trait OutputCodec<V: ?Sized> {
    /// Encode `value` into its textual representation. `signature` resolves symbol
    /// ids to their external labels when the codec needs them.
    fn encode(&self, signature: &Signature, value: &V) -> String;
}

/// Codec for self-describing values: renders via the value's [`Display`](fmt::Display) impl.
///
/// Suitable for algebras whose value is a stand-alone term (e.g. a tree algebra).
#[derive(Clone, Copy, Debug, Default)]
pub struct DisplayCodec;

impl<V: fmt::Display + ?Sized> OutputCodec<V> for DisplayCodec {
    fn encode(&self, _signature: &Signature, value: &V) -> String {
        value.to_string()
    }
}

/// Codec for a sequence of word symbols: resolves each symbol and joins with spaces.
///
/// Used by [`StringAlgebra`](crate::StringAlgebra) (value `Vec<Symbol>`); depends only on
/// [`Symbol`] and [`Signature`], not on the algebra.
#[derive(Clone, Copy, Debug, Default)]
pub struct SpaceJoinCodec;

impl OutputCodec<Vec<Symbol>> for SpaceJoinCodec {
    #[allow(clippy::ptr_arg)] // value type is fixed by the `OutputCodec<Vec<Symbol>>` impl
    fn encode(&self, signature: &Signature, value: &Vec<Symbol>) -> String {
        let mut out = String::new();
        for (i, symbol) in value.iter().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            out.push_str(signature.resolve(*symbol));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_codec_uses_display() {
        let sig = Signature::new();
        assert_eq!(DisplayCodec.encode(&sig, &2u8), "2");
        assert_eq!(DisplayCodec.encode(&sig, "hi"), "hi");
    }

    #[test]
    fn space_join_codec_resolves_and_joins() {
        let mut sig = Signature::new();
        let the = sig.intern("the".to_owned(), 0).unwrap();
        let woman = sig.intern("woman".to_owned(), 0).unwrap();

        assert_eq!(SpaceJoinCodec.encode(&sig, &vec![the, woman]), "the woman");
        assert_eq!(SpaceJoinCodec.encode(&sig, &vec![]), "");
        assert_eq!(SpaceJoinCodec.encode(&sig, &vec![the]), "the");
    }
}
