//! Output codecs: render an algebra's public value to its textual representation.
//!
//! An [`OutputCodec`] is keyed on the public value type. Public values are self-contained (no
//! interner ids), so codecs need no [`Signature`](crate::Signature). This mirrors Alto's
//! output-codec layer.

use std::fmt;

/// Render a public algebra value of type `V` as text.
pub trait OutputCodec<V: ?Sized> {
    /// Encode `value` into its textual representation.
    fn encode(&self, value: &V) -> String;
}

/// Codec for self-describing values: renders via the value's [`Display`](fmt::Display) impl.
///
/// Suitable for values that already carry their own labels (e.g. a tree algebra's value).
#[derive(Clone, Copy, Debug, Default)]
pub struct DisplayCodec;

impl<V: fmt::Display + ?Sized> OutputCodec<V> for DisplayCodec {
    fn encode(&self, value: &V) -> String {
        value.to_string()
    }
}

/// Codec for a word sequence: joins the words with single spaces.
///
/// Used by [`StringAlgebra`](crate::StringAlgebra) (public value `Vec<String>`).
#[derive(Clone, Copy, Debug, Default)]
pub struct SpaceJoinCodec;

impl OutputCodec<Vec<String>> for SpaceJoinCodec {
    #[allow(clippy::ptr_arg)] // value type is fixed by the `OutputCodec<Vec<String>>` impl
    fn encode(&self, value: &Vec<String>) -> String {
        value.join(" ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_codec_uses_display() {
        assert_eq!(DisplayCodec.encode(&2u8), "2");
        assert_eq!(DisplayCodec.encode("hi"), "hi");
    }

    #[test]
    fn space_join_codec_joins_words() {
        assert_eq!(
            SpaceJoinCodec.encode(&vec!["the".to_owned(), "woman".to_owned()]),
            "the woman"
        );
        assert_eq!(SpaceJoinCodec.encode(&vec![]), "");
        assert_eq!(SpaceJoinCodec.encode(&vec!["the".to_owned()]), "the");
    }
}
