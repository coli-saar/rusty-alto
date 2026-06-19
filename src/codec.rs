//! Typed input and output codecs.
//!
//! An [`OutputCodec`] is keyed on the public value type. Public values are self-contained (no
//! interner ids), so codecs need no [`Signature`](crate::Signature). This mirrors Alto's
//! output-codec layer.

use std::{fmt, io::Read};

/// Decode a textual or byte-stream representation into a value.
pub trait InputCodec<T> {
    /// Codec-specific failure.
    type Error;

    /// Decode a UTF-8 string.
    fn decode(&self, input: &str) -> Result<T, Self::Error>;

    /// Read an entire byte stream as UTF-8 and decode it.
    fn read<R: Read>(&self, mut reader: R) -> Result<T, InputCodecReadError<Self::Error>> {
        let mut bytes = Vec::new();
        reader
            .read_to_end(&mut bytes)
            .map_err(InputCodecReadError::Io)?;
        let input = String::from_utf8(bytes).map_err(InputCodecReadError::Utf8)?;
        self.decode(&input).map_err(InputCodecReadError::Codec)
    }
}

/// Stream-level errors shared by input codecs.
#[derive(Debug)]
pub enum InputCodecReadError<E> {
    /// Reading the byte stream failed.
    Io(std::io::Error),
    /// The stream was not valid UTF-8.
    Utf8(std::string::FromUtf8Error),
    /// The codec rejected otherwise valid UTF-8 input.
    Codec(E),
}

impl<E: fmt::Display> fmt::Display for InputCodecReadError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "failed to read codec input: {error}"),
            Self::Utf8(error) => write!(f, "codec input is not valid UTF-8: {error}"),
            Self::Codec(error) => error.fmt(f),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for InputCodecReadError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Utf8(error) => Some(error),
            Self::Codec(error) => Some(error),
        }
    }
}

/// Input codec for Alto's textual `.irtg` format.
#[derive(Clone, Copy, Debug, Default)]
pub struct IrtgInputCodec;

impl InputCodec<crate::Irtg> for IrtgInputCodec {
    type Error = crate::IrtgError;

    fn decode(&self, input: &str) -> Result<crate::Irtg, Self::Error> {
        crate::parse_irtg(input.as_bytes())
    }
}

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
