//! Typed input and output codecs.
//!
//! An [`InputCodec`] is keyed on the type it produces. [`InputCodecRegistry`]
//! can therefore offer several formats for one semantic result, such as
//! `.irtg` and `.tag` for [`Irtg`], without mixing in codecs for other types.
//!
//! An [`OutputCodec`] is keyed on the public value type. Public values are
//! self-contained (no interner ids), so codecs need no
//! [`Signature`](crate::Signature). An algebra owns one codec that produces
//! its preferred [`VisualRepresentation`]; independent textual codecs are
//! stored in an [`OutputCodecRegistry`] and are available to every algebra
//! with the same public value type.
//!
//! Registry lookup is by exact Rust type. Listing codecs only returns their metadata and does not
//! encode a value. A GUI can therefore evaluate a derivation on demand, call
//! [`Algebra::visualize`](crate::Algebra::visualize) for display, list the matching textual codecs
//! for a Copy menu, and invoke only the codec selected by the user.

use crate::{
    ExplicitWithSignature, FeatureStructure, Irtg, TagStringValue, TreeValue,
    codecs::TulipacInputCodec,
};
use std::{
    any::{Any, TypeId},
    collections::HashMap,
    error::Error,
    fmt, fs,
    io::{Cursor, Read},
    path::Path,
};

/// Failure while selecting or invoking an input codec.
#[derive(Debug)]
pub enum InputCodecError {
    /// Reading the input failed.
    Io(std::io::Error),
    /// Input bytes were not valid UTF-8.
    Utf8(std::string::FromUtf8Error),
    /// A concrete codec rejected the input.
    Codec(Box<dyn Error + Send + Sync>),
    /// A path has no usable filename extension.
    MissingExtension,
    /// No codec for the requested result type has this name or extension.
    UnknownCodec(String),
}

impl InputCodecError {
    /// Wrap a concrete codec error while retaining it as the error source.
    pub fn codec(error: impl Error + Send + Sync + 'static) -> Self {
        Self::Codec(Box::new(error))
    }
}

impl fmt::Display for InputCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "failed to read codec input: {error}"),
            Self::Utf8(error) => write!(f, "codec input is not valid UTF-8: {error}"),
            Self::Codec(error) => error.fmt(f),
            Self::MissingExtension => f.write_str("input path has no filename extension"),
            Self::UnknownCodec(format) => write!(f, "no input codec registered for {format:?}"),
        }
    }
}

impl Error for InputCodecError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Utf8(error) => Some(error),
            Self::Codec(error) => Some(&**error),
            Self::MissingExtension | Self::UnknownCodec(_) => None,
        }
    }
}

impl From<std::io::Error> for InputCodecError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<std::string::FromUtf8Error> for InputCodecError {
    fn from(error: std::string::FromUtf8Error) -> Self {
        Self::Utf8(error)
    }
}

/// Decode a byte stream into a value of type `T`.
pub trait InputCodec<T>: Send + Sync {
    /// Return static codec metadata. This must not read or parse input.
    fn metadata(&self) -> &'static CodecMetadata;

    /// Decode a byte stream.
    fn read(&self, reader: &mut dyn Read) -> Result<T, InputCodecError>;

    /// Decode a file. Codecs with path-relative semantics may override this method.
    fn read_path(&self, path: &Path) -> Result<T, InputCodecError> {
        let mut file = fs::File::open(path)?;
        self.read(&mut file)
    }

    /// Decode UTF-8 text.
    fn decode(&self, input: &str) -> Result<T, InputCodecError> {
        self.read(&mut Cursor::new(input.as_bytes()))
    }

    /// Decode an in-memory byte sequence.
    fn read_bytes(&self, input: &[u8]) -> Result<T, InputCodecError> {
        self.read(&mut Cursor::new(input))
    }
}

/// Input codec for Alto's textual `.irtg` format.
#[derive(Clone, Copy, Debug, Default)]
pub struct IrtgInputCodec;

impl InputCodec<crate::Irtg> for IrtgInputCodec {
    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "irtg",
            description: "IRTG grammar",
            extension: Some("irtg"),
        };
        &METADATA
    }

    fn read(&self, reader: &mut dyn Read) -> Result<crate::Irtg, InputCodecError> {
        crate::parse_irtg(reader).map_err(InputCodecError::codec)
    }
}

/// Input codec for Alto's textual `.auto` tree-automaton format.
#[derive(Clone, Copy, Debug, Default)]
pub struct AltoTreeAutomatonInputCodec;

impl InputCodec<ExplicitWithSignature> for AltoTreeAutomatonInputCodec {
    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "auto",
            description: "Tree automaton",
            extension: Some("auto"),
        };
        &METADATA
    }

    fn read(&self, reader: &mut dyn Read) -> Result<ExplicitWithSignature, InputCodecError> {
        let input = read_utf8(reader)?;
        crate::parse_alto(&input).map_err(InputCodecError::codec)
    }
}

fn read_utf8(reader: &mut dyn Read) -> Result<String, InputCodecError> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    String::from_utf8(bytes).map_err(InputCodecError::Utf8)
}

/// Static information describing an output codec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodecMetadata {
    /// Stable programmatic codec name.
    pub name: &'static str,
    /// Human-readable description suitable for menus.
    pub description: &'static str,
    /// Conventional filename extension, without a leading dot.
    pub extension: Option<&'static str>,
}

/// Thread-safe input codec trait object stored by [`InputCodecRegistry`].
pub type RegisteredInputCodec<T> = dyn InputCodec<T> + Send + Sync;

/// Error returned when an input-codec registration conflicts with an existing codec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputCodecRegistryError {
    /// Two codecs for the same result type use the same normalized name.
    DuplicateName(String),
    /// Two codecs for the same result type use the same normalized extension.
    DuplicateExtension(String),
}

impl fmt::Display for InputCodecRegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateName(name) => {
                write!(f, "duplicate input codec name {name:?} for one result type")
            }
            Self::DuplicateExtension(extension) => write!(
                f,
                "duplicate input codec extension {extension:?} for one result type"
            ),
        }
    }
}

impl Error for InputCodecRegistryError {}

/// Registry of input codecs, keyed first by exact result type and then by codec metadata.
#[derive(Default)]
pub struct InputCodecRegistry {
    codecs: HashMap<TypeId, Box<dyn Any + Send + Sync>>,
}

impl InputCodecRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create the registry containing rusty-alto's built-in file formats.
    pub fn standard() -> Self {
        let mut registry = Self::new();
        registry
            .register::<Irtg, _>(IrtgInputCodec)
            .expect("built-in input codec metadata is unique");
        registry
            .register::<Irtg, _>(TulipacInputCodec)
            .expect("built-in input codec metadata is unique");
        registry
            .register::<ExplicitWithSignature, _>(AltoTreeAutomatonInputCodec)
            .expect("built-in input codec metadata is unique");
        registry
    }

    /// Register a codec for the exact result type `T`.
    pub fn register<T: 'static, C>(&mut self, codec: C) -> Result<(), InputCodecRegistryError>
    where
        C: InputCodec<T> + 'static,
    {
        let codecs = self
            .codecs
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Box::new(Vec::<Box<RegisteredInputCodec<T>>>::new()))
            .downcast_mut::<Vec<Box<RegisteredInputCodec<T>>>>()
            .expect("a TypeId uniquely identifies its codec vector");
        let metadata = codec.metadata();
        let name = normalize_name(metadata.name);
        if codecs
            .iter()
            .any(|registered| normalize_name(registered.metadata().name) == name)
        {
            return Err(InputCodecRegistryError::DuplicateName(name));
        }
        if let Some(extension) = metadata.extension.map(normalize_extension)
            && codecs.iter().any(|registered| {
                registered
                    .metadata()
                    .extension
                    .map(normalize_extension)
                    .as_deref()
                    == Some(extension.as_str())
            })
        {
            return Err(InputCodecRegistryError::DuplicateExtension(extension));
        }
        codecs.push(Box::new(codec));
        Ok(())
    }

    /// Return all codecs registered for the exact result type `T`.
    pub fn codecs_for<T: 'static>(&self) -> &[Box<RegisteredInputCodec<T>>] {
        self.codecs
            .get(&TypeId::of::<T>())
            .and_then(|codecs| codecs.downcast_ref::<Vec<Box<RegisteredInputCodec<T>>>>())
            .map_or(&[], Vec::as_slice)
    }

    /// Find a codec for `T` by its case-insensitive metadata name.
    pub fn codec_for_name<T: 'static>(
        &self,
        name: &str,
    ) -> Result<&RegisteredInputCodec<T>, InputCodecError> {
        let normalized = normalize_name(name);
        self.codecs_for::<T>()
            .iter()
            .find(|codec| normalize_name(codec.metadata().name) == normalized)
            .map(Box::as_ref)
            .ok_or_else(|| InputCodecError::UnknownCodec(name.to_owned()))
    }

    /// Find a codec for `T` by filename extension.
    pub fn codec_for_extension<T: 'static>(
        &self,
        extension: &str,
    ) -> Result<&RegisteredInputCodec<T>, InputCodecError> {
        let normalized = normalize_extension(extension);
        self.codecs_for::<T>()
            .iter()
            .find(|codec| {
                codec
                    .metadata()
                    .extension
                    .map(normalize_extension)
                    .as_deref()
                    == Some(normalized.as_str())
            })
            .map(Box::as_ref)
            .ok_or_else(|| InputCodecError::UnknownCodec(extension.to_owned()))
    }

    /// Find a codec for `T` from the extension of `path`.
    pub fn codec_for_path<T: 'static>(
        &self,
        path: &Path,
    ) -> Result<&RegisteredInputCodec<T>, InputCodecError> {
        let extension = path
            .extension()
            .and_then(|extension| extension.to_str())
            .ok_or(InputCodecError::MissingExtension)?;
        self.codec_for_extension(extension)
    }
}

fn normalize_name(name: &str) -> String {
    name.trim().to_ascii_lowercase()
}

fn normalize_extension(extension: &str) -> String {
    extension
        .trim()
        .trim_start_matches('.')
        .to_ascii_lowercase()
}

/// Encode a public algebra value of type `V`.
///
/// Textual codecs use `Output = String`; algebra-owned display codecs use
/// `Output = VisualRepresentation`.
pub trait OutputCodec<V: ?Sized> {
    /// The representation produced by this codec.
    type Output;

    /// Return static codec metadata. This must not inspect or encode a value.
    fn metadata(&self) -> &'static CodecMetadata;

    /// Encode `value`.
    fn encode(&self, value: &V) -> Self::Output;
}

/// Codec for self-describing values: renders via the value's [`Display`](fmt::Display) impl.
///
/// Suitable for values that already carry their own labels (e.g. a tree algebra's value).
#[derive(Clone, Copy, Debug, Default)]
pub struct DisplayCodec;

impl<V: fmt::Display + ?Sized> OutputCodec<V> for DisplayCodec {
    type Output = String;

    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "display",
            description: "Default string representation",
            extension: Some("txt"),
        };
        &METADATA
    }

    fn encode(&self, value: &V) -> Self::Output {
        value.to_string()
    }
}

/// Codec for a word sequence: joins the words with single spaces.
///
/// Used by [`StringAlgebra`](crate::StringAlgebra) (public value `Vec<String>`).
#[derive(Clone, Copy, Debug, Default)]
pub struct SpaceJoinCodec;

impl OutputCodec<Vec<String>> for SpaceJoinCodec {
    type Output = String;

    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "string",
            description: "Space-separated string",
            extension: Some("txt"),
        };
        &METADATA
    }

    #[allow(clippy::ptr_arg)] // value type is fixed by the `OutputCodec<Vec<String>>` impl
    fn encode(&self, value: &Vec<String>) -> Self::Output {
        value.join(" ")
    }
}

/// GUI-neutral preferred representation of an algebra value.
#[derive(Debug)]
pub enum VisualRepresentation {
    /// Plain textual display.
    Text(String),
    /// A structured tree.
    Tree(TreeValue),
    /// A structured feature structure.
    FeatureStructure(FeatureStructure),
}

/// Adapt any textual codec into a display codec.
#[derive(Clone, Copy, Debug, Default)]
pub struct TextVisualizationCodec<C> {
    codec: C,
}

impl<C> TextVisualizationCodec<C> {
    /// Wrap `codec` as a text visualization codec.
    pub fn new(codec: C) -> Self {
        Self { codec }
    }
}

impl<V: ?Sized, C> OutputCodec<V> for TextVisualizationCodec<C>
where
    C: OutputCodec<V, Output = String>,
{
    type Output = VisualRepresentation;

    fn metadata(&self) -> &'static CodecMetadata {
        self.codec.metadata()
    }

    fn encode(&self, value: &V) -> Self::Output {
        VisualRepresentation::Text(self.codec.encode(value))
    }
}

/// Display codec that preserves tree structure.
#[derive(Clone, Copy, Debug, Default)]
pub struct TreeVisualizationCodec;

impl OutputCodec<TreeValue> for TreeVisualizationCodec {
    type Output = VisualRepresentation;

    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "tree-visualization",
            description: "Tree visualization",
            extension: None,
        };
        &METADATA
    }

    fn encode(&self, value: &TreeValue) -> Self::Output {
        VisualRepresentation::Tree(value.clone())
    }
}

/// Display codec that preserves feature-structure topology.
#[derive(Clone, Copy, Debug, Default)]
pub struct FeatureStructureVisualizationCodec;

impl OutputCodec<FeatureStructure> for FeatureStructureVisualizationCodec {
    type Output = VisualRepresentation;

    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "feature-structure-visualization",
            description: "Feature-structure visualization",
            extension: None,
        };
        &METADATA
    }

    fn encode(&self, value: &FeatureStructure) -> Self::Output {
        VisualRepresentation::FeatureStructure(value.clone())
    }
}

/// Thread-safe textual codec trait object stored by [`OutputCodecRegistry`].
pub type TextOutputCodec<V> = dyn OutputCodec<V, Output = String> + Send + Sync;

/// Failure while selecting a textual output codec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OutputCodecError {
    /// No codec for the value's exact public type has this name.
    UnknownCodec(String),
}

impl fmt::Display for OutputCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownCodec(name) => write!(f, "no output codec registered with name {name:?}"),
        }
    }
}

impl Error for OutputCodecError {}

/// Registry of independent textual output codecs, keyed by exact public value type.
///
/// The registry's `Any` storage is only a heterogeneous type map. After lookup,
/// callers receive ordinary typed [`OutputCodec<V>`] trait objects.
#[derive(Default)]
pub struct OutputCodecRegistry {
    codecs: HashMap<TypeId, Box<dyn Any + Send + Sync>>,
}

impl OutputCodecRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create the standard registry for rusty-alto's built-in public value types.
    pub fn standard() -> Self {
        let mut registry = Self::new();
        registry.register::<Vec<String>, _>(SpaceJoinCodec);
        registry.register::<TagStringValue<String>, _>(DisplayCodec);
        registry.register::<TreeValue, _>(DisplayCodec);
        registry.register::<FeatureStructure, _>(DisplayCodec);
        registry
    }

    /// Register a textual codec for the exact public value type `V`.
    pub fn register<V: 'static, C>(&mut self, codec: C)
    where
        C: OutputCodec<V, Output = String> + Send + Sync + 'static,
    {
        self.codecs
            .entry(TypeId::of::<V>())
            .or_insert_with(|| Box::new(Vec::<Box<TextOutputCodec<V>>>::new()))
            .downcast_mut::<Vec<Box<TextOutputCodec<V>>>>()
            .expect("a TypeId uniquely identifies its codec vector")
            .push(Box::new(codec));
    }

    /// Return textual codecs registered for the exact public value type `V`.
    ///
    /// Accessing this slice or codec metadata does not invoke encoding.
    pub fn codecs_for<V: 'static>(&self) -> &[Box<TextOutputCodec<V>>] {
        self.codecs
            .get(&TypeId::of::<V>())
            .and_then(|codecs| codecs.downcast_ref::<Vec<Box<TextOutputCodec<V>>>>())
            .map_or(&[], Vec::as_slice)
    }

    /// Find a textual codec by its case-insensitive metadata name.
    pub fn codec_for_name<V: 'static>(
        &self,
        name: &str,
    ) -> Result<&TextOutputCodec<V>, OutputCodecError> {
        let normalized = normalize_name(name);
        self.codecs_for::<V>()
            .iter()
            .find(|codec| normalize_name(codec.metadata().name) == normalized)
            .map(Box::as_ref)
            .ok_or_else(|| OutputCodecError::UnknownCodec(name.to_owned()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    #[derive(Clone)]
    struct CountingInputCodec {
        calls: Arc<AtomicUsize>,
        metadata: &'static CodecMetadata,
    }

    impl InputCodec<u32> for CountingInputCodec {
        fn metadata(&self) -> &'static CodecMetadata {
            self.metadata
        }

        fn read(&self, reader: &mut dyn Read) -> Result<u32, InputCodecError> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            let input = read_utf8(reader)?;
            input.trim().parse().map_err(InputCodecError::codec)
        }
    }

    static COUNTING_METADATA: CodecMetadata = CodecMetadata {
        name: "count",
        description: "Count",
        extension: Some("count"),
    };

    static DUPLICATE_NAME_METADATA: CodecMetadata = CodecMetadata {
        name: "COUNT",
        description: "Duplicate count",
        extension: Some("other"),
    };

    static DUPLICATE_EXTENSION_METADATA: CodecMetadata = CodecMetadata {
        name: "other",
        description: "Duplicate extension",
        extension: Some(".COUNT"),
    };

    #[test]
    fn standard_input_registry_is_partitioned_by_exact_result_type() {
        let registry = InputCodecRegistry::standard();
        let irtg_extensions = registry
            .codecs_for::<Irtg>()
            .iter()
            .filter_map(|codec| codec.metadata().extension)
            .collect::<Vec<_>>();
        assert_eq!(irtg_extensions, vec!["irtg", "tag"]);

        let auto_extensions = registry
            .codecs_for::<ExplicitWithSignature>()
            .iter()
            .filter_map(|codec| codec.metadata().extension)
            .collect::<Vec<_>>();
        assert_eq!(auto_extensions, vec!["auto"]);
        assert!(registry.codecs_for::<u32>().is_empty());
    }

    #[test]
    fn input_registry_lookup_is_normalized_and_lazy() {
        let calls = Arc::new(AtomicUsize::new(0));
        let mut registry = InputCodecRegistry::new();
        registry
            .register::<u32, _>(CountingInputCodec {
                calls: calls.clone(),
                metadata: &COUNTING_METADATA,
            })
            .unwrap();

        assert_eq!(
            registry
                .codec_for_name::<u32>("COUNT")
                .unwrap()
                .metadata()
                .name,
            "count"
        );
        assert_eq!(
            registry
                .codec_for_extension::<u32>(".CoUnT")
                .unwrap()
                .metadata()
                .extension,
            Some("count")
        );
        assert_eq!(
            registry
                .codec_for_path::<u32>(Path::new("value.COUNT"))
                .unwrap()
                .metadata()
                .name,
            "count"
        );
        assert_eq!(calls.load(Ordering::Relaxed), 0);
        assert_eq!(
            registry
                .codec_for_extension::<u32>("count")
                .unwrap()
                .decode("17")
                .unwrap(),
            17
        );
        assert_eq!(calls.load(Ordering::Relaxed), 1);
        assert!(matches!(
            registry.codec_for_path::<u32>(Path::new("no-extension")),
            Err(InputCodecError::MissingExtension)
        ));
        assert!(matches!(
            registry.codec_for_extension::<u32>("unknown"),
            Err(InputCodecError::UnknownCodec(_))
        ));
    }

    #[test]
    fn input_registry_rejects_duplicate_names_and_extensions_per_type() {
        let calls = Arc::new(AtomicUsize::new(0));
        let mut registry = InputCodecRegistry::new();
        registry
            .register::<u32, _>(CountingInputCodec {
                calls: calls.clone(),
                metadata: &COUNTING_METADATA,
            })
            .unwrap();
        assert_eq!(
            registry.register::<u32, _>(CountingInputCodec {
                calls: calls.clone(),
                metadata: &DUPLICATE_NAME_METADATA,
            }),
            Err(InputCodecRegistryError::DuplicateName("count".to_owned()))
        );
        assert_eq!(
            registry.register::<u32, _>(CountingInputCodec {
                calls,
                metadata: &DUPLICATE_EXTENSION_METADATA,
            }),
            Err(InputCodecRegistryError::DuplicateExtension(
                "count".to_owned()
            ))
        );
        assert!(
            registry.register::<u64, _>(U64InputCodec).is_ok(),
            "the same metadata is allowed for another result type"
        );
    }

    struct U64InputCodec;

    impl InputCodec<u64> for U64InputCodec {
        fn metadata(&self) -> &'static CodecMetadata {
            &COUNTING_METADATA
        }

        fn read(&self, reader: &mut dyn Read) -> Result<u64, InputCodecError> {
            read_utf8(reader)?
                .trim()
                .parse()
                .map_err(InputCodecError::codec)
        }
    }

    #[test]
    fn built_in_input_codecs_decode_expected_types() {
        let irtg = IrtgInputCodec
            .decode(
                "interpretation string: de.up.ling.irtg.algebra.StringAlgebra\n\
                 S! -> word\n[string] hello\n",
            )
            .unwrap();
        assert!(irtg.interpretation_ref("string").is_some());

        let auto = AltoTreeAutomatonInputCodec
            .decode("S! -> f(A)\nA -> a")
            .unwrap();
        assert_eq!(auto.states.resolve(crate::StateId(0)), "S");
        assert!(auto.signature.get("f").is_some());
        assert_eq!(auto.automaton.rules().count(), 2);
    }

    #[test]
    fn display_codec_uses_display() {
        assert_eq!(DisplayCodec.encode(&2u8), "2");
        assert_eq!(DisplayCodec.encode("hi"), "hi");
        assert_eq!(
            <DisplayCodec as OutputCodec<u8>>::metadata(&DisplayCodec).extension,
            Some("txt")
        );
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

    #[test]
    fn text_visualization_wraps_text() {
        let codec = TextVisualizationCodec::new(SpaceJoinCodec);
        let value = vec!["hello".to_owned(), "world".to_owned()];
        assert!(matches!(
            codec.encode(&value),
            VisualRepresentation::Text(text) if text == "hello world"
        ));
    }

    #[test]
    fn registry_uses_exact_types_and_does_not_encode_during_lookup() {
        struct CountingCodec(Arc<AtomicUsize>);

        impl OutputCodec<u32> for CountingCodec {
            type Output = String;

            fn metadata(&self) -> &'static CodecMetadata {
                static METADATA: CodecMetadata = CodecMetadata {
                    name: "counting",
                    description: "Counting codec",
                    extension: Some("count"),
                };
                &METADATA
            }

            fn encode(&self, value: &u32) -> Self::Output {
                self.0.fetch_add(1, Ordering::Relaxed);
                value.to_string()
            }
        }

        let calls = Arc::new(AtomicUsize::new(0));
        let mut registry = OutputCodecRegistry::new();
        registry.register::<u32, _>(CountingCodec(calls.clone()));

        let codecs = registry.codecs_for::<u32>();
        assert_eq!(codecs.len(), 1);
        assert_eq!(codecs[0].metadata().extension, Some("count"));
        assert!(registry.codecs_for::<u64>().is_empty());
        assert_eq!(calls.load(Ordering::Relaxed), 0);

        assert_eq!(registry.codec_for_name::<u32>("COUNTING").unwrap().encode(&7), "7");
        assert_eq!(calls.load(Ordering::Relaxed), 1);
        assert!(matches!(
            registry.codec_for_name::<u64>("counting"),
            Err(OutputCodecError::UnknownCodec(_))
        ));
    }
}
