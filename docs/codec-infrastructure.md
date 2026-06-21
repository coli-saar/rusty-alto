# Codec infrastructure and GUI integration

This document describes the input and output codec APIs in `rusty-alto` and the
intended integration points for a GUI.

## Shared metadata

Every codec exposes static `CodecMetadata`:

```rust
pub struct CodecMetadata {
    pub name: &'static str,
    pub description: &'static str,
    pub extension: Option<&'static str>,
}
```

Reading metadata never reads, evaluates, parses, or encodes a value. Names are
stable programmatic identifiers, descriptions are suitable for menus and file
filters, and extensions omit the leading dot.

## Input codecs

`InputCodec<T>` decodes a byte stream into a concrete result type `T`. The
trait is object-safe, so multiple formats that produce the same type can be
stored together:

```rust
let registry = InputCodecRegistry::standard();
let codec = registry.codec_for_path::<Irtg>(path)?;
let grammar = codec.read_path(path)?;
```

The standard registry contains:

| Extension | Codec | Result type |
| --- | --- | --- |
| `.irtg` | `IrtgInputCodec` | `Irtg` |
| `.tag` | `TulipacInputCodec` | `Irtg` |
| `.auto` | `AltoTreeAutomatonInputCodec` | `ExplicitWithSignature` |

Registry lookup first uses the exact Rust result type and then the normalized
codec name or extension. Consequently, looking up `.auto` as an `Irtg` fails
even though an `.auto` codec exists. Names and extensions are compared
case-insensitively, and a leading dot on an extension is ignored.

`read` is the core stream operation. `read_path` normally opens the file and
delegates to `read`, but codecs may override it when the path carries semantic
context. `TulipacInputCodec` does this so relative `#include` directives are
resolved against the including file. Reading the same input from an anonymous
stream reports that a path is required when includes occur.

All input codecs report `InputCodecError`. Concrete parse errors and I/O errors
remain available through `std::error::Error::source`.

### Why `.auto` does not return bare `Explicit`

`Explicit` is deliberately a compact numeric automaton and does not own a
terminal signature. This allows algorithms to derive one `Explicit` from
another without copying naming data.

An Alto `.auto` file contains symbol names and state names, so its complete
decoded value is `ExplicitWithSignature`:

```rust
pub struct ExplicitWithSignature {
    pub automaton: Explicit,
    pub states: Interner<String>,
    pub signature: Signature,
}
```

The wrapper belongs at the file/document boundary; algorithms can use its
`automaton` field directly.

## Output codecs and algebra visualization

`OutputCodec<V>` is keyed by the standalone public value type `V`. Textual
codecs use `Output = String`. They are registered in `OutputCodecRegistry` by
the exact Rust value type and are independent of any particular algebra:

```rust
let registry = OutputCodecRegistry::standard();
for codec in registry.codecs_for::<TreeValue>() {
    println!("{}", codec.metadata().description);
}
```

Each algebra separately owns one display codec and exposes it through
`Algebra::visualize(&value) -> VisualRepresentation`. Built-in tree and
feature-structure algebras preserve structure; string-like algebras return
`VisualRepresentation::Text`.

This distinction mirrors the two GUI jobs:

- The algebra chooses the preferred visual representation.
- Every textual codec matching the public value type is a possible Copy or
  export representation.

## GUI adaptation checklist

### Opening files

1. Construct or retain `InputCodecRegistry::standard()`.
2. Build the “Open grammar” filters from
   `registry.codecs_for::<Irtg>()`; this includes both `.irtg` and `.tag`.
3. After a file is selected, call `codec_for_path::<Irtg>(&path)`.
4. Invoke `codec.read_path(&path)` only in the loading worker.
5. Report unknown extensions and parse errors from `InputCodecError`.
6. If the GUI later opens standalone automata, use a separate
   `codecs_for::<ExplicitWithSignature>()` workflow.

Enumerating codecs and constructing filters must not open files.

### Displaying algebra values

1. Keep the derivation tree as the primary object.
2. Evaluate an interpretation only when its value is needed.
3. Call `algebra.visualize(&value)` for the selected interpretation.
4. Render the returned `VisualRepresentation` using GUI-owned layout and
   widgets.

### Copy menus

1. Determine the interpretation's public value type while still in its typed
   layer.
2. Enumerate `OutputCodecRegistry::codecs_for::<A::Value>()`.
3. Build menu labels from metadata without invoking `encode`.
4. Evaluate the algebra value and invoke only the textual codec selected by
   the user.
5. Cache values or encoded strings only if the application benefits; caching
   is not part of either codec API.
