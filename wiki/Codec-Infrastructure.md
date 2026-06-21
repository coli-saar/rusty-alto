# Codec infrastructure

rusty-alto uses typed codec registries so frontends can discover formats
without losing the Rust type of the object being read or written.

## Input codecs

`InputCodec<T>` reads a stream or path and produces `T`. The standard
`InputCodecRegistry` contains:

| Extension | Result |
| --- | --- |
| `.irtg` | `Irtg` |
| `.tag` | `Irtg` |
| `.auto` | `ExplicitWithSignature` |

Codecs are looked up first by exact result type and then by metadata name or
filename extension. A frontend opening a grammar asks only for
`codecs_for::<Irtg>()`, so its file chooser naturally offers `.irtg` and
`.tag`, but not `.auto`.

Path reading is distinct from anonymous stream reading because some formats
need path context. In particular, the Tulipac codec resolves relative
`#include` directives against the including file.

`.auto` returns `ExplicitWithSignature` rather than bare `Explicit`. The
wrapper preserves the terminal signature and state names present in the file;
`Explicit` remains a compact numeric automaton that can be derived without
copying signatures.

## Output codecs and visualization

`OutputCodec<V>` consumes an algebra's standalone public value type. The
`OutputCodecRegistry` stores textual codecs by exact `V`; any algebra with that
value type gets the same Copy/export formats.

Each algebra separately constructs one preferred display codec.
`Algebra::visualize` returns a `VisualRepresentation`, currently text, tree, or
feature structure. The GUI owns the final widget layout and interaction.

## Laziness

Metadata lookup never runs a codec. A GUI should:

1. Build file filters or Copy menus from `CodecMetadata`.
2. Read a selected file only after the user chooses it.
3. Keep the derivation tree as the primary language-enumeration object.
4. Evaluate an interpretation only when its tab is displayed or copied.
5. Invoke only the selected output codec.

The detailed API and implementation checklist are maintained in
[`docs/codec-infrastructure.md`](https://github.com/coli-saar/rusty-alto/blob/main/docs/codec-infrastructure.md).
