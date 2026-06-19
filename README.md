# rusty-alto

`rusty-alto` is a fast Rust library and command-line toolkit for weighted
bottom-up tree automata and interpreted regular tree grammars (IRTGs). It reads
grammars, automata, and corpora in formats compatible with
[Alto](https://github.com/coli-saar/alto), with the long-term goal of providing
a clean Rust API while outperforming Alto on parsing workloads.

The project is under active development. The main end-user program today is
`eval`, which parses an Alto corpus with an IRTG, extracts the best derivation,
evaluates all declared interpretations, and can report timing and Parseval
scores.

## Highlights

- Alto-compatible readers for `.auto` tree automata, `.irtg` grammars, and
  corpus files.
- A small oracle-style automaton API that supports both stored and
  on-demand transitions.
- Weighted explicit automata with lazy, arity-specialized indexes.
- Automaton combinators for products, inverse homomorphisms, symbol mappings,
  and determinization.
- Efficient condensed intersection for IRTG parsing.
- Exact one-best A* parsing with zero, outside, SX, and SXF heuristics.
- Viterbi extraction, sorted language enumeration, corpus output, and
  EVALB-style Parseval scoring.
- Trees represented with
  [`packed-term-arena`](https://crates.io/crates/packed-term-arena).

The [project wiki](https://github.com/coli-saar/rusty-alto/wiki) explains the
architecture and the main design decisions. The
[Rust API documentation](https://coli-saar.github.io/rusty-alto/rusty_alto/)
is rebuilt from `main`.

## Building

Clone the repository:

```sh
git clone https://github.com/coli-saar/rusty-alto.git
cd rusty-alto
```

Install a current stable Rust toolchain, then build and test:

```sh
rustup toolchain install stable
cargo build
cargo test
```

Use a release build for real grammars:

```sh
cargo build --release --bin eval
```

You can also build the API documentation locally:

```sh
cargo doc --no-deps --all-features --open
```

## Running `eval`

```text
eval <grammar.irtg> <corpus|-> [options]
```

Run it through Cargo:

```sh
cargo run --release --bin eval -- grammar.irtg corpus.txt \
  --algorithm astar --heuristic sx \
  --output predicted.corpus
```

Or run the compiled binary directly:

```sh
./target/release/eval grammar.irtg corpus.txt \
  --algorithm exhaustive \
  --output predicted.corpus
```

Useful options include:

| Option | Purpose |
| --- | --- |
| `-o, --output FILE` | Write the annotated output corpus to `FILE`; the default is stdout. |
| `--limit N` | Parse only the first `N` corpus instances. |
| `--algorithm exhaustive\|astar` | Select full chart construction or exact one-best A*. |
| `--heuristic zero\|outside\|sx\|sxf` | Select the A* heuristic. |
| `--jobs N` | Parse up to `N` sentences concurrently. |
| `--times FILE.csv` | Write per-sentence timing data. |
| `--astar-stats FILE.csv` | Write detailed A* counters. |
| `--parseval INTERPRETATION` | Score a constituency-tree interpretation. |

Run `cargo run --release --bin eval -- --help` for the complete interface.
See [`docs/eval.md`](docs/eval.md) for corpus formats, algorithms, heuristics,
Parseval configuration, and extended examples.

### Interactive parser

The default `rusty-alto` binary is a small interactive frontend for a grammar
with a string interpretation:

```sh
cargo run --release -- grammar.irtg
```

Enter one sentence per line; press Ctrl-D to stop. When stdin is redirected,
the binary processes one sentence per input line.

## Library sketch

```rust
use rusty_alto::{StringAlgebra, parse_irtg};

let irtg = parse_irtg(std::fs::File::open("grammar.irtg")?)?;
let english = irtg.interpretation::<StringAlgebra>("english")?;
let sentence = english.parse_object("john watches")?;
let chart = irtg.parse([english.input(sentence)])?;

if let Some(best) = chart.automaton.viterbi() {
    println!("best weight: {}", best.weight());
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

The central abstraction is `BottomUpTa`: an automaton answers a transition
query for a symbol and a tuple of child states. Explicit automata, algebra
decomposition automata, and composed automata share this interface. Optional
refinement traits expose indexed, condensed, deterministic, and top-down views
when an algorithm can use them efficiently.

## Alto compatibility and performance

The implementation is heavily inspired by Alto, including its IRTG model,
condensed inverse-homomorphism construction, indexed intersection techniques,
and language enumeration algorithms. Rust-specific data layouts, dense IDs,
lazy indexes, and specialized fast paths are used where they improve common
tree-automata and parsing workloads without narrowing the public abstraction.

Java comparison harnesses live in `tools/alto-compare/`; the corresponding
drivers are:

```sh
./scripts/compare-alto.sh
./scripts/compare-condensed-parsing.sh
./scripts/compare-intersection.sh
```

See [`docs/performance.md`](docs/performance.md) for implementation notes and
measured bottlenecks.

## Project status

Supported interpretation algebras currently include Alto string algebras and
tree-with-arities variants. String interpretations can be used as parse input;
tree interpretations are currently output-only. APIs and file-format coverage
may still change as the implementation matures.

## License

To be determined.
