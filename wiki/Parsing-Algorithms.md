# Choosing a parsing algorithm

`rusty-alto` offers three intersection strategies. They recognize the same
derivations, but explore the product of the grammar automaton and the input
decomposition automaton differently. The best choice depends on whether you
need a complete chart or only the best derivation, and on the shape of the
actual IRTG workload.

## Quick choice

| Goal | Recommended starting point |
| --- | --- |
| Build a complete chart for inspection, enumeration, filtering, or later processing | **Top-down condensed** |
| Compare or study bottom-up indexed intersection behavior | **Indexed condensed** |
| Find the highest-weight derivation without constructing the complete chart | **A\*** |
| Unsure | **Top-down condensed** |

These are execution strategies, not grammar formalisms. A grammar loaded from
Tulipac `.tag` syntax is compiled to an ordinary `Irtg`, just like a grammar
loaded from `.irtg` syntax. Once loaded, the parser operates on the IRTG's
grammar automaton, homomorphisms, and decomposition automata. The filename
extension is not a sound basis for choosing an algorithm.

## Top-down condensed

Top-down condensed materialization is the default used by `Irtg::parse`. It
starts from accepting product states and follows compatible condensed rules
downward.

Choose it when:

- you need the complete parse chart;
- you want to enumerate derivations or apply additional automaton operations;
- you have no workload-specific benchmark favoring another chart builder.

It is the safest general default. In current measurements it also behaves much
better than indexed condensed materialization on some TAG-derived IRTGs,
especially longer or highly ambiguous inputs. This is an observed workload
property, not a rule that all TAG grammars are slow under the indexed
algorithm.

Rust API:

```rust
let chart = irtg.parse(inputs)?;

// Equivalent explicit selection:
let chart = irtg.parse_with(
    inputs,
    &MaterializationStrategy::TopDownCondensed,
)?;
```

## Indexed condensed

Indexed condensed materialization grows reachable product states bottom-up. It
uses partial-child indexes to find grammar and decomposition rules that can be
joined through a known child.

Choose it when:

- you specifically need to compare indexed and top-down materialization;
- your own representative benchmark shows it performs well;
- you need its detailed intersection statistics.

It still constructs a complete chart. It is therefore not an early-exit
one-best parser. Candidate generation can grow very large for some ambiguous
or discontinuous decomposition automata. Some TAG-derived workloads exhibit
this behavior and can take dramatically longer than top-down condensed
materialization. Benchmark the sentences and grammars that matter to you
before selecting it as an application default.

Rust API:

```rust
let chart = irtg.parse_with(
    inputs,
    &MaterializationStrategy::IndexedCondensed,
)?;
```

## A*

A* explores product states in best-first order. It is most attractive when the
application needs the highest-weight derivation rather than every derivation.
With `stop_at_first_goal`, it can stop once the best accepting derivation is
proved.

Choose it when:

- you need one-best output;
- grammar weights satisfy the A* precondition: every rule weight is at most
  one;
- an admissible heuristic is available for the input interpretation;
- you have benchmarked heuristic setup as well as search time.

The available heuristic families are:

| Heuristic | Use |
| --- | --- |
| Zero | General exact baseline with no informed estimate. |
| Outside | Reuses grammar-only outside weights. |
| SX | Sentence-length-aware bound for string interpretations. |
| SXF | SX plus obligatory-terminal feasibility filtering. |

`SX` and `SXF` are specific to compatible string-algebra parsing. For other
input algebras, use a compatible general heuristic such as zero or outside.
A* is exact when its heuristic is admissible.

If a complete chart is required, A* can materialize a Viterbi-oriented forest,
but top-down condensed remains the clearer default for general chart
construction.

## Performance and grammar provenance

Algorithm choice should be based on the loaded IRTG and representative inputs,
not on how the grammar was serialized.

For example, `.tag` tells the input-codec registry to use the Tulipac reader.
That reader compiles the source to an `Irtg`. After loading, the same parser API
also handles IRTGs constructed programmatically or read from `.irtg` files.
An application cannot reliably infer "this parse is TAG" from the path, and it
does not need to. Relevant performance factors include:

- decomposition-automaton state space and transition fan-out;
- ambiguity and recursion in the grammar;
- homomorphism shape and rule arity;
- sentence length and discontinuity;
- whether a complete chart or only one-best output is requested;
- heuristic quality and setup cost.

Measure release builds. Debug builds are not meaningful parser benchmarks.

## Cooperative cancellation

Long-running parses can be stopped cooperatively with `ParseControl`.
Ordinary callers do not need a control: `parse` and `parse_with` keep their
simple APIs. Interactive or service applications can opt into
`parse_with_control`.

```rust
use rusty_alto::{
    IrtgError, MaterializationStrategy, ParseControl,
};

let control = ParseControl::new();
let worker_control = control.clone();

let worker = std::thread::spawn(move || {
    irtg.parse_with_control(
        inputs,
        &MaterializationStrategy::IndexedCondensed,
        &worker_control,
    )
});

// From the UI, timeout handler, or request owner:
control.cancel();

match worker.join().unwrap() {
    Err(IrtgError::Cancelled) => {}
    result => {
        let chart = result?;
        // use chart
    }
}
# Ok::<(), IrtgError>(())
```

Cancellation is cooperative:

- `cancel()` is thread-safe, cheap, and may be called more than once;
- cloned controls refer to the same cancellation state;
- parsing checks the state at safe points in top-down, indexed, and A*
  exploration, and during feature-structure filtering;
- cancellation returns `IrtgError::Cancelled`;
- partial charts are discarded rather than returned;
- the thread is not forcibly terminated, so return is prompt but not
  instantaneous if it is inside an indivisible algebra or automaton callback.

Use a fresh `ParseControl` for each independent parse job. A canceled control
stays canceled.

Feature-structure filtering can be canceled separately through
`filter_non_null_with_state_origins_controlled`.

## Benchmark before changing defaults

For a representative sample, record at least:

- algorithm and heuristic;
- release-mode wall time;
- whether a complete chart or one-best result was requested;
- chart states and rules when a chart is built;
- success, no-parse, error, or cancellation;
- sentence length and the grammar version.

The same algorithm may be excellent for one grammar and pathological for
another. Treat the recommendations above as starting points, then keep the
choice supported by measurements.
