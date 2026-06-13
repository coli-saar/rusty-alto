# Benchmark Results

This document records benchmark procedures, current measurements, and
interpretation. Implementation decisions and low-level performance details live
in [`performance.md`](performance.md).

Treat these numbers as directional unless a section explicitly says otherwise.
Most entries are smoke measurements intended to catch obvious regressions and
guide the next implementation step.

Times in the summary tables are rounded to human-readable units. Generated
reports under `target/alto-comparison/` keep the raw nanosecond counters when
exact machine-readable values are needed.

## Criterion Suite

The Criterion suite lives in [`benches/phase1.rs`](../benches/phase1.rs).

Run the full suite with:

```bash
cargo bench --bench phase1
```

For a quick development smoke check:

```bash
cargo bench --bench phase1 -- --sample-size 10
```

The suite currently covers:

- explicit `step_det` lookup for arity 0, 1, 2, and higher arity
- explicit indexed `step_partial` and top-down rule enumeration
- deterministic and nondeterministic tree runs
- cold and warm `Memo` runs over an implicit automaton
- generic, deterministic, and indexed product steps
- generic determinization
- materialization over a finite implicit automaton
- repeated explicit reachability queries

## Criterion Findings

The following impacts came from Criterion smoke runs with `--sample-size 10`.
They are useful for direction, not publication-quality claims.

| Area | Impact |
| --- | --- |
| `run_nondet` borrows child state sets instead of cloning them | `run_nondet_balanced_depth_9` improved by about 38%. |
| `Memo` replays cached results by borrow instead of cloning cached `SmallVec`s | Cold/warm deterministic runs over a memoized implicit automaton improved by about 8-11%. |
| `Product` generic path uses inline `SmallVec` result buffers | `product_binary_step` improved by about 76%. |
| `Product` deterministic fast path | `product_binary_step_det` measured around 8 ns in the smoke run. |
| `Explicit::reachable_states` caches its result | Repeated reachability benchmarks moved to nanosecond-scale clone-of-cached-bitset behavior. |

The main lesson so far is that allocation avoidance matters more than clever
extra indexing for the Phase 1 workloads. The rejected materialization
query-deduplication experiment is the clearest example: it added hashing work
and regressed the arity <= 2 materialization benchmark by about 7-10%.

## Alto Comparison Harness

The cross-library comparison harness uses one Alto `.auto` file plus one
tree-per-line input file as the joint workload.

Run a single comparison with:

```bash
scripts/compare-alto.sh \
  --auto examples/compare.auto \
  --trees examples/compare.trees \
  --iterations 1000 \
  --warmup 20
```

Run the generated suite with:

```bash
scripts/compare-alto.sh \
  --suite \
  --iterations 100 \
  --warmup 10 \
  --report target/alto-comparison/report.md
```

By default the script uses:

```text
~/Documents/workspace/alto/build/libs/alto-2.3.8-SNAPSHOT-all.jar
```

Override that path with `--alto-jar PATH` or `ALTO_JAR=PATH`. A JitPack or
GitHub-release jar can be used as long as it contains Alto and its runtime
dependencies.

The script writes a Markdown report with comparison tables. It aborts if Rust
and Alto disagree on either:

- `accepted_last`: number of accepted trees in the final measured iteration
- `root_states_last`: total number of root states across those trees

This harness is an end-to-end comparison. It includes parsing, tree-run
machinery, runtime effects, and JVM behavior, so it complements Criterion rather
than replacing it.

## Intersection Comparison Harness

The intersection harness compares materializing the product of a generated
explicit grammar automaton and an explicit CKY-style string-span automaton. The
right automaton follows Alto's `StringAlgebra` decomposition shape: word labels
create length-1 spans, and the binary `*` label combines adjacent spans.

Run it with:

```bash
scripts/compare-intersection.sh \
  --states 12 \
  --len 10 \
  --vocab 4 \
  --iterations 10 \
  --warmup 2 \
  --report target/alto-comparison/intersection-report.md
```

The script runs four combinations:

- `rusty-alto` naive: repeated compatible rule-pair scanning
- `rusty-alto` sibling: agenda-driven child-pair joins using child-state indexes
- Alto naive: `IntersectionAutomaton.intersectBottomUpNaive`
- Alto sibling: an agenda benchmark using Alto `ConcreteTreeAutomaton` and
  `SiblingFinder` indexes

It verifies that the Rust naive and sibling algorithms produce identical output
state and rule counts. Alto counts are reported in the same table; the current
generated workload has matched the same counts in smoke runs.

## Condensed Parsing Harness

The condensed parsing harness is the main end-to-end benchmark for
homomorphism-based string parsing. It builds:

- a source tree automaton with many lexical and binary source labels,
- a homomorphism from those labels into `StringAlgebra` terms,
- a string decomposition automaton for the input sentence, and
- the condensed inverse homomorphism of that decomposition automaton.

The benchmark then materializes the intersection of the source automaton with
the condensed inverse homomorphism. Lexical source labels map to word constants,
and all binary source labels map to `*(?0, ?1)`, so the workload directly tests
whether shared homomorphic images are exploited as label sets.

Run it with:

```bash
scripts/compare-condensed-parsing.sh \
  --states 16 \
  --len 12 \
  --vocab 4 \
  --lexical-labels 4 \
  --binary-labels 16 \
  --iterations 10 \
  --warmup 2 \
  --report target/alto-comparison/condensed-parsing-report.md
```

The script compares `rusty-alto` against Alto's
`CondensedNondeletingInverseHomAutomaton` plus `intersectCondensed`. It aborts
if output state or rule counts differ.

## Generated Alto Suite

Suite mode currently generates eight workloads:

| Workload family | Shape | Sizes |
| --- | --- | --- |
| deterministic binary | balanced `f(left,right)` trees | small, large |
| deterministic unary | `g(g(...a))` chains | small, large |
| nondeterministic binary | balanced `f(left,right)` trees with two possible state families | small, large |
| nondeterministic unary | `g(g(...a))` chains with two possible state families | small, large |

The deterministic binary workload is the most favorable case for the current
library: nullary and binary rules, dense states, and a deterministic result at
every node. The nondeterministic unary workload is less favorable because it
propagates small state sets through many levels where tuple enumeration is not
the main cost.

## Current Alto Suite Results

The following smoke run used 50 iterations and 5 warmup iterations. Both
engines agreed on all semantic counters.

| Workload | Rust mode | Trees | rusty-alto time/tree | Alto time/tree | Alto/rusty speedup |
| --- | --- | ---: | ---: | ---: | ---: |
| deterministic-binary-small | det | 64 | 1.59 us | 5.34 us | 3.36x |
| deterministic-binary-large | det | 32 | 11.6 us | 57.6 us | 4.96x |
| deterministic-unary-small | det | 128 | 320 ns | 1.56 us | 4.87x |
| deterministic-unary-large | det | 32 | 4.64 us | 14.8 us | 3.18x |
| nondeterministic-binary-small | nondet | 64 | 1.34 us | 3.82 us | 2.86x |
| nondeterministic-binary-large | nondet | 16 | 5.67 us | 15.6 us | 2.76x |
| nondeterministic-unary-small | nondet | 128 | 1.93 us | 3.89 us | 2.02x |
| nondeterministic-unary-large | nondet | 32 | 30.0 us | 42.1 us | 1.40x |

Interpretation:

- The deterministic rows show the expected benefit from dense `StateId` side
  tables and arity-specialized `step_det` lookup.
- Binary deterministic trees scale especially well because the workload stays
  inside the optimized nullary/binary rule indexes.
- Nondeterministic rows remain favorable, but the margin is smaller because
  both engines must carry multiple root states.
- Deep unary nondeterminism has the smallest margin. It stresses repeated
  propagation of small state sets, not the arity-2 lookup path where the current
  implementation is strongest.

## Earlier Smoke Checks

The tiny sample workload in [`examples/compare.auto`](../examples/compare.auto)
and [`examples/compare.trees`](../examples/compare.trees) is useful as a quick
sanity check. In a 1000-iteration, 20-warmup smoke run, both engines agreed on
`accepted_last=3` and `root_states_last=4`; the measured time was roughly
386 ns/tree for `rusty-alto` and 739 ns/tree for Alto.

The generated deterministic workload with `DEPTH=8`, `COUNT=32`, 500
iterations, and 50 warmup iterations accepted all 32 trees in both engines. The
smoke run measured roughly 6.0 us/tree for `rusty-alto` in `mode=det` and
20.9 us/tree for Alto.

## Current Intersection Results

The following smoke run used 12 grammar states, sentence length 10, vocabulary
size 4, 10 iterations, and 2 warmup iterations.

| Engine | Algorithm | Left rules | Right rules | Output states | Output rules | Time/intersection |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| rusty-alto | naive | 192 | 175 | 660 | 23,880 | 6.80 ms |
| rusty-alto | sibling | 192 | 175 | 660 | 23,880 | 5.42 ms |
| Alto | naive | 192 | 175 | 660 | 23,880 | 57.2 ms |
| Alto | sibling | 192 | 175 | 660 | 23,880 | 10.2 ms |

Interpretation:

- Rust's indexed path is already faster on this moderate workload, but the
  speedup is modest because both Rust implementations are simple and the naive
  scan is still small enough to stay cache-friendly.
- Alto's sibling-finder path gives a much larger improvement over Alto's naive
  intersection on the same generated automata.
- The workload is intentionally close to `StringAlgebra` CKY decomposition. The
  condensed parsing harness below now compares the explicit CKY automaton
  against the lazy `StringAlgebra` decomposition automaton directly.

## Current Condensed Parsing Results

The following smoke run used 16 grammar states, sentence length 12, vocabulary
size 4, 4 lexical source labels per word, 16 binary source labels mapping to
concat, 3 measured iterations, and 1 warmup iteration.

| Engine | Decomp | Intersection | Grammar rules | Decomp rules | Right rules/queries | Output states | Output rules | Time/parse |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| rusty-alto | implicit | eager | 4,352 | 298 | 298 | 1,248 | 1,172,224 | 158 ms |
| rusty-alto | implicit | indexed-condensed | 4,352 | 298 | 168 | 1,248 | 1,172,224 | 175 ms |
| Alto | implicit | condensed | 4,352 | 298 | NA | 1,248 | 1,172,224 | 283 ms |

Interpretation:

- Both engines materialized the same chart: 1,248 output states and 1,172,224
  output rules.
- The indexed-condensed path queried only 168 right-side nullary/indexed
  condensed entries instead of enumerating all 298 right rules. On this dense
  small workload, runtime is still dominated by materializing over one million
  output rules, so the query reduction does not yet translate into a win.
- The synthetic grammar saturates the chart: all 78 spans combine with all 16
  grammar states.
- The Rust benchmark uses the same fast hash tables as the library hot paths
  and inline child tuples for arity <= 2. That matters here because almost all
  materialized output rules are binary.
- The implicit rows use the same generic `Explicit x CondensedTa` intersection
  path as other condensed automata; there is no string-specific intersection
  shortcut.

The implicit path does become faster when the string decomposition is a larger
fraction of the work and the run is cold with respect to explicit condensed-rule
caches. The following runs used 4 grammar states, 1 lexical label per word, and
1 binary label mapping to concat, with no warmup.

| Sentence length | Decomp | Intersection | Decomp rules | Right rules/queries | Output states | Output rules | Time/parse |
| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 96 | implicit | eager | 147,536 | 147,536 | 18,624 | 2,359,424 | 421 ms |
| 96 | implicit | indexed-condensed | 147,536 | 9,408 | 18,624 | 2,359,424 | 377 ms |

The indexed-condensed path avoids materializing most right-side inverse-hom
rules here, but the benchmark still saturates the chart: 4 grammar states times
4,656 spans gives 18,624 output states. More selective grammars should show a
larger gap because fewer right-side rules become reachable at all.

## Next Benchmarking Work

Add parser-like product workloads once indexed rule enumeration exists. The
current product benchmarks measure transition-query performance, not full
chart-style parsing behavior.

Add less-saturating grammars to the condensed parsing harness so indexed
condensed intersection can demonstrate pruning of unreachable inverse-hom
rules, not only reduced right-side query counts.

Add a dense-state determinization benchmark before replacing the current
`BTreeSet`-based generic determinizer.

Add larger realistic Alto automata once the parser covers enough of Alto's
format to load them without hand reduction.
