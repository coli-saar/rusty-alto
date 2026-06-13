# Benchmark Results

This document records benchmark procedures, current measurements, and
interpretation. Implementation decisions and low-level performance details live
in [`performance.md`](performance.md).

Treat these numbers as directional unless a section explicitly says otherwise.
Most entries are smoke measurements intended to catch obvious regressions and
guide the next implementation step.

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

| Workload | Rust mode | Trees | rusty-alto ns/tree | Alto ns/tree | Alto/rusty speedup |
| --- | --- | ---: | ---: | ---: | ---: |
| deterministic-binary-small | det | 64 | 1589.583 | 5343.333 | 3.36 |
| deterministic-binary-large | det | 32 | 11614.636 | 57575.234 | 4.96 |
| deterministic-unary-small | det | 128 | 319.811 | 1558.268 | 4.87 |
| deterministic-unary-large | det | 32 | 4635.834 | 14751.641 | 3.18 |
| nondeterministic-binary-small | nondet | 64 | 1339.062 | 3824.128 | 2.86 |
| nondeterministic-binary-large | nondet | 16 | 5669.792 | 15627.864 | 2.76 |
| nondeterministic-unary-small | nondet | 128 | 1929.303 | 3888.828 | 2.02 |
| nondeterministic-unary-large | nondet | 32 | 30008.177 | 42103.906 | 1.40 |

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

| Engine | Algorithm | Left rules | Right rules | Output states | Output rules | ns/intersection |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| rusty-alto | naive | 192 | 175 | 660 | 23880 | 6797487.500 |
| rusty-alto | sibling | 192 | 175 | 660 | 23880 | 5424145.900 |
| Alto | naive | 192 | 175 | 660 | 23880 | 57177995.900 |
| Alto | sibling | 192 | 175 | 660 | 23880 | 10214129.200 |

Interpretation:

- Rust's indexed path is already faster on this moderate workload, but the
  speedup is modest because both Rust implementations are simple and the naive
  scan is still small enough to stay cache-friendly.
- Alto's sibling-finder path gives a much larger improvement over Alto's naive
  intersection on the same generated automata.
- The workload is intentionally close to `StringAlgebra` CKY decomposition, but
  it is still explicit on the Rust side. A future port of Alto's implicit
  `StringAlgebra` decomposition should add an explicit-vs-implicit row.

## Next Benchmarking Work

Add parser-like product workloads once indexed rule enumeration exists. The
current product benchmarks measure transition-query performance, not full
chart-style parsing behavior.

Extend the intersection harness after porting `StringAlgebra` so it can compare
explicit grammar vs implicit decomposition automata directly.

Add a dense-state determinization benchmark before replacing the current
`BTreeSet`-based generic determinizer.

Add larger realistic Alto automata once the parser covers enough of Alto's
format to load them without hand reduction.
