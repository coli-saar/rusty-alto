# PTB Parsing Performance Changes

This note explains the PTB parsing optimizations made after the first
lazy-index/direct-Viterbi change. The goal was not to add a specialized
`parse_viterbi` path, but to make the general explicit chart construction and
one-best traversal machinery cheaper.

## Starting Point

After lazy bottom-up indexes and direct `Explicit::viterbi`, PTB parsing was much
better but still not as fast as expected from the lower-level benchmarks in
`docs/benchmark-results.md`. A macOS `sample` profile on PTB line 13 showed that
runtime was no longer dominated by inverse homomorphism or string decomposition.
Most samples were in explicit chart materialization:

- `TopDownIntersection::collect_pair`
- `LeftIndex::rule_indexes_for_sets`
- `SetTrie::for_each_value_for_key_sets_at`
- hash-table growth and allocation
- `ExplicitBuilder::add_weighted_rule`

The same sample also showed avoidable allocation in `Explicit::viterbi`, where
the DFS copied child tuples before recursive traversal.

After the `ProductStateMap` / trusted-rule-tracking work landed, the user reran
the fish profiling commands for PTB line 13. The file
`/private/tmp/rusty_alto_ptb13.sample.txt` was timestamped June 14, 2026 at
08:42:23, after the release binary timestamp, and its frames lined up with the
new source locations. I therefore treated it as the current profile for the
second cleanup round. It no longer showed the old duplicate-rule hash set as
the story; the visible costs had moved to:

- recursive `viterbi::visit_state`;
- `TopDownIntersection::collect_pair`;
- left-rule set matching through `LeftIndex` and `SetTrie`;
- residual rule-materialization allocation.

I tried to collect a fresh `sample` after the second cleanup, but macOS refused
to inspect the `rusty-alto` process without sudo in this environment. The
measurements below are fresh, but the post-first-round profile is the last
profiler snapshot used for diagnosis.

We checked Alto again before changing the design. Alto's `ParsingEvaluator`
calls `chart.viterbi()`, and Alto's generic Viterbi path also works over an
explicitly materialized chart. So the right comparison was not "lazy Viterbi
versus explicit Viterbi"; it was "how expensive is it to build and traverse the
explicit chart?"

## Product-State Map

The condensed intersection materializer needs a map

```text
(left_state, right_state) -> product_state
```

The old implementation stored this as a vector indexed by left state, with one
hash map per left state:

```text
left_state -> { right_state -> product_state }
```

Alto's analogous `IntInt2IntMap` is right-major. Its source comment says this is
intentional because right states are dense in the condensed parser and most
right states receive corresponding left partners. The Rust materializer now uses
a private `ProductStateMap` with the same orientation:

```text
right_state -> { left_state -> product_state }
```

This is still a general product/intersection data structure. It is not specific
to PTB, strings, or Viterbi. It simply reflects the shape of condensed
intersection workloads, where right states are generated densely by the right
automaton interner.

The change is tested by `materialize::tests::product_state_map_is_right_major_and_sparse`.

## Inline Rule Construction

Materialization naturally builds child tuples as `SmallVec<[StateId; 2]>`,
because almost all relevant automata rules have arity 0, 1, or 2. But
`ExplicitBuilder::add_weighted_rule` accepted `Vec<StateId>`, then converted that
`Vec` back into `SmallVec` internally.

That caused an avoidable round trip:

```text
SmallVec -> Vec -> SmallVec
```

The builder now has an internal method:

```rust
add_weighted_rule_inline(symbol, children, parent, weight)
```

Public callers can continue using `Vec<StateId>`. Internal materializers can move
their inline child tuple directly into the builder. This removes allocation and
copying from the hottest rule-construction path without changing the public API.

The change is tested by `explicit::tests::add_weighted_rule_inline_preserves_child_tuple`.

## Trusted Rule Tracking

The top-down condensed materializer previously maintained an `output_seen` hash
set for every generated rule:

```text
(symbol, children, parent)
```

This was expensive in the profile: every emitted rule paid for another hash key,
and the child tuple had to be cloned for the set. Earlier PTB instrumentation
found no duplicate output rules on the checked sentences, and the materializer
already builds the final `Explicit` chart with `build_trusted`.

The new code makes this invariant explicit with `TrustedRuleTracker`:

- in debug builds, it keeps a `seen` set and asserts that no duplicate rule is
  generated;
- in release builds, it moves rules straight into the builder with no duplicate
  hash-table cost.

This is a general construction policy: external `ExplicitBuilder::build` still
checks duplicates, while internal algorithms that generate unique rules by
construction can avoid paying for duplicate checks in hot loops.

The existing materializer tests pass with the debug assertion enabled, so the
current invariant is exercised by the test suite.

## Viterbi Traversal

`Explicit::viterbi` was already a direct one-best dynamic program, but its DFS
phase copied each top-down rule's child tuple into a temporary `Vec<Vec<StateId>>`
before recursing. This avoided borrow-shape friction but showed up clearly in
the profile.

`Explicit` now exposes two crate-private helpers:

```rust
rule_indexes_topdown(parent)
rule(rule_idx)
```

The Viterbi DFS walks rule indexes and borrowed rule views directly. It no
longer allocates child-tuple copies during traversal. These helpers are general:
future semiring evaluation, reachability, or top-down algorithms can use the
same pattern when they need stable rule references without materializing owned
tuples.

The second cleanup also replaces recursive DFS with an explicit `Enter`/`Exit`
stack. This keeps the same semantics as before:

- stuck states and out-of-range states are ignored;
- self-loop rules are skipped;
- already visited states are not traversed again;
- states are emitted in postorder before the dynamic program consumes them.

Backpointers now store children as `SmallVec<[StateId; 2]>`, matching the rule
storage used elsewhere. This keeps binary parse-chart derivations inline and
avoids heap allocation for the common case.

The behavior is covered by tests for best-tree weight, self-loop skipping, and
binary child order.

## Reused Match Buffers

The top-down materializer repeatedly asks the left grammar index for all rules
whose child tuple is accepted by one partner set per child position. Previously
`LeftIndex::rule_indexes_for_sets` returned a fresh `SmallVec` for every query.
That is small, but it is directly inside the materialization loop.

`LeftIndex` now has:

```rust
rule_indexes_for_sets_into(symbols, child_sets, out)
```

The caller owns the buffer and the method clears and refills it. The
`TopDownIntersection` context keeps one `matches_scratch: Vec<usize>` and reuses
it for both normal rules and loop rules. This is not PTB-specific; it is the
usual "write into caller scratch" shape for a hot index query.

## Singleton Set Views

Loop-rule processing previously allocated a one-element `FxHashSet` for the
left state currently being propagated through the loop position. The
`SetTrie` traversal only needs the `KeySet` interface, so the materializer now
uses a lightweight private view:

```rust
One(StateId) | Many(&FxHashSet<StateId>)
```

To support this cleanly, `SetTrie::for_each_value_for_key_sets` now accepts any
slice of `KeySet` values, and there is a blanket `KeySet` implementation for
references. Existing callers can still pass borrowed hash sets, while loop
processing can mix singleton and borrowed-set views without allocating.

This is tested directly against `SetTrie` traversal and through
`LeftIndex::rule_indexes_for_sets_into`.

## Top-Down Result Index

`Explicit::result_index` used to create one empty vector per state and grow each
parent bucket as rules were inserted. The new implementation does a count pass
followed by a fill pass, so every per-parent rule-index vector is allocated with
its exact final capacity.

This keeps `rules_topdown`, `rule`, and `rule_indexes_topdown` behavior
unchanged. It only changes how the cached index is constructed.

## Measurements

These timings used the release binary on the PTB files in
`~/Documents/workspace/alto/ptb`.

Before this round, after the first lazy-index/Viterbi change, the observed
timings were approximately:

| PTB line | Total | Parse | Top |
| ---: | ---: | ---: | ---: |
| 13 | 5.9-6.4 s | 5.1-5.5 s | 0.8-0.9 s |
| 4 | 41.6 s | 36.5 s | 5.1 s |

After the first materialization cleanup round:

| PTB line | Total | Parse | Top |
| ---: | ---: | ---: | ---: |
| 13 | 1.585 s | 1.285 s | 299.69 ms |
| 4 | 10.598 s | 7.923 s | 2.675 s |

After the second allocation cleanup round:

| PTB line | Total | Parse | Top |
| ---: | ---: | ---: | ---: |
| 13 | 1.382 s | 1.186 s | 195.63 ms |
| 4 | 9.213 s | 7.538 s | 1.675 s |

The largest gain is in parse time, which matches the profile: the main cost was
explicit chart construction, not the Viterbi algorithm itself. The second round
also produced a visible top-time improvement because Viterbi no longer recurses
and keeps binary backpointers inline.

## Remaining Work

The profile still points at materialization as the main cost center. Good next
steps would be:

- benchmark left-major versus right-major `ProductStateMap` on non-PTB
  intersections;
- consider pre-sizing large vectors and hash maps from grammar and sentence
  statistics;
- expose more allocation-free rule traversal APIs if other algorithms need
  them;
- profile again on a long PTB sentence to see whether `SetTrie` lookup,
  product-state interning, or Viterbi traversal is now the next bottleneck.

The important design point is that these changes are not a specialized PTB
parser. They make the common explicit-materialization path cheaper while keeping
the public automaton API clean.
