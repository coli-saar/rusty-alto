# Sorted-language iterator autoresearch history

- Target: runtime and asymptotic scaling of the state-agenda iterator prototype
- Direction: lower is better
- Environment: local release builds
- Maximum iterations: 40
- Correctness gate: `cargo test sorted_language --lib`
- Benchmark command: `cargo bench --bench sorted_language_scaling`
- Scope: the sorted-language implementation, its tests and benchmarks,
  and minimal module/benchmark registration

The now-removed legacy iterator was the comparison baseline for these results.

## Outcome

- Replaced eager per-state sorting with lazy state-local agendas.
- Cached materialized subtrees so recursive enumeration is linear in the
  number of emitted nodes rather than repeatedly rebuilding prefixes.
- Represented high-arity successors as one-coordinate bumps and scored them
  with prefix/suffix products, avoiding rank-vector copies and division.
- Filtered unproductive rules once through the automaton's cached productivity
  analysis.
- Kept child ranks inline in each compact backpointer after ablation showed
  that a flattened side arena was 5-11% slower.
- Removed the separate iterative search and materialization implementations
  after deciding that depth-20,000 trees do not justify their maintenance cost.
- Added randomized, structural, zero-weight, high-arity, cold-start, and
  asymptotic regression coverage.
- Changed productivity saturation to process each child occurrence once;
  initialization is now linear even for rules with thousands of distinct
  children.
- Added balanced binary-tree probes for cold first-tree latency, the second
  tree specifically, and average advancement after the first tree.
- Replaced the productivity hash-of-vectors with a reusable dense CSR index.
- Added arity-shaped child-rank backpointers and direct unary/binary successor
  scoring while retaining the generic factorized path for larger arities.
- Kept initial rules in the automaton's top-down index behind a lazy cursor,
  avoiding per-state candidate-vector allocation.
- Kept tiny ready/blocked batches inline, bypassed one-element state heaps, and
  preserved generated-candidate capacity across advances.
- Deferred binary successor construction until a second item is requested and
  represented its single pending expansion with a flag.
- Replaced adaptive sparse/paged state-stream storage with a dense optional
  array after realistic automata showed high state-touch rates and materially
  faster dense access.
- Adopted packed-term-arena 0.1.3's allocation-free leaf/slice insertion in
  recursive tree materialization.

After the second ablation-driven pass, the largest measured speedups are 325x
for exhausting 4,096 alternatives in one state, 297x for exhausting 2,048
accepting states, and 78x for obtaining the second tree of arity 512. Random
acyclic workloads improve by 2.35-2.90x over the old iterator and by 23-28%
over the previous agenda implementation. After the large-binary follow-up,
the 65,535-node deterministic first tree is also 2.09x faster than the old
iterator, rather than 9% slower.
