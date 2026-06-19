# A* Post-Revision Performance Plan

## Purpose

The changes in `docs/astar-revision-plan.md` are largely implemented, but they
did not improve end-to-end performance on the first 30 PTB sentences. This plan
records the remaining performance work identified by the post-implementation
audit and orders it by expected leverage.

The central result of the audit is that the parser is now candidate-bound.
Direct span construction has eliminated right-transition work on the specialized
PTB path, but eager candidate generation still realizes hundreds of millions of
edges that are immediately filtered or dominated.

## Current Baseline

Measured with a warmed `release-optimized` build:

```sh
target/release-optimized/eval \
  ~/Documents/workspace/alto/ptb/out.irtg \
  ~/Documents/workspace/alto/ptb/out.txt \
  --limit 30 --algorithm astar --heuristic sxf \
  -o /tmp/rusty-alto-eval.corpus \
  --times /tmp/rusty-alto-times.csv \
  --astar-stats /tmp/rusty-alto-stats.csv
```

Results:

- Total parse time: 40.57 s.
- Previous recorded total: 39.99 s.
- Median sentence parse time: 171.38 ms, versus 169.04 ms previously.
- Candidate edges: 521.0 million.
- F-filtered candidates: 254.8 million.
- Dominated candidates: 189.9 million.
- Candidates discarded after finalization: 32.3 million.
- Product states created: 27.7 million.
- Product states finalized: 16.8 million.
- Right-transition calls on the specialized string path: zero.

The direct-span and transition-elimination changes therefore worked, but removed
a cost that is no longer significant. CPU profiling places candidate admission
and insertion at the center of the remaining runtime, followed by obligatory-leaf
filtering, product lookup, agenda operations, and finalization.

## P0 — Improve Measurement

Before changing algorithms, make the benchmark distinguish the important costs.

- Add counters for:
  - distinct parent product pairs presented to the heuristic;
  - heuristic cache hits and misses;
  - sibling queries returning an empty slice;
  - rule candidates per sibling tuple;
  - pending-edge allocations and higher-arity spills;
  - product-map hits, misses, and insertions;
  - sibling-index activations and lookups;
  - eager versus lazy merit evaluations and realized candidates.
- Expose the eager and lazy string sources in `ptb-eval` as explicit benchmark
  strategies. Do not select lazy automatically.
- Run at least three interleaved trials and compare medians. Record both total
  parse time and the longest-sentence tail, because previous lazy experiments
  behaved differently on short and long sentences.
- Capture peak RSS along with CPU time.

## P1 — Cache Heuristic Results by Product Pair

**Status: implemented and retained.**

### Problem

`push_candidate_with_child_score` evaluates the combined SX/F heuristic before
looking up the parent product. The same `(parent_left, parent_span)` is reached
through many rules and split points, so the identical heuristic calculation is
repeated per candidate.

This is especially visible for the F filter: approximately half of all
candidates are rejected, but each rejected occurrence repeats the obligatory
leaf lookup and terminal-supply checks.

### Implemented change

- `IntersectionHeuristic` has an algebra-independent opt-in for admission
  memoization.
- A* stores two right-major `FixedBitSet` collections:
  - pairs whose admission filter has been checked;
  - checked pairs that were admitted.
- Cached rejections return immediately.
- Cached admissions skip the expensive filter and call
  `estimate_after_admission`; SX therefore retains its cheap array lookup while
  F returns its known pass value without repeating terminal-supply checks.
- The cache is independent of `ProductStateMap`, so rejected pairs do not create
  product states.
- The implementation uses only interned right-state IDs and grammar state IDs;
  it contains no string-algebra or span assumptions.

### Measured result

On the first 30 PTB sentences:

- admission-cache hits: 459.2 million;
- admission-cache misses: 61.8 million;
- hit rate: 88.1%;
- all candidate, product, finalization, and parse results unchanged.

Three interleaved same-binary trials:

| Cache | Total parse times | Median |
| --- | --- | --- |
| off | 40.68 s, 40.57 s, 40.82 s | 40.68 s |
| on | 37.84 s, 37.92 s, 37.09 s | 37.84 s |

The retained bitset cache improves median total parse time by approximately
7.0%. A first implementation using right-major hash maps cached the complete
`Option<f64>` estimate; despite the same hit rate, it regressed to 46.95 s
because 61.8 million hash entries were too expensive. That representation was
discarded.

### Verification

- Candidate, product, finalization, and parse results are unchanged at limit 30.
- Full tests and Clippy pass.
- Still compare `sxf` at limits 100 and full PTB and record peak RSS.

## P2 — Re-evaluate Lazy Candidate Generation

### Problem

The eager source realizes every compatible `(rule, sibling, split)` candidate.
The measured funnel shows that most of these candidates never affect the final
agenda state. Constant-factor improvements alone cannot remove the resulting
`O(|rules| n^3)` work.

The existing lazy frontier is the only implemented approach that attacks this
candidate count asymptotically, but the revised implementation has only small
equivalence tests and is not available in the PTB benchmark binary.

### Change

- Add explicit `astar-eager` and `astar-lazy` PTB benchmark strategies using the
  same scoring, filtering, product storage, and agenda implementation.
- Measure:
  - candidate merit evaluations;
  - realized candidate edges;
  - parent-agenda pushes and updates;
  - frontier pushes, pops, and updates;
  - generators and stored sibling entries;
  - peak RSS;
  - performance grouped by sentence length.
- Re-profile the revised lazy implementation before altering it.

If merit computation remains the bottleneck, investigate a second-stage design:

- Order rules within a sibling group by grammar-rule score.
- Cache parent-pair heuristic values so sibling merits do not repeat F/SX work.
- Use a heap or monotone iterator over rule/sibling combinations rather than
  realizing all rules for a selected sibling.
- Preserve the eager source as the production default until lazy wins
  reproducibly on both total time and long sentences, without unacceptable
  memory growth.

### Expected effect

This has the highest asymptotic ceiling. It is also the highest-risk item, so it
should follow the heuristic cache and use the new counters to explain wins or
regressions.

## P3 — Replace Hashing in the String Sibling Index

### Problem

`SpanProductSiblingFinder` currently hashes `(boundary, left_state)` during every
activation and sibling lookup. This representation is sparse in memory, but
activation appears prominently in the CPU profile and sibling lookup is in the
candidate-generation loop.

Alto's string sibling finder indexes directly by span boundary. Rusty-alto needs
the additional left-state discrimination, but does not necessarily need a
two-component hash for it.

### Change

Benchmark these representations:

1. A vector indexed by boundary whose entries are maps from compact left slots
   to sibling-list IDs.
2. Assign every left state that occurs in a binary child position a compact
   sibling-state slot in `PreparedAstarGrammar`, then use:
   - dense boundary × compact-slot arrays when small;
   - sparse per-boundary sorted vectors when large.
3. A hybrid representation that starts as a small vector and promotes to a map
   only for unusually populated boundaries.

Do not return to an array indexed by the raw grammar-state maximum unless memory
measurements justify it. The goal is direct or compact indexing for the common
PTB case while retaining sparse behavior for general grammars.

### Verification

- Sibling tuple counts and parse results must be identical.
- Measure activation time, lookup time, and peak RSS separately.
- Retain the current hash representation as an A/B implementation until the
  replacement wins reproducibly.

## P4 — Finish Product-State and Backpointer Compaction

### Problem

The P3 storage work is incomplete:

- `PendingEdge` still contains a `SmallVec<[StateId; 2]>`.
- `pending` stores an `Option<AgendaItem>` for every created product.
- Finalization clones pending children into a second `SmallVec` in the
  backpointer arena.
- The general `Backpointer` stores a score for every finalized product even
  though A* already stores finalized inside scores separately.

At 27.7 million products and 16.8 million finalizations, representation size and
copy traffic affect both RSS and cache locality.

### Change

- Introduce a compact child tuple with explicit variants for arity 0, 1, and 2,
  spilling to arena storage only for larger arities.
- Move the child tuple from pending state into the finalized backpointer rather
  than cloning it.
- Use an A*-specific finalized backpointer containing only:
  - rule ID or symbol;
  - compact children.
- Consider splitting pending state into structure-of-arrays:
  - pending rule ID;
  - child payload;
  - occupancy bitset.
- Measure whether arena allocation for all pending edges is better than an
  inline per-product representation. Do not assume that fewer Rust types imply
  better locality.

### Verification

- Record `size_of` values for the old and new pending/backpointer payloads.
- Compare peak RSS and finalization self-time.
- Test arbitrary-arity fallback rules so spills remain correct.

If the compact child tuple is sufficiently general, consider proposing it to
`rusty-tree` rather than adding general-purpose tree tuple handling here. Do not
modify `rusty-tree` as part of this work.

## P5 — Complete Prepared Grammar Reuse

### Problem

`PreparedAstarGrammar` reuses the owned rules and major indexes, but each
sentence still performs some grammar-dependent work:

- `string_fallback_rules` classifies every rule against the homomorphism.
- A filtered fallback `LeftIndex` is rebuilt when fallback rules exist.
- all rule scores are recomputed for the scorer.

These costs are small for the current fully specialized PTB path, but the
prepared API does not yet meet its intended semantics and will regress on
mixed-specialization workloads.

### Change

- Add an interpretation-specific prepared string layer containing:
  - fallback-rule bitset;
  - filtered fallback index;
  - whether generic partner storage is needed;
  - any compact sibling-state slot assignment from P3.
- Add scorer-specific prepared rule scores, or store log-probability scores in
  the batch evaluator when the scorer is fixed.
- Keep `PreparedAstarGrammar` scorer-independent unless a clean generic cache
  API emerges; avoid hiding scorer identity behind unsafe assumptions.
- Continue checking that prepared data is paired with the grammar and
  interpretation it was built from.

### Verification

- Add a mixed specialized/fallback batch benchmark.
- Confirm that no grammar or homomorphism classification occurs inside the
  sentence loop.
- Verify identical output for prepared and unprepared entry points.

## P6 — Avoid Double Hashing on Product Insertion

### Problem

On a missing product pair, `ProductStateMap` first performs `get` and then a
separate `insert`, hashing the left state twice. The 30-sentence run creates
27.7 million products.

### Change

- Add an entry-style `get_or_insert_with` operation to `ProductStateMap`.
- Use `hashbrown` raw-entry or entry APIs to perform one lookup for a miss.
- Return both the product ID and whether it was newly inserted, preserving the
  current caller contract.
- Keep the right-major sparse organization unless profiling after P1–P4 shows
  that a different representation has a clear advantage.

### Verification

- Product IDs and pair order must remain deterministic.
- Product counts and all parse outputs must remain unchanged.
- Re-profile product lookup and insertion; keep only if the end-to-end effect is
  measurable or the abstraction is clearly simpler.

## Recommended Sequence

1. Improve counters and expose eager/lazy benchmark strategies.
2. Implement and benchmark the parent-pair heuristic cache.
3. Benchmark the revised lazy frontier with the cache in place.
4. Replace the hashed string sibling index, guided by RSS and CPU profiles.
5. Compact pending edges and finalized backpointers.
6. Complete prepared interpretation/scorer reuse.
7. Add single-lookup product insertion.
8. Re-profile before pursuing any new product-map or agenda redesign.

## Acceptance Criteria

- Specialized and generic parsing remain score- and tree-equivalent.
- Candidate counts remain identical for eager A/B experiments unless an
  explicitly lazy source is selected.
- The heuristic cache materially reduces heuristic evaluations and improves
  median `sxf` parse time.
- Any new sibling-index representation improves CPU time without an
  unacceptable peak-RSS regression.
- Compact storage reduces peak RSS or finalization time measurably.
- Prepared batch parsing performs no grammar/homomorphism indexing in the
  per-sentence loop.
- Lazy is enabled in production only after reproducible wins at limits 20, 100,
  and full PTB, including the longest-sentence tail.
- Full tests, Clippy, `eval --limit 100`, and a complete PTB run pass.
