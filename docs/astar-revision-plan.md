# Prioritized A* Generalization and Performance Plan

## Summary

Make A* general for arbitrary condensed automata and rule arities while preserving an optimized binary-string candidate source. Optimize the eager path first, retain `lazy_span.rs` as an unwired experiment, then benchmark it against the improved eager implementation.

## P0 — Correctness and Baseline

- Benchmark warmed `release-optimized` builds with `eval --limit 20`, `100`, and the full PTB corpus using `zero`, `sx`, and `sxf`.
- Add tests for reversed string variables, fixed tokens around children, mixed specialized/fallback rules, arbitrary arity, non-string automata, and admissible inconsistent heuristics.
- Support reopening for admissible inconsistent heuristics; built-in consistent heuristics must retain zero reopenings.
- Correct API semantics: distinguish Viterbi forests from complete charts, filter beams by finalized merit, filter nullary seeds, and prevent prepared indexes from being paired with a different grammar.

## P1 — General Candidate Sources

- Keep algebra semantics out of the A* core. It owns scoring, filtering, dominance, agenda operations, reopening, finalization, and backpointers.
- Add a crate-private candidate-source interface for seeds, product activation, and candidate enumeration.
- Provide an always-correct generic implementation using `CondensedTa`, finalized partner sets, and arbitrary child tuples.
- Move span-specific indexes and transitions into a `StringAstarSource` under the string algebra module.
- Keep `StringYieldTemplate` private to that specialization. Classify rules individually and send unsupported forms or higher arities through the generic source.
- Replace binary-only core representations with child tuples that store arities 0–2 inline and spill for larger rules.

## P2 — Low-Risk Hot-Path Improvements

- Precompute grammar-rule scores, eliminating per-candidate logarithms.
- Fuse admission filtering and outside-score evaluation.
- Compute exact parent spans directly for supported string templates instead of hashing transition-memo keys.
- Iterate borrowed sibling slices without copying.
- Reuse prepared grammar indexes across `eval` instances.
- Build generic indexes and partner storage only for fallback rules.

## P3 — Memory and Cache Locality

- Replace the theoretical-size heap allocation with a dynamically growing indexed quaternary heap.
- Compact product state by merging inside-score arrays, removing duplicate agenda scores, representing pending edges by rule ID plus compact children, and arena-allocating finalized backpointers.
- Flatten the string sibling index and allocate only populated boundary/nonterminal slots.
- Re-profile before changing `ProductStateMap`; do not revive the rejected dense dominance matrix without evidence.

## P4 — Cleanup, Separation, and Lazy Re-evaluation

- Remove stale-pop handling from the decrease-key agenda. Since it holds at most one entry per product, popping a product without a pending item becomes an invariant failure.
- Split the implementation into:

  - General A* core and public facade.
  - Agenda and product-state storage.
  - Generic condensed candidate source.
  - String-specific candidate source.

- Remove `RUSTY_ALTO_LAZY_FRONTIER` and automatic production selection.
- Keep `lazy_span.rs`, focused equivalence tests, and an explicit benchmark-only entry point.
- Adapt the lazy frontier to the new candidate-source and compact-storage interfaces without duplicating the general search core.
- After P1–P3 stabilize, benchmark eager and lazy with identical scoring, candidate generation, agenda, and product storage.
- Enable lazy in production only if it demonstrates a reproducible time or memory advantage. Otherwise preserve it as an unwired research prototype.

## Benchmarking and Profiling

Build and warm caches:

```sh
cargo build --profile release-optimized --bin eval
```

Routine A/B:

```sh
target/release-optimized/eval \
  ~/Documents/workspace/alto/ptb/out.irtg \
  ~/Documents/workspace/alto/ptb/out.txt \
  --limit 20 --algorithm astar --heuristic sxf \
  -o /tmp/rusty-alto-eval.corpus \
  --times /tmp/rusty-alto-times.csv
```

Use `--limit 1` for smoke tests, `20` for iteration, `100` after each phase, and the full corpus for final validation. Run at least three interleaved trials and compare median `parse_ms`. Use `zero` as a candidate-volume stress test, `sx`/`sxf` as production workloads, and exhaustive parsing on a smaller limit as the correctness oracle.

Add optional per-sentence A* statistics for candidates, filtering, dominance, products, reopenings, agenda operations and capacity, generic versus specialized work, transition memo behavior, and storage peaks.

Capture CPU profiles and peak RSS before P1, after P2, and after P3. Re-profile before pursuing additional data-structure changes.

For lazy-frontier evaluation, compare eager and lazy at limits 20, 100, and full corpus, measuring time, peak RSS, merit evaluations, realized candidates, product-agenda operations, frontier operations, stored sibling entries, and performance by sentence length.

## Acceptance Criteria

- A* scores match exhaustive parsing; specialized and forced-generic string paths are bit-identical.
- Built-in heuristics have no structural reopenings.
- Binary-string candidate counts do not regress.
- Each retained phase improves median parse time or peak RSS without material regression in the other.
- Lazy remains explicit and experimental unless it wins reproducibly after eager optimization.
- Full tests, Clippy, `eval --limit 100`, and a complete PTB run pass.

## Assumptions

- Binary string parsing is the principal optimized workload, not a correctness assumption.
- String yield templates remain private to the string specialization.
- Arbitrary algebras require only `CondensedTa`.
- `lazy_span.rs` remains available for controlled experimentation.
