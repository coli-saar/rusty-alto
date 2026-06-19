# Development and performance

## Repository map

| Path | Role |
| --- | --- |
| `src/traits.rs` | Core automaton capabilities. |
| `src/explicit.rs` | Stored weighted automata and lazy indexes. |
| `src/combinators/` | Product, inverse homomorphism, mapping, determinization. |
| `src/algebras/` | Algebra interfaces and string/tree implementations. |
| `src/irtg.rs` | Interpretations and the high-level parsing API. |
| `src/materialize.rs` | General and condensed chart construction. |
| `src/astar.rs`, `src/astar/` | Exact one-best search and specialized indexes. |
| `src/run.rs`, `src/viterbi.rs`, `src/sorted_language.rs` | Automaton consumers. |
| `src/corpus.rs`, `src/parseval.rs` | Corpus I/O and evaluation. |
| `src/bin/eval.rs` | Main corpus parsing frontend. |
| `tools/alto-compare/`, `scripts/` | Cross-language benchmarks against Alto. |
| `docs/` | Detailed experiment reports and implementation notes. |

## Local build

`rusty-tree` is currently a sibling path dependency:

```text
workspace/
  rusty-alto/
  rusty-tree/
```

From `rusty-alto`:

```sh
cargo test
cargo doc --no-deps --all-features
cargo build --release --bin eval
```

Release mode is essential for meaningful parser timings.

## Documentation maintenance

The `Documentation` GitHub Actions workflow checks out both repositories and
builds rustdoc with warnings treated as errors. Pull requests therefore catch
stale intra-doc links and invalid examples. Successful builds on `main` publish
the result to GitHub Pages.

Wiki source lives in `wiki/` in the main repository. The `Wiki` workflow
synchronizes it to GitHub's separate wiki repository after changes reach
`main`. Keeping the source beside the code makes architectural edits reviewable
in normal pull requests.

## Performance principles

- Start with a clean, algebra-independent abstraction.
- Add specialization for measured common cases, especially rule arities up to
  two and deterministic transitions.
- Avoid per-query allocation in transition and join hot paths.
- Build expensive indexes lazily.
- Use dense IDs, `FxHashMap`, borrowed hash lookups, and small inline buffers
  where profiling supports them.
- Preserve a correct general fallback when a specialization does not apply.

The current string A* implementation illustrates this approach. A general
candidate generator handles arbitrary condensed automata and rule arities. A
product-aware span sibling finder accelerates unary and binary string rules
without changing the public A* or automaton interfaces.

## Comparing with Alto

Alto's source is the first place to look when an algorithmic choice is subtle,
especially for IRTG parsing and language enumeration. The Java harnesses under
`tools/alto-compare/` run equivalent workloads through Alto; scripts under
`scripts/` compare outputs and timings.

Before accepting a performance change:

1. Verify semantic equality with unit tests and, where relevant, Alto output.
2. Measure a representative release workload.
3. Record counters that explain the change, not just wall-clock time.
4. Keep the simpler general path unless the specialization has a demonstrated
   benefit.

Historical measurements and active bottleneck analyses live in `docs/`, in
particular `docs/performance.md`, `docs/benchmark-results.md`, and the A*
design notes.
