# Changelog

## Changes in 0.2.3 (2026-09-11)

- Sorted-language enumeration is substantially faster and now checks its
  probability-weight contract; Python `k_best` follows the same ordering.
- Feature-structure evaluation and unification now reuse a workspace graph,
  avoiding much of their previous allocation and copying.
- Explicit automata use denser rule and state-stream indexes, and the lazy
  string A* frontier remains available as an opt-in experiment.
- `packed-term-arena` was bumped to 0.1.3 and the minimum Rust version to 1.88.
- Crates.io packages no longer contain benchmarks, and a matching `vX.Y.Z` tag
  now tests and publishes the crate automatically.

## Changes in 0.2.2 (2026-09-07)

- Restored the performance of finite-language enumeration and automaton
  trimming with compact derivation nodes, reusable traversal storage, and a
  fast path for builders whose states are known to be productive.
- Corrected the cross-platform Python test and wheel workflow.

## Changes in 0.2.1 (2026-09-07)

- Finite explicit languages can be enumerated without sorting and counted with
  either checked machine integers or arbitrary-precision integers.
- Explicit automata can be trimmed while they are built, with a stable mapping
  between original and retained states.
- Introduced Python bindings for explicit and lazy automata, combinators,
  algebras, IRTG parsing, Viterbi extraction, and language inspection.

## Changes in 0.2.0 (2026-06-21)

- Expanded the initial tree-automata library into an Alto-compatible IRTG
  toolkit with `.irtg` grammars, corpora, condensed parsing, Viterbi extraction,
  sorted languages, and EVALB-style Parseval scoring.
- Introduced exact one-best A* parsing with zero, outside, SX, and SXF
  heuristics, including prepared indexes for repeated string parsing.
- Added string, tree, TAG string, TAG tree, and feature-structure algebras;
  Tulipac `.tag` grammars compile directly to IRTGs.
- The `eval` command and interactive parser cover batch, parallel, cancellable,
  and feature-filtered parsing workflows.
- Typed input and output codec registries, structured visualization values, and
  application-facing summaries support graphical frontends without coupling
  them to parser internals.
- Tree storage moved to `packed-term-arena`, and the Rust API, performance
  notes, comparison tools, and publishing infrastructure were consolidated.

## Changes in 0.1.0 (2026-06-13)

- Initial Rust implementation of weighted bottom-up tree automata with
  Alto-compatible `.auto` input.
- Explicit and on-demand automata share a small oracle-style API, with products,
  determinization, memoization, materialization, and deterministic and
  nondeterministic tree runs.
- Included the first Alto comparison harness and benchmarks for the core data
  structures and algorithms.
