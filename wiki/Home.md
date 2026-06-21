# rusty-alto technical overview

`rusty-alto` is a Rust implementation of weighted tree automata and interpreted
regular tree grammars (IRTGs), designed to consume Alto-compatible data while
offering a clean compositional API and efficient parsing algorithms.

The main pieces are:

- an oracle-style interface for bottom-up tree automata;
- an explicit, indexed automaton representation;
- lazy automaton combinators;
- algebras, homomorphisms, and IRTG interpretations;
- typed input/output codec registries and algebra-owned display codecs;
- TAG string, TAG derived-tree, and feature-structure algebras;
- materialization and A* algorithms that turn composed automata into parse
  charts or one-best derivations;
- runners, Viterbi extraction, corpus I/O, and evaluation tools.

Start here:

- [Architecture](Architecture) follows data through the main modules.
- [Parsing pipeline](Parsing-Pipeline) explains how an IRTG and an input
  sentence become a derivation.
- [Choosing a parsing algorithm](Parsing-Algorithms) compares the user-facing
  strategies, their trade-offs, and cooperative cancellation.
- [Codec infrastructure](Codec-Infrastructure) explains format discovery,
  algebra value visualization, and the GUI integration boundary.
- [Design decisions](Design-Decisions) records the abstractions and
  performance trade-offs that shape the implementation.
- [Development and performance](Development-and-Performance) describes the
  repository layout, testing, benchmarking, and the relationship with Alto and
  `packed-term-arena`.

For the public Rust API, see the
[generated cargo documentation](https://docs.rs/rusty-alto).
For command-line usage, see the
[README](https://github.com/coli-saar/rusty-alto#readme) and
[`docs/eval.md`](https://github.com/coli-saar/rusty-alto/blob/main/docs/eval.md).
