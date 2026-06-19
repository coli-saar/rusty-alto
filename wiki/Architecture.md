# Architecture

## Conceptual layers

```text
Alto files and corpora
        |
        v
 parsers + signatures  ----->  explicit grammar automaton
        |                              |
        v                              v
 interpretations  -----> homomorphisms + algebra decomposition automata
                                       |
                                       v
                         inverse homomorphism + intersection
                                       |
                           +-----------+-----------+
                           |                       |
                           v                       v
                    materialized chart       A* one-best search
                           |                       |
                           +-----------+-----------+
                                       v
                         derivation tree / interpreted values
```

The layers deliberately meet through small traits rather than through one
large grammar or parser type. This keeps an explicit automaton, a decomposition
automaton, and a composed automaton interchangeable wherever they offer the
same capabilities.

## Core identifiers and signatures

`ids.rs` defines compact `Symbol` and `StateId` values. Dense integer IDs make
transition tables, side arrays, and hash keys cheap. `StateId::STUCK` is
reserved for failed deterministic runs, avoiding an `Option<StateId>` at every
tree node.

`interner.rs` maps application-level values to dense IDs. `signature.rs`
associates terminal names with symbols and enforces a single arity for each
name. Signatures are kept explicit because different automata may use different
symbol spaces.

## Automaton traits

`BottomUpTa` is the base interface:

```rust
fn step(&self, symbol: Symbol, children: &[State], out: &mut dyn FnMut(State));
fn is_accepting(&self, state: &State) -> bool;
```

It treats an automaton as a transition oracle. The rules may be stored,
computed, or delegated to other automata.

Algorithms opt into stronger refinement traits when they need more structure:

| Trait | Capability |
| --- | --- |
| `DetBottomUpTa` | Return at most one parent state without callback overhead. |
| `IndexedBottomUpTa` | Find rules from one known child state and position. |
| `CondensedTa` | Group symbols that share a child/result transition shape. |
| `TopDownTa` | Enumerate rules from a parent state. |
| `CondensedTopDownTa` | Combine condensed labels with top-down enumeration. |
| `StateUniverse` | Enumerate all states of a finite automaton. |

Keeping these capabilities separate prevents the weakest useful abstraction
from inheriting expensive or impossible enumeration requirements.

## Explicit automata

`explicit.rs` contains `Explicit` and `ExplicitBuilder`. The builder validates
and canonicalizes weighted rules. The resulting automaton stores rules once
and builds query indexes lazily.

The bottom-up hot path has specialized indexes for arities zero, one, and two,
because these dominate grammar workloads. Higher arities use a general
borrowed-key lookup. Top-down, partial-child, and condensed indexes remain
independent, so an automaton only pays for access patterns that are actually
used.

`Explicit` is both a normal automaton and the materialized output of parsing
and composition algorithms.

## Lazy combinators

The types in `combinators/` construct automaton views without copying all
rules:

- `Product<A, B>` recognizes the intersection of two tree languages.
- `InvHom<A>` pulls an automaton back through a tree homomorphism.
- `Mapped<A, F>` changes the symbol view.
- `Determinized<A>` performs subset construction.

`Memo<A>` bridges rich implicit state types and algorithms that benefit from
dense `StateId`s. It interns states and caches discovered transitions, and can
be frozen into an `Explicit` automaton.

## Trees and runs

`rusty-tree` owns the general tree arena and parser. `run.rs` evaluates an
automaton over a tree in post-order. Deterministic and nondeterministic runners
are separate so the deterministic path can use one state per node.

Tree operations that are broadly useful belong in `rusty-tree`; `rusty-alto`
should only add automaton-specific tree logic.

## IRTGs and algebras

An `Irtg` contains:

- an explicit weighted grammar automaton;
- the grammar signature and state names;
- named interpretations.

Each interpretation combines an algebra, an algebra signature, and a
homomorphism from grammar symbols to algebra terms. Currently, string algebras
can decompose observed inputs into automata. Tree-with-arities algebras can
evaluate derivations but are output-only.

`alto_ast.rs`, `alto_grammar.lalrpop`, `alto.rs`, and `irtg.rs` implement the
Alto-compatible syntax and construct the runtime representation.

## Results and evaluation

Materialization produces an `Explicit` parse chart. `viterbi.rs` extracts its
best weighted derivation, while `sorted_language.rs` enumerates derivations in
weight order.

`corpus.rs` reads and writes Alto corpus files. `parseval.rs` compares predicted
and gold constituency trees using EVALB-style normalization and constituent
counts. The `eval` binary joins these pieces into the main corpus-processing
frontend.
