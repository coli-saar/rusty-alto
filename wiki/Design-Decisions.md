# Design decisions

## Automata are transition oracles

The base API asks an automaton to answer a local transition query. This is
smaller and more compositional than requiring every automaton to expose a
stored rule collection.

An explicit automaton is therefore viewed as a fully materialized cache of an
implicit one. Algebra decomposition automata and combinators can remain lazy,
while algorithms that need a finite rule set can materialize them.

## Capabilities are refinement traits

Bottom-up stepping, determinism, top-down enumeration, indexed joins,
condensation, and finite-state enumeration are distinct capabilities. Combining
them into one trait would force slow generic implementations or make useful
implicit automata impossible to express.

Algorithms state the strongest capability they can exploit and provide
separate fallbacks where appropriate.

## Optimize common arities without changing the model

Nullary, unary, and binary rules dominate the intended grammar workloads.
`Explicit` and the A* string path specialize these cases to reduce allocation,
hashing, and sibling search.

Rules of arbitrary arity remain part of the same public abstraction and use
general paths. This is a deliberate boundary: specializing a common structural
case is useful; baking a single algebra or one parser construction into the
core automaton API is not.

## Condensation belongs at the automaton boundary

In IRTGs, many grammar symbols can have the same homomorphic image. Evaluating
that image separately for every symbol wastes work. `CondensedTa` groups labels
that share a transition shape, so materializers can evaluate once and carry a
symbol set through the join.

This generalizes beyond string inverse homomorphism and therefore lives in the
automaton interface rather than in an IRTG-specific parser.

## Indexes are lazy and independent

An explicit automaton may be used for bottom-up runs, top-down traversal,
partial-child joins, condensed enumeration, or several of these. Building all
indexes eagerly would increase construction time and memory for access
patterns that may never occur.

Each index is cached on first use. The trade-off is interior synchronization
and a slightly more complex implementation, in exchange for making large parse
charts pay only for the queries they receive.

## Dense IDs and sentinel states

Symbols and explicit states use small integer IDs. Dense IDs improve hash keys
and permit vector-backed side data. Deterministic runs use
`StateId::STUCK` as a rejection sentinel, which avoids wrapping every node state
in `Option`.

Rich state values are still supported by the base trait. `Memo` is the explicit
boundary where they are interned when dense storage becomes valuable.

## Callback-based enumeration

Transition and rule enumeration methods accept callbacks. This keeps the
traits object-safe, permits implementations to lend internal slices for the
duration of a call, and avoids allocating a fresh result collection for every
query.

The callback contract requires duplicate-free results. Ordering is generally
unspecified unless a higher-level iterator explicitly provides it.

## Separate chart construction from one-best search

A full parse chart is valuable when callers need more than one derivation or
want to run further automaton algorithms. It is unnecessary overhead when only
the best parse matters.

The API therefore supports both materializing intersections and direct A*
one-best search. They share automaton and scoring abstractions, but do not force
one execution shape on the other.

## Use Alto as an algorithmic reference, not an API template

Alto is the compatibility target and a major source of algorithmic ideas:
interpreted grammars, condensed inverse homomorphism, sibling-finder-style
intersection, and sorted language enumeration.

The Rust implementation keeps those semantic lessons while using ownership,
dense storage, borrowed lookups, and monomorphized fast paths where they make
the implementation cleaner or faster.

## Keep general tree functionality in packed-term-arena

`rusty-alto` uses `packed-term-arena` as its arena representation. General operations
such as traversal, copying, parsing, or tree display should be proposed for
`packed-term-arena` rather than reimplemented locally. This repository should contain
tree code only when it is specific to automata, grammars, or evaluation.
