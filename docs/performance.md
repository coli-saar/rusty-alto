# Performance Implementation Decisions

This document describes the current performance-oriented implementation choices
in `rusty-alto`. Benchmark procedures and measured results live in
[`benchmark-results.md`](benchmark-results.md).

Keep this document focused on design decisions, hot-path data structures, and
known implementation tradeoffs.

## Core Model

The library treats a bottom-up tree automaton as an oracle. The
[`BottomUpTa`](../src/traits.rs) trait answers one hot-path question: given a
node symbol and the states assigned to the node's children, which states can the
node itself receive?

This shape keeps explicit automata, implicit automata, memoized automata, and
combinators behind one interface. It also makes the execution engine responsible
for tree traversal and temporary state storage, while each automaton
implementation focuses on answering transition queries quickly.

The deterministic companion trait, `DetBottomUpTa`, exposes the same query in a
single-result form. Runners and combinators use it when determinism is known,
which avoids result-set allocation and tuple enumeration.

## Dense Identifiers

Runtime execution uses dense IDs:

- `Symbol` for labels.
- `StateId` for explicit or memoized states.
- `NodeId` for tree arena nodes.

Dense IDs make per-node side tables cheap: vectors indexed by `NodeId` or
`StateId` replace maps in the common execution path. This is especially
important for deterministic runs, where each tree node stores one state.

All automaton runs are raw-symbol runs. The core [`Arena`](../src/arena.rs)
trait returns `Symbol` from `symbol(node)`, so runners never compare label
strings. Loading code should use [`Signature`](../src/signature.rs) to intern
external labels once, then store raw `Symbol`s in the tree arena. This is the
same performance boundary as Alto's `runRaw`, but it is the only execution mode
in this library rather than a separate API.

`StateId::STUCK` is reserved as a deterministic rejection sentinel. It lets the
deterministic runner store `StateId` directly instead of `Option<StateId>` for
each node. A separate visited bitset records whether a node has been computed,
so shared rejected nodes in a DAG-like arena are not recomputed.

## Explicit Automata

[`Explicit`](../src/explicit.rs) is the materialized automaton representation.
It stores transition rules canonically in one rule vector and builds lookup
indexes on demand. Bottom-up queries use arity-specialized indexes:

- arity 0: `(symbol) -> states`
- arity 1: `(symbol, child) -> states`
- arity 2: `(symbol, left, right) -> states`
- arity > 2: `(symbol, boxed child tuple) -> states`

The arity 0, 1, and 2 indexes are the optimized path because these arities cover
the target Phase 1 workloads. They avoid boxed tuple keys, avoid per-query
allocation, and keep hash keys small and copyable.

These bottom-up indexes are lazy. Building large parse charts can produce tens
of millions of explicit rules, while the next consumer may only need top-down
access for Viterbi. Deferring bottom-up index construction keeps chart
materialization from paying for an access pattern the caller never uses. The
first ordinary `step` or `step_det` query builds the bottom-up indexes once and
reuses them thereafter.

Higher arities remain supported, but they use a generic boxed-key table with a
borrowed lookup key. That keeps correctness and API coverage without making
rare high-arity rules shape the common case.

`Explicit::step_det` checks whether a query has exactly one result state. This
allows deterministic clients to query the explicit index directly while still
sharing storage with nondeterministic automata.

`Explicit::reachable_states()` caches its saturated result. Explicit automata
are immutable after construction, so repeated reachability and emptiness checks
can clone a cached bitset instead of rerunning saturation.

`Explicit` also builds indexed and top-down indexes lazily. The first indexed
query constructs a child-position index from `(symbol, position, child state)`
to matching rules. The first top-down query constructs a parent-state index from
`result state` to matching rules. These indexes are independent: Viterbi and
top-down chart traversal do not force bottom-up indexes, and bottom-up
recognition does not force top-down indexes.

Condensed rule enumeration is cached lazily as well. `Explicit::condensed_rules`
groups rules by `(children, result)` and stores the corresponding `SymbolSet`
after the first request. This avoids rebuilding a hash map every time condensed
algorithms, especially inverse homomorphism, enumerate the same explicit
automaton.

`Explicit` implements `StateUniverse` by enumerating dense
`StateId(0)..StateId(num_states-1)`. This is intentionally separate from
ordinary bottom-up querying: most runs never need a full state universe, but
complete condensed inverse homomorphism needs it for image terms that are just a
bare variable.

## Implicit Automata And Memoization

Implicit automata can expose arbitrary state types. [`Memo`](../src/memo.rs)
bridges those automata into the dense `StateId` execution world.

On a cache miss, `Memo`:

1. resolves dense child IDs back to inner state values,
2. calls the wrapped automaton,
3. interns any returned states into dense `StateId`s,
4. stores the dense result set for the query.

On a cache hit, `Memo` replays the cached dense result by borrow instead of
cloning a temporary `SmallVec`. This matters for repeated runs over an implicit
automaton, where transition-query caching should become nearly pure lookup.

## Tree Execution

[`run_det`](../src/run.rs) and `run_nondet` traverse the tree arena bottom-up and
store results in side tables keyed by `NodeId`.

The deterministic runner stores one `StateId` per node plus the visited bitset
described above. Rejected subtrees receive `StateId::STUCK`; accepted roots are
checked against the automaton's final-state set.

The nondeterministic runner stores sorted small state sets. During tuple
enumeration it borrows child state slices rather than cloning every child set
into temporary vectors. This is a low-level but important detail: binary
branching with small sets is common, and cloning on every parent query creates
avoidable memory traffic.

The current tuple enumeration is intentionally simple and optimized for small
arity. Higher-arity nondeterminism is correct but exponential in the product of
child set sizes.

## Indexed Enumeration

[`IndexedBottomUpTa`](../src/traits.rs) is the Phase 2 sibling-finder-style
refinement. Instead of asking for the result of a complete child tuple, callers
can ask for every rule with a fixed symbol, child position, and child state.
This avoids enumerating child tuples that are absent from the rule relation.

`Explicit` answers indexed queries from its lazy child-position index. `Memo`
forwards indexed queries when the wrapped automaton supports them, interning any
states exposed by the inner automaton. `Product` implements indexed enumeration
when both components do: it queries both sides for partial matches and joins
only rules with the same symbol and arity.

This gives the automata engine the core primitive needed by sibling-finder-like
intersection and parsing algorithms. Chart construction, Viterbi, and EM still
need to consume this trait explicitly to get the asymptotic benefit.

## Combinators

[`Product`](../src/combinators/product.rs) has two execution paths.

The generic `BottomUpTa` path queries both component automata and combines their
result sets. It uses inline `SmallVec` buffers for the common case where each
side returns one or two states, avoiding heap allocation in small products.

When both components implement `DetBottomUpTa`, the product also implements
`DetBottomUpTa`. The deterministic path queries each side once and returns one
paired state if both sides accept the child tuple. This is the preferred path
for deterministic intersection workloads.

When both components implement `IndexedBottomUpTa`, the product exposes an
indexed join. This does not replace the generic `BottomUpTa` implementation;
algorithms that require fast enumeration should bound their inputs by
`IndexedBottomUpTa` directly.

[`Determinized`](../src/combinators/determinized.rs) is currently a portable
correctness baseline. It uses `BTreeSet` to represent subset states. A future
high-performance determinization path should use dense `StateId` bitsets and be
benchmarked separately before replacing the generic version.

[`Mapped`](../src/combinators/mapped.rs) is a one-way symbol-remapping view. It
translates external `Symbol`s before querying the wrapped automaton and forwards
bottom-up, deterministic, and indexed bottom-up queries. It intentionally does
not implement top-down enumeration because that would require an inverse symbol
map.

[`Homomorphism`](../src/homomorphism.rs) stores right-hand side terms as roots
in a caller-owned `TreeArena<HomLabel>`. The homomorphism itself stores raw
`Symbol`s, source arities, structural term IDs, and label sets. This keeps RHS
terms compatible with external signatures and tree arenas, and it makes the
normal run path equivalent to Alto-style raw-symbol execution: there is no
separate string-labeled `run` mode.

Construction validates the nondeleting invariant once. For a source symbol of
arity `k`, variables `?0 .. ?{k-1}` must occur exactly once in the RHS tree.
After that, inverse-homomorphism evaluation can substitute child states without
rechecking variable coverage on every transition query.

Structurally identical RHS trees are deduplicated even if they are represented
by different arena nodes. Each unique term has a label set containing all source
symbols with that image. Condensed inverse homomorphism uses these label sets to
emit one grouped rule for many source labels instead of evaluating the same RHS
once per label.

[`InvHom`](../src/combinators/invhom.rs) keeps complete bottom-up,
deterministic bottom-up, and condensed implementations. Its old indexed and
top-down implementations were removed because they only handled a subset of RHS
shapes. Complete condensed evaluation recursively matches RHS symbol nodes
against inner condensed rules, merges partial variable assignments, handles
ground subterms, and uses `StateUniverse` for bare-variable roots. The generic
`step` implementation deduplicates result states before invoking the caller's
callback, preserving the `BottomUpTa` no-duplicates contract even when an inner
oracle emits duplicates.

## Top-Down Enumeration

[`TopDownTa`](../src/traits.rs) is the Phase 2 top-down refinement. It
enumerates rules by parent state and reports the bottom-up initial states,
which are the accepting states. `Explicit` answers top-down queries from its
lazy parent-state index. `Memo` and `Product` forward top-down queries when
their components support them.

## Materialization

Materialization converts a finite implicit automaton fragment into an
[`Explicit`](../src/explicit.rs) automaton. The current implementation is tuned
for arity <= 2 and finite state/symbol domains.

An attempted query-deduplication set inside materialization was rejected after
benchmarking. It looked plausible, but the extra hashing cost outweighed saved
memo queries in the current arity <= 2 workload.

## Alto Format And Comparison Runner

[`parse_alto`](../src/alto.rs) reads Alto-style `.auto` files into explicit
automata. The comparison binary, [`compare_alto`](../src/bin/compare_alto.rs),
uses the parsed automaton plus a tree-per-line input file as a joint workload
for Rust and Alto comparisons.

`parse_alto_with_signature` accepts a caller-owned
[`Signature`](../src/signature.rs). Use it when an automaton and one or more
tree inputs should be compiled into the same label ID space. The ordinary
`parse_alto` helper creates a fresh signature and returns it as part of the
parsed automaton.

The Rust runner detects deterministic automata by checking whether any
`(symbol, child tuple)` key has more than one result state. Deterministic inputs
use the dense `run_det`-style path; nondeterministic inputs use sorted state
sets.

[`compare_condensed_parsing`](../src/bin/compare_condensed_parsing.rs) is the
current parser-like comparison benchmark. It builds a source tree automaton,
maps its labels into `StringAlgebra` terms with a homomorphism, wraps a string
decomposition automaton in condensed inverse homomorphism, and materializes the
intersection. The Rust materializer uses fast hash tables and inline arity <= 2
child tuples because the output chart can contain millions of binary rules.
The companion script,
[`compare-condensed-parsing.sh`](../scripts/compare-condensed-parsing.sh),
compares this path against Alto's `CondensedNondeletingInverseHomAutomaton` and
`intersectCondensed`.

## Current Bottlenecks

The condensed parsing benchmark now supports both explicit CKY-style string
decomposition and lazy `StringAlgebra` decomposition. Its indexed-condensed
intersection path avoids eagerly collecting the full inverse-hom rule relation;
the next benchmark gap is less-saturating grammars where this can translate
right-side query reductions into larger wall-clock wins.

High-performance parsing still needs reusable library algorithms, not only
benchmark-local materializers, that consume `IndexedBottomUpTa` and
`CondensedTa`. The automata engine exposes the sibling-finder-style and
condensed primitives. Chart construction now returns explicit charts whose
indexes are demand-driven, and [`Explicit::viterbi`](../src/viterbi.rs) provides
a direct one-best extraction path that avoids the heavier k-best sorted-language
iterator when only the best derivation is needed. EM still needs library-level
APIs.

Generic determinization still uses `BTreeSet`. This is simple and correct, but
not the intended final representation for dense-state workloads.

Materialization and nondeterministic execution are optimized for arity <= 2.
Higher arities are supported as a fallback, but they should not be treated as a
performance target until more specialized indexed or symbolic enumeration
exists.
