# rusty-alto

A fast Rust library for bottom-up tree automata, with support for interpreted regular tree grammars (IRTGs) in the [Alto](https://github.com/coli-saar/alto) format.

## What this is

**Tree automata** generalize finite-state automata from strings to trees. A bottom-up tree automaton reads a tree from its leaves upward: each leaf receives a state, and each internal node receives a state based on its symbol and the states of its children. If the root ends up in an accepting state, the tree is accepted.

This library treats every automaton — whether its rules are stored in a table or computed on demand — as an oracle: given a symbol and child states, tell me the possible parent states. Explicit automata are just a materialized cache of this oracle. That insight unifies explicit and implicit automata behind one trait and lets the library compose them freely.

**Alto** is a Java toolkit for IRTGs developed at Saarland University. `rusty-alto` takes significant inspiration from Alto's design and algorithms — the oracle-trait model, the condensed inverse-homomorphism construction, the sibling-finder-style indexed join, and the sorted language iterator all trace their lineage directly to Alto. The library also reads Alto's `.auto` and `.irtg` file formats so that grammars produced by Alto tooling can be used without conversion.

## Connection to Alto

Alto represents grammars as interpreted regular tree grammars. An IRTG consists of a core tree automaton (the grammar) and one or more *interpretations*, each mapping grammar derivation trees into objects from some algebra — strings, dependency graphs, logical formulas, and so on.

`rusty-alto` reads Alto's IRTG format directly and uses the same parsing strategy:

```
interpretation english: de.up.ling.irtg.algebra.StringAlgebra

S! -> r(NP, VP) [1.0]
  [english] *(?1, ?2)

NP -> john_rule
  [english] john

VP -> watches_rule
  [english] watches
```

Given an IRTG and an observed string, the library performs parsing by intersecting the grammar with a decomposition automaton for the input, using an efficient condensed inverse-homomorphism construction. The result is a parse chart — an explicit automaton whose derivations are exactly the analyses of the input.

```rust
use rusty_alto::*;

let irtg = parse_irtg(std::fs::File::open("grammar.irtg")?)?;
let english = irtg.interpretation::<StringAlgebra>("english")?;
let value = english.parse_object("john watches")?;
let chart = irtg.parse([english.input(value)])?;

if chart.automaton.is_empty() {
    println!("no parse");
    return;
}
println!("accepted — {} rules in chart", chart.automaton.rules().count());

// Extract the top-1 derivation tree in descending weight order.
let mut lang = chart.automaton.sorted_language();
if let Some(best) = lang.next() {
    println!("top-1 weight: {:.6}", best.weight());

    // Map Symbol labels to strings, then display using the arena's built-in formatter.
    let sig = irtg.grammar_signature();
    let mut named: rusty_tree::tree::TreeArena<String> = rusty_tree::tree::TreeArena::new();
    let named_root = lang.arena().map(best.tree(), |sym| sig.resolve(*sym).to_owned(), &mut named);
    println!("{}", named_root.display(&named));
    // e.g. "r(john_rule, watches_rule)"
}
```

## Core concepts

### `BottomUpTa` — the oracle trait

Every automaton in the library implements `BottomUpTa`. The single hot-path method:

```rust
fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State));
```

Explicit automata answer this query with a hash-map lookup. Implicit automata compute the answer on demand. Combinators delegate to their components.

### `Explicit` — the materialized form

`Explicit` stores rules in arity-specialized hash maps for arity 0, 1, and 2, covering the common cases without per-query allocation. Higher arities are supported via a borrowed-key lookup that also avoids allocation.

Build one with `ExplicitBuilder`:

```rust
let mut sig = Signature::new();
let a = sig.intern("a".to_owned(), 0).unwrap();
let f = sig.intern("f".to_owned(), 2).unwrap();

let mut builder = ExplicitBuilder::new();
let leaf = builder.new_state();
let root = builder.new_state();
builder.add_rule(a, vec![], leaf);
builder.add_rule(f, vec![leaf, leaf], root);
builder.add_accepting(root);
let automaton = builder.build();
```

### Running an automaton

```rust
let run = run_det(&automaton, &tree, root_node);
assert!(automaton.is_accepting(&run.root_state));
```

Use `run_det` when the automaton is deterministic (at most one result state per symbol/children tuple). Use `run_nondet` for the general case.

### Combinators

| Type | Description |
|------|-------------|
| `Product<A, B>` | Intersection: accepts trees in both `L(A)` and `L(B)` |
| `InvHom` | Inverse homomorphism: pull back rules through a homomorphism |
| `Mapped<A, F>` | Symbol remapping view |
| `Determinized<A>` | Subset construction, turning any automaton deterministic |

### `Memo<A>` — bridging implicit to explicit

When an implicit automaton has its own rich state type (strings, tuples, syntax objects), wrap it in `Memo` to cache transitions and expose dense `StateId` values to runners and combinators. Freeze with `into_explicit()` when all reachable states have been discovered.

### Materialization

`materialize()` saturates a finite implicit automaton into an `Explicit` by seeding from nullary rules and repeatedly applying transitions until no new states appear.

`materialize_topdown_condensed_intersection()` is the parsing workhorse: it drives the condensed inverse-homomorphism construction top-down, building the parse chart while avoiding the exponential blowup of naive Earley-style approaches.

## Refinement traits

Some algorithms need to enumerate rules, not just query them on demand. The refinement traits provide this:

- **`IndexedBottomUpTa`** — given a symbol, child position, and state at that position, enumerate all matching rules. This is the sibling-finder primitive (Groschwitz et al., ACL 2016) that makes intersection-based parsing asymptotically tractable.
- **`CondensedTa`** — enumerate rules grouped by transition shape: many grammar symbols often share the same homomorphic image, so one evaluation covers the whole group.
- **`TopDownTa`** — enumerate rules by parent state.
- **`StateUniverse`** — enumerate all states in a finite automaton; needed by condensed inverse homomorphism when an image term is a bare variable.

Slow blanket fallbacks exist where possible, so you can compose automata before adding fast trait impls.

## Performance

The library is designed to be competitive with Alto on the workloads that motivated it:

- `FxHashMap` (via `rustc-hash` + `hashbrown`) throughout — SipHash is too slow for integer-keyed inner loops.
- `StateId::STUCK` sentinel instead of `Option<StateId>` in the deterministic run side table.
- `SmallVec<[_; 4]>` for child-state buffers — most tree nodes have arity ≤ 4.
- Arity-specialized indexes in `Explicit` built lazily on first use.
- Condensed rule enumeration cached after the first request.
- DAG-friendly runner that skips already-computed nodes.

See [`docs/performance.md`](docs/performance.md) for a detailed account of design decisions and known bottlenecks.

## Comparing with Alto

The `tools/alto-compare/` directory contains Java harnesses that run equivalent workloads through Alto. Shell scripts in `scripts/` drive both sides and print timing summaries:

```sh
./scripts/compare-alto.sh
./scripts/compare-condensed-parsing.sh
./scripts/compare-intersection.sh
```

## License

To be determined.
