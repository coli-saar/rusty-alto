# Python bindings

The `rusty_alto` Python package exposes the core of the Rust library —
weighted tree automata, lazy decomposition automata, native combinators, and
IRTG parsing — through [PyO3](https://pyo3.rs). It ships a typed stub
(`py.typed`), so editors and type checkers see the full API.

This page is the user-facing reference. For how the binding crate is built and
how to extend it, see
[`docs/python-bindings-internals.md`](https://github.com/coli-saar/rusty-alto/blob/main/docs/python-bindings-internals.md).

## Installing

There is no published wheel yet; build from a checkout with
[maturin](https://www.maturin.rs).

```sh
python -m venv .venv
source .venv/bin/activate
pip install maturin pytest
maturin develop --release      # builds and installs into the active venv
pytest bindings/python/tests
```

Use `maturin develop` (debug) for quick iteration and `--release` for anything
resembling a real grammar — decomposition and parsing are far slower without
optimizations. Release wheels target CPython's stable ABI (`abi3`) for Python
3.9 and newer, so a single wheel works across interpreter versions.

```python
import rusty_alto as ra
print(ra.__version__)
```

## Core model

An **automaton** is a transition oracle, not necessarily a stored table. The
same `Automaton` class wraps two kinds of object:

- **Explicit** automata — a finite, weighted rule table. These come from
  `AutomatonBuilder`, `load_automaton`, an IRTG grammar, a parse chart, or
  `Automaton.materialize()`. Only explicit automata support weighted queries
  (`rules`, `viterbi`, `k_best`, `language_cardinality`).
- **Lazy** automata — transitions computed on demand. Algebra decompositions
  and the combinators (`product`, `determinize`, `map_symbols`,
  `inverse_homomorphism`) stay lazy until you explicitly `materialize()` them.

### Capabilities

Different automata answer different queries. Inspect what an automaton supports
through read-only properties; calling an unsupported method raises
`UnsupportedOperationError` rather than returning a wrong answer.

| Property | True when the automaton can… |
| --- | --- |
| `is_deterministic` | give at most one parent per transition (`step_deterministic`) |
| `has_state_universe` | enumerate every state (`states`) |
| `is_top_down` | enumerate `initial_states` and `rules_for_parent` |
| `is_indexed` | answer `rules_for_child` (indexed bottom-up joins) |
| `is_condensed` | answer `condensed_rules` (multiple labels sharing a transition) |

`repr(automaton)` prints all five flags at a glance.

### State ownership

Each automaton instance has a hidden owner id, and every `State` it produces
records that id. Passing a state into a *different* automaton raises
`StateOwnerError`. This prevents silently mixing dense state IDs or implicit
state domains that happen to look alike.

```python
left = ra.StringAlgebra().decompose("a")
right = ra.StringAlgebra().decompose("a")
state = left.step("a", [])[0]
right.is_accepting(state)        # raises StateOwnerError
```

States are hashable and comparable, so you can use them as dict keys or set
members within a single automaton.

## Building an explicit automaton

`AutomatonBuilder` builds a weighted automaton by naming states and adding
rules. State names are arbitrary strings; rule weights default to `1.0`. The
symbol's arity is fixed by the number of children the first time you use it.

```python
builder = ra.AutomatonBuilder()
builder.add_state("leaf")
builder.add_state("root", accepting=True)
builder.add_rule("a", [], "leaf")            # nullary rule, weight 1.0
builder.add_rule("f", ["leaf"], "root", 0.5) # unary rule, weight 0.5
automaton = builder.build()

automaton.accepts(ra.Tree("f", [ra.Tree("a")]))   # True
automaton.viterbi().weight                          # 0.5
```

`build()` consumes the builder; call it once.

### Running and inspecting

```python
automaton.run(tree)              # bottom-up: states reachable at the root
automaton.accepts(tree)          # any reachable root state accepting?
automaton.step("f", [leaf])      # one bottom-up transition step
automaton.states()               # all states (needs has_state_universe)
automaton.rules()                # (symbol_id, [child_ids], parent_id, weight) — explicit only
automaton.viterbi()              # best WeightedTree, or None — explicit only
automaton.k_best(5)              # up to 5 best WeightedTrees — explicit only
automaton.language_cardinality() # ("finite", n) | ("infinite", None) | ("too_large", None)
```

`Tree(label, children=[...])` is a simple immutable term. `str(tree)` renders
the usual `f(a, b)` notation; `tree.label` and `tree.children` walk it.

## Lazy decomposition and combinators

Algebras turn a value into a lazy decomposition automaton whose language is the
set of terms evaluating to that value.

```python
decomposition = ra.StringAlgebra().decompose("john sleeps")
decomposition.is_condensed          # True
decomposition.states()              # spans over the input
```

The combinators are all lazy — they compose oracles without materializing:

```python
product        = left.product(right)             # synchronous product
deterministic  = product.determinize()           # on-the-fly subset construction
renamed        = automaton.map_symbols(sig, m)    # relabel transitions
preimage       = inner.inverse_homomorphism(hom)  # inverse homomorphism
```

`materialize()` is the one explicit step. It runs the lazy automaton over an
alphabet and returns the resulting explicit automaton **and** a list mapping new
dense states back to the source states they came from:

```python
explicit, source_states = decomposition.materialize()
# optionally restrict the alphabet: materialize([(symbol_id, arity), ...])
```

A composed state remembers its provenance: `state.components()` returns the
parts of a product, determinized set, or paired span; `state.kind` names the
shape (`"explicit"`, `"span"`, `"product"`, `"set"`, …); `state.start` /
`state.end` expose span boundaries.

## Algebras

| Class | Input | Notes |
| --- | --- | --- |
| `StringAlgebra()` | whitespace-tokenized string | concatenation algebra |
| `TagStringAlgebra()` | string | TAG string algebra; input must be one contiguous string |
| `TagTreeAlgebra(sig, with_arities=False)` | term, e.g. `"S(a)"` | TAG derived trees |
| `BinarizingTagTreeAlgebra(sig, with_arities=False)` | term | binarized TAG trees (adds an append symbol) |
| `FeatureStructureAlgebra()` | feature-structure text | see below |

`decompose(text)` returns a lazy `Automaton`. `parse(text)` (string algebras)
returns the token list. `with_arities=True` distinguishes node labels by their
arity (`Tree_with_arities` style).

### Feature structures

```python
fs = ra.FeatureStructure.parse("[case: nom, num: sg]")
unified = fs.unify(other)        # FeatureStructure | None (None = clash)
sub     = fs.project("case")     # value at an attribute, or None
print(fs)                        # canonical text form
```

## IRTGs

Load a grammar from a file (`.irtg` or Tulipac `.tag`) or an in-memory string,
then parse one or more interpretation inputs.

```python
irtg = ra.Irtg.load("grammar.irtg")
# or: irtg = ra.Irtg.from_string(grammar_text)

best = irtg.best({"string": "john sleeps"})
if best:
    print(best.weight)           # derivation weight
    print(best.tree)             # derivation tree (grammar symbols)
    print(best.interpret())      # {interpretation_name: value}
```

`best(...)` returns the single highest-weight `Derivation` (or `None`).
`parse(...)` returns a full `ParseChart` you can inspect, enumerate, or re-rank.

```python
chart = irtg.parse({"string": "john sleeps"})
chart.automaton                  # the chart as an explicit Automaton
chart.stats                      # per-interpretation parse statistics
derivation = chart.best()        # best derivation in the chart
```

### Parse strategies

Both `parse` and `best` accept a `strategy=` string:

| Strategy | Meaning |
| --- | --- |
| `"top_down"` (default) | top-down condensed materialization; builds the full chart |
| `"indexed"` | indexed condensed materialization |
| `"astar"` | A\* one-best search; does not build the full chart |

See [Choosing a parsing algorithm](Parsing-Algorithms) for the trade-offs.

### Interpretations

```python
string = irtg.interpretation("string")
string.name, string.class_name, string.signature
decomp = string.decompose("john sleeps")     # the optimized decomposition automaton
value  = string.parse("john sleeps")         # an InterpretationValue
chart  = irtg.parse({"string": value})       # reuse a pre-parsed value
```

Passing an `InterpretationValue` (instead of a raw string) lets you parse the
input once and reuse it; it must be passed under the interpretation that
produced it.

### Derivations

```python
d = irtg.best({"string": "john sleeps"})
d.weight, d.score                # log-style weight and search score
d.tree                           # derivation Tree over grammar symbols
d.interpret()                    # {name: str | Tree | FeatureStructure}
d.encode("string", codec_name)   # render one interpretation via a named output codec
```

`interpret()` returns each interpretation's value in its natural Python form: a
string, a `Tree`, or a `FeatureStructure`.

## Cancellation

Parsing releases the GIL, so a long parse can be cancelled from another thread
with a `ParseControl`:

```python
control = ra.ParseControl()
# from another thread: control.cancel()
try:
    irtg.parse({"string": text}, control=control)
except ra.RustyAltoError:
    ...                          # raised with a "cancelled" message
```

## Threading

`Irtg`, `Automaton`, and the value types are immutable and safe to share across
threads. Heavy operations (`parse`, `best`, `viterbi`, `k_best`, `materialize`)
release the GIL while computing, so threads run in parallel.

```python
from concurrent.futures import ThreadPoolExecutor

irtg = ra.Irtg.from_string(grammar)
with ThreadPoolExecutor(max_workers=4) as pool:
    weights = list(pool.map(
        lambda _: irtg.best({"string": "john sleeps"}).weight,
        range(8),
    ))
```

The algebra classes (`StringAlgebra`, etc.) hold internal mutable state and are
*not* meant to be shared across threads; create one per thread.

## Loading a stored automaton

```python
automaton = ra.load_automaton("grammar.auto")
```

Reads an explicit automaton (`.auto`) through the standard codec registry.

## Errors

All binding exceptions derive from `RustyAltoError` (itself a `RuntimeError`):

| Exception | Raised when |
| --- | --- |
| `RustyAltoError` | a parse, decode, or build fails; also raised on cancellation |
| `UnsupportedOperationError` | a method needs a capability the automaton lacks |
| `StateOwnerError` | a `State` is used with an automaton that did not create it |

Invalid arguments (unknown symbols, malformed homomorphisms, out-of-range IDs)
raise `ValueError`.

## API summary

| Type | Purpose |
| --- | --- |
| `Signature` | interned symbol table (`from_symbols`, `id`, `name`, `arity`, `symbols`) |
| `Tree` | immutable term (`label`, `children`) |
| `State` | an automaton state with provenance (`kind`, `components`, `start`/`end`) |
| `WeightedTree` | a tree with `weight` and `score` |
| `Homomorphism` | term mapping between signatures (`from_terms`) |
| `Automaton` | explicit or lazy tree automaton |
| `AutomatonBuilder` | build an explicit weighted automaton |
| `StringAlgebra`, `TagStringAlgebra`, `TagTreeAlgebra`, `BinarizingTagTreeAlgebra` | algebra decompositions |
| `FeatureStructure`, `FeatureStructureAlgebra` | feature structures and their algebra |
| `Irtg`, `Interpretation`, `InterpretationValue` | grammars and their interpretations |
| `ParseChart`, `Derivation` | parse results |
| `ParseControl` | cooperative cancellation |
| `load_automaton` | read a stored `.auto` automaton |
