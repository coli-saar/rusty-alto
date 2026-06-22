# Python bindings

The `rusty_alto` Python package exposes the same oracle-style distinction as
the Rust API: an automaton may be an explicit weighted rule table or a lazy
native transition computation.

```python
import rusty_alto as ra

decomposition = ra.StringAlgebra().decompose("john sleeps")
assert decomposition.is_condensed

leaf = decomposition.step("john", [])
chart, source_states = decomposition.materialize()
```

States are owned by their automaton. Passing a state to another automaton raises
`StateOwnerError`, preventing accidental mixing of dense IDs or implicit state
domains.

Built-in products, determinization, symbol mappings, and inverse
homomorphisms remain lazy. `materialize()` is explicit and returns both the
resulting explicit automaton and its mapping back to source states.

## IRTGs

```python
grammar = ra.Irtg.load("grammar.irtg")
best = grammar.best({"string": "john sleeps"})
if best:
    print(best.weight)
    print(best.tree)
    print(best.interpret())
```

`Interpretation.decompose(text)` exposes the optimized decomposition automaton
used by that interpretation. Complete charts are represented by the same
`Automaton` class and retain state-provenance components.

## Building

Create a virtual environment and run:

```sh
pip install maturin pytest
maturin develop
pytest bindings/python/tests
```

Release wheels use CPython's stable ABI for Python 3.9 and newer.
