# Python bindings: internals and maintenance

This is the developer-facing companion to the user guide on the wiki
([Python-Bindings](https://github.com/coli-saar/rusty-alto/wiki/Python-Bindings)).
It describes how the `rusty_alto` package is assembled, the design of the
binding crate, and how to extend or release it.

## Layout

| Path | Role |
| --- | --- |
| `bindings/python/Cargo.toml` | the `rusty-alto-python` crate (`cdylib`, lib name `_rusty_alto`) |
| `bindings/python/src/lib.rs` | all PyO3 wrapper types and the `#[pymodule]` |
| `bindings/python/tests/` | `pytest` suite run against the built extension |
| `pyproject.toml` (repo root) | maturin build config; `python-source = "python"` |
| `python/rusty_alto/__init__.py` | re-exports from the compiled `_rusty_alto` |
| `python/rusty_alto/__init__.pyi` | hand-written type stub (the public API contract) |
| `python/rusty_alto/py.typed` | marks the package as typed |

The crate is a workspace member (see the root `Cargo.toml`). The compiled
extension is named `_rusty_alto` and lives inside the pure-Python `rusty_alto`
package, which re-exports it. maturin builds an `abi3` wheel
(`abi3-py39`), so one wheel covers CPython 3.9+.

## The single-`Automaton`-class design

The Rust library has many distinct automaton types (explicit, the per-algebra
decomposition automata, and the lazy combinators), each with its own state
type. Exposing one Python class per Rust type would be unusable. Instead the
binding erases them behind two enums in `lib.rs`:

- `AutomatonKind` — one variant per backing automaton (`Explicit`, `String`,
  `TagString`, `TagTree`, `BinarizedTagTree`, `Product`, `Determinized`,
  `Mapped`, `InverseHomomorphism`).
- `StateValue` — the matching per-kind state payloads (`Explicit(StateId)`,
  `Span`, `TagSpan`, `TagTree`, `BinarizedTagTree`, `Product`, `Determinized`).

`AutomatonData` holds an `AutomatonKind` plus an `owner` id; `PyAutomaton`
wraps it in an `Arc`. Every oracle operation (`step`, `is_accepting`,
`all_states`, `initial_states`, `rules_for_parent`, `rules_for_child`,
`condensed_rules`, `capabilities`) is a `match` over the kind that dispatches to
the corresponding core automaton and re-wraps results as `StateValue`s. Both
enums are `Clone + Eq + Hash` so states can be hashed and compared on the Python
side.

### State ownership

`owner` is a process-global `AtomicU64` counter (`next_owner`). Each
`PyAutomaton` gets a fresh id; each `PyState` records the id of the automaton
that produced it. `AutomatonData::check_state` rejects any state whose owner
differs, raising `StateOwnerError`. This is what stops callers from mixing dense
`StateId`s (or look-alike spans) from unrelated automata.

`AutomatonData::state_display` recursively renders a human-readable name for a
state, preferring stored state names (explicit automata, charts) and falling
back to the value's `Display`.

### Capabilities

`AutomatonData::capabilities()` returns a `Capabilities` struct computed
structurally — e.g. a `Product` is deterministic only if both sides are, and is
never condensed. The `PyAutomaton` getters (`is_deterministic`, etc.) read from
it. Methods that need a capability call the relevant `Option`-returning helper
and translate `None` into `UnsupportedOperationError`.

## Lazy combinators

`product`, `determinize`, `map_symbols`, and `inverse_homomorphism` build a new
`AutomatonKind` that references the operands via `Arc` — no work happens until
the automaton is queried. The actual semantics live in the `match` arms of
`AutomatonData::step` and friends:

- **Product** zips children pairwise and takes the cross product of results.
- **Determinized** does on-the-fly subset construction; results are sorted by
  display string for a deterministic state identity. It deliberately has no
  finite state universe or top-down view.
- **Mapped** rewrites symbols through a mapping (and reverses it for top-down).
- **InverseHomomorphism** evaluates the stored homomorphism term against child
  states (`evaluate_hom_term`), using a `cartesian` helper for the product of
  sub-results.

`materialize_dynamic` is the one eager driver: a worklist that interns reachable
states into an `ExplicitBuilder`, seeding from nullary symbols and expanding
over the supplied alphabet. It returns the `Explicit` automaton plus the ordered
`StateValue`s, which `materialize()` turns into the source-state mapping.

## GIL handling

Long-running, pure-Rust operations release the GIL via `py.detach(...)` so other
Python threads make progress: `Irtg::parse`/`best`, `Automaton::viterbi`,
`k_best`, and `materialize`. `ParseControl` wraps the core `ParseControl`; its
`cancel()` flips an atomic that the detached parse polls, surfacing as a
`RustyAltoError("...cancelled...")`. The thread-safety test in the suite relies
on this.

## Errors

Three exception types are created with `create_exception!` and registered in the
module:

```
RustyAltoError            (subclass of RuntimeError)
├── UnsupportedOperationError
└── StateOwnerError
```

`runtime_error` / `value_error` are the conversion helpers. Argument validation
(unknown symbols, bad homomorphisms, out-of-range IDs) uses `PyValueError`.

## Keeping the stub in sync

`python/rusty_alto/__init__.pyi` is written by hand and is the public API
contract enforced by type checkers. **It is not generated** — any change to the
`#[pymethods]` surface (new method, renamed parameter, changed signature,
default value, return type) must be mirrored there in the same change. The
`#[pyo3(signature = ...)]` defaults are the source of truth for the `= ...`
defaults in the stub.

## Adding a new automaton kind or algebra

To expose a new backing automaton:

1. Add a variant to `AutomatonKind` (and a `StateValue` variant if it has a new
   state type, plus its `Display` and an `*_states` extractor helper).
2. Extend every `match` in `AutomatonData`: `signature`, `state_display`,
   `step`, `is_accepting`, `all_states`, `initial_states`,
   `rules_for_parent`, `rules_for_child`, `condensed_rules`, and
   `capabilities`. The compiler's exhaustiveness checks will list most of these.
3. For a new algebra, add a `#[pyclass]` wrapper (mirroring `PyStringAlgebra`)
   whose `decompose` constructs the new kind, and register it in the
   `#[pymodule]`.
4. Update `__init__.pyi` and add coverage to `bindings/python/tests`.

## Build, test, release

```sh
maturin develop            # debug build into the active venv
maturin develop --release  # optimized; use for anything non-trivial
pytest bindings/python/tests
maturin build --release    # produce an abi3 wheel under target/wheels/
```

The crate version lives in `bindings/python/Cargo.toml`; the distribution
version and metadata live in the root `pyproject.toml`. Keep them in step with
the main crate version. The Rust crate's crates.io release process is documented
in [`publishing.md`](publishing.md); the Python wheel is not yet published.
