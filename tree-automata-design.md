# Tree Automata Library — Implementation Design

This document specifies a Rust tree-automata library that runs over a pre-existing arena-tree representation. It is meant to be a complete implementation brief: the architecture, public API signatures, internal data structures, invariants, and a phased build order are all here.

## 1. Background and central insight

A *tree automaton* assigns states to nodes of a tree bottom-up according to transition rules. The two common implementation styles are:

- **Explicit** automata that intern every rule into a table.
- **Implicit** automata that compute rules on demand (a regex derivative, a type system, a decomposition of an algebra value, etc.).

The design treats explicit automata as **a fully materialized cache of an implicit one**. The primary abstraction is an oracle trait that answers transition queries; the explicit type is a data structure that happens to implement it; and a memoizing adapter is the bridge that lets the two compose.

Two practical complications shape the trait surface:

1. Some algorithms (parse-chart construction, Viterbi, EM) consume an automaton by **enumerating its rules**, not by querying it on demand. Naive lazy composition produces correct results but bad asymptotics — see the Alto/sibling-finder literature (Groschwitz et al., ACL 2016). The fix is opt-in refinement traits (`IndexedBottomUpTa`, `CondensedTa`) that expose indexed enumeration, with blanket-slow fallbacks for components that don't implement them.

2. Top-down queries are useful but not universally supportable. Top-down is a separate opt-in trait, not part of the base.

## 2. Crate setup

**Crate name:** `rusty-alto` (workspace-internal).

**Dependencies** (use these exact crates; pin to the latest stable as of implementation):

- `rustc-hash` — `FxHashMap`, `FxHashSet` as the default hasher. SipHash is too slow for the integer-keyed inner loops.
- `hashbrown` — direct access for `raw_entry_mut`, used to look up rules with borrowed keys without allocation. We re-export `HashMap` from `hashbrown` rather than using `std::collections::HashMap`.
- `smallvec` — `SmallVec<[T; N]>` for child-state buffers and rule results.
- `fixedbitset` — for `Explicit`'s accepting set and for bitset state sets when `|Q|` is moderate.
- `thiserror` — for error enums.

**Tree dependencies**

We are using `packed-term-arena` to manage trees. Include a dependency to this package, it is installed locally for now.
The source code is in `~/Documents/workspace/packed-term-arena`.

**No `serde`** in the initial implementation. We can add it later behind a feature flag.

**MSRV:** Rust 1.75 (we use return-position `impl Trait` in traits sparingly, mostly callback-style).

**Module layout:**

```
src/
  lib.rs              // re-exports
  ids.rs              // StateId, Symbol, Arity
  interner.rs         // Interner<T>
  traits.rs           // BottomUpTa, DetBottomUpTa, refinement traits
  explicit.rs         // Explicit
  memo.rs             // Memo<A>
  combinators/
    mod.rs
    product.rs        // Product<A, B>
    determinized.rs   // Determinized<A>
    mapped.rs         // Mapped<A, F>
  run.rs              // run_det, run_nondet, side-table types
  arena.rs            // Arena trait (assumptions on the host tree)
  materialize.rs      // materialize<A>(...)
```

## 3. Foundational types

### 3.1 StateId

```rust
/// Dense integer state identifier.
///
/// `StateId::STUCK` is reserved as a sentinel meaning "no state assigned
/// / this subtree is rejected by the automaton". This lets the deterministic
/// run avoid `Option<StateId>` in its side table.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StateId(pub u32);

impl StateId {
    pub const STUCK: StateId = StateId(u32::MAX);
    pub fn index(self) -> usize { self.0 as usize }
    pub fn is_stuck(self) -> bool { self == Self::STUCK }
}
```

User code should never construct a `StateId` directly except through the `Interner`. We don't make the field private because internal modules need it, but we document that external users go through interners.

### 3.2 Symbol and Arity

```rust
/// A terminal-symbol identifier in some signature.
///
/// Symbols are externally managed (the host system owns the signature). The
/// library does not intern symbols; it accepts whatever u32 the caller gives.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(pub u32);

/// Number of children a symbol takes.
pub type Arity = u8;
```

### 3.3 Interner

```rust
/// Bidirectional map between a value type `T` and dense `StateId`s.
/// Used by `Memo` to turn implicit-automaton states into dense IDs, and by
/// `Explicit::materialize` to relate dense IDs back to the original states.
pub struct Interner<T: Clone + Eq + Hash> {
    forward: hashbrown::HashMap<T, StateId, fxhash::FxBuildHasher>,
    backward: Vec<T>,
}

impl<T: Clone + Eq + Hash> Interner<T> {
    pub fn new() -> Self;
    pub fn len(&self) -> usize;

    /// Returns the existing StateId for `t`, or inserts and returns a fresh one.
    pub fn intern(&mut self, t: T) -> StateId;

    /// Look up without inserting.
    pub fn get(&self, t: &T) -> Option<StateId>;

    /// Reverse lookup. Panics on STUCK or on unknown IDs.
    pub fn resolve(&self, id: StateId) -> &T;
}
```

`fxhash::FxBuildHasher` is what `rustc-hash` exposes. (Crate is named `rustc-hash`, build-hasher is in scope as `FxBuildHasher`.)

## 4. Core traits

### 4.1 BottomUpTa — the oracle

```rust
/// A bottom-up tree automaton, queried as an oracle.
///
/// Implementors answer: given a symbol and the states already assigned to a
/// node's children, which states can this node take? Implementors must NOT
/// cache anything internally beyond what's needed for correctness; caching is
/// `Memo`'s job. A correct implementation is a pure function modulo any
/// shared structure passed in by reference (a signature, an interner, a
/// borrowed grammar).
///
/// Object-safe (the `out` callback keeps it so).
pub trait BottomUpTa {
    type State: Clone + Eq + Hash;

    /// Invoke `out` once for every state q such that
    /// `f(children[0], ..., children[n-1]) -> q` is a transition rule.
    /// May call `out` zero or more times. Order is unspecified; duplicates
    /// must not be produced.
    fn step(
        &self,
        f: Symbol,
        children: &[Self::State],
        out: &mut dyn FnMut(Self::State),
    );

    fn is_accepting(&self, q: &Self::State) -> bool;
}
```

**Implementor contract:**

- `step` is pure modulo its `&self` borrow.
- Duplicates in `out` callbacks are forbidden. If an implementation might produce them naturally, it must dedupe before calling `out`.
- The `out` callback may store states; implementors must move (or clone) states into it, not pass references to internal storage that gets reused.

### 4.2 DetBottomUpTa — the deterministic fast path

```rust
/// A deterministic bottom-up automaton: at most one resulting state per
/// (symbol, child-states) tuple. This is where almost all the performance
/// lives, since each node carries a single state rather than a set.
pub trait DetBottomUpTa: BottomUpTa {
    /// Returns `Some(q)` if there is a unique transition rule
    /// `f(children) -> q`, `None` otherwise.
    fn step_det(
        &self,
        f: Symbol,
        children: &[Self::State],
    ) -> Option<Self::State>;
}
```

Implementors of `DetBottomUpTa` must also implement `BottomUpTa` such that `step` calls `out` exactly once with `q` whenever `step_det` returns `Some(q)`, and not at all when `step_det` returns `None`. A blanket method on `DetBottomUpTa` cannot be used to derive `step`, because we want the deterministic path to skip the callback overhead.

### 4.3 IndexedBottomUpTa — indexed enumeration for the join-style product

```rust
/// Refinement of BottomUpTa that supports indexed bottom-up lookup.
///
/// Given one child state at a particular position, enumerate the rules
/// `f(...) -> q` for which that position holds that state, streaming the
/// remaining child states. This is what makes the join-style product
/// asymptotically optimal (cf. Groschwitz et al. 2016 "sibling-finder").
pub trait IndexedBottomUpTa: BottomUpTa {
    /// For every rule `f(c[0], ..., c[n-1]) -> q` in which `c[i] == q_i`,
    /// invoke `out(c, q)` exactly once. `c` is a borrowed slice; the
    /// callback may copy from it but must not retain the borrow.
    fn step_partial(
        &self,
        f: Symbol,
        i: usize,
        q_i: &Self::State,
        out: &mut dyn FnMut(&[Self::State], Self::State),
    );
}
```

There is **no blanket impl** from `BottomUpTa` to `IndexedBottomUpTa`, because the naive "enumerate all tuples and filter" implementation is exactly the bad asymptotic we're trying to avoid. Algorithms that want fast enumeration should bound their type parameters with `IndexedBottomUpTa` directly; consumers without that capability use slower fallbacks explicitly.

`Explicit` implements `IndexedBottomUpTa` via per-position indexes (see §5). `Memo` implements it iff its inner type does. `Product<A, B>` has two impls (see §8.1).

### 4.4 CondensedTa — sets of labels per rule

```rust
/// Refinement that exposes "condensed" rules: rules sharing the same parent
/// and child-state tuple are grouped by a label set, so the engine can
/// process O(|labels|) rules at once.
///
/// Useful when many grammar symbols share the same homomorphic image (the
/// common case in IRTG encodings of CFGs, where many rules `A -> B C` all
/// map to `concat(x1, x2)` in the string algebra).
pub trait CondensedTa: BottomUpTa {
    /// For every distinct child-state tuple `c` that appears in any rule of
    /// this automaton with parent state in a rule, invoke
    /// `out(c, labels, q)` where `labels` is the set of symbols `f` such
    /// that `f(c) -> q` is a rule. The grouping is "across symbols sharing
    /// the same shape", not across parents.
    fn condensed_rules(
        &self,
        out: &mut dyn FnMut(&[Self::State], &SymbolSet, Self::State),
    );
}

/// Compact representation of a set of symbols.
/// Implementation: a sorted `SmallVec<[Symbol; 4]>`, with `contains` via
/// binary search and equality via memcmp. We add a bitset variant later if
/// profile demands.
pub struct SymbolSet { ... }
```

Not implemented in phase 1. Specified here for completeness so the trait hierarchy is stable.

### 4.5 TopDownTa — opt-in top-down queries

```rust
/// Top-down view of an automaton. Optional; not all automata support it.
pub trait TopDownTa: BottomUpTa {
    /// Invoke `out(children, f)` once for every rule `f(children) -> q`.
    fn step_topdown(
        &self,
        q: &Self::State,
        out: &mut dyn FnMut(Symbol, &[Self::State]),
    );

    /// The set of states that any accepting derivation can start from
    /// (i.e. the initial states of the top-down view). For bottom-up
    /// automata this is the set of accepting states.
    fn initial_states(&self, out: &mut dyn FnMut(Self::State));
}
```

Algorithms that need top-down (some minimization variants, some emptiness checks) take `where A: TopDownTa`. There is no runtime "this automaton doesn't support top-down" error path.

## 5. Explicit

The explicit automaton stores all rules in arity-specialized tables. This is a performance decision: arity-≤2 rules cover the vast majority of practical workloads, and keying maps by `(Symbol, StateId)` or `(Symbol, StateId, StateId)` instead of `(Symbol, Box<[StateId]>)` eliminates per-lookup allocation and gives `Copy` keys that hash in a handful of instructions.

```rust
pub struct Explicit {
    num_states: u32,
    accepting: fixedbitset::FixedBitSet,

    /// Rules f -> q, indexed by Symbol.
    /// Most symbols have few nullary rules, but a SmallVec keeps storage tight.
    nullary: hashbrown::HashMap<Symbol, SmallVec<[StateId; 2]>, FxBuildHasher>,

    /// Rules f(q1) -> q, indexed by (Symbol, q1).
    unary: hashbrown::HashMap<(Symbol, StateId), SmallVec<[StateId; 2]>, FxBuildHasher>,

    /// Rules f(q1, q2) -> q, indexed by (Symbol, q1, q2).
    binary: hashbrown::HashMap<(Symbol, StateId, StateId), SmallVec<[StateId; 2]>, FxBuildHasher>,

    /// Fallback for arity >= 3. Key is (Symbol, child-state slice).
    higher: hashbrown::HashMap<HigherKey, SmallVec<[StateId; 2]>, FxBuildHasher>,

    /// Indexes for IndexedBottomUpTa. Built lazily on first call.
    indexes: std::cell::OnceCell<Indexes>,
}

/// Key for arity >= 3. Stored as boxed slice. Lookup uses raw_entry to
/// avoid allocating per query.
struct HigherKey(Symbol, Box<[StateId]>);

/// Per-(symbol, child-position, state) index: gives the rules and their
/// other child states.
struct Indexes {
    /// For arity-2: (Symbol, position, state) -> Vec<(other_child, result)>
    binary_idx: hashbrown::HashMap<(Symbol, u8, StateId), Vec<(StateId, StateId)>, FxBuildHasher>,
    /// For arity-n>=3: (Symbol, position, state) -> Vec<(full_children, result)>
    higher_idx: hashbrown::HashMap<(Symbol, u8, StateId), Vec<(Box<[StateId]>, StateId)>, FxBuildHasher>,
    /// For arity-1: (Symbol, state) -> Vec<result>  (same as `unary` actually,
    /// but kept here for uniformity)
    unary_idx: hashbrown::HashMap<(Symbol, StateId), Vec<StateId>, FxBuildHasher>,
}
```

### 5.1 Construction API

```rust
pub struct ExplicitBuilder {
    next_state: u32,
    accepting: Vec<StateId>,
    rules: Vec<(Symbol, Vec<StateId>, StateId)>,  // raw accumulator
}

impl ExplicitBuilder {
    pub fn new() -> Self;

    /// Allocate a fresh state. States are sequential u32 starting from 0.
    /// Do not allocate STUCK; the builder will reject it.
    pub fn new_state(&mut self) -> StateId;

    pub fn add_accepting(&mut self, q: StateId);

    /// Add a rule. `children` may be empty (nullary).
    /// Panics if any state is STUCK or out of range.
    pub fn add_rule(&mut self, f: Symbol, children: Vec<StateId>, q: StateId);

    pub fn build(self) -> Explicit;
}
```

`build` populates the arity-specialized maps from the raw accumulator. It does NOT build the indexes; those are built on first `IndexedBottomUpTa::step_partial` call via the `OnceCell`.

### 5.2 Trait impls

```rust
impl BottomUpTa for Explicit {
    type State = StateId;

    fn step(&self, f: Symbol, children: &[StateId], out: &mut dyn FnMut(StateId)) {
        match children.len() {
            0 => if let Some(rs) = self.nullary.get(&f) {
                for &q in rs { out(q); }
            },
            1 => if let Some(rs) = self.unary.get(&(f, children[0])) {
                for &q in rs { out(q); }
            },
            2 => if let Some(rs) = self.binary.get(&(f, children[0], children[1])) {
                for &q in rs { out(q); }
            },
            _ => {
                // Use raw_entry with a borrowed key to avoid allocation.
                // See implementation note 5.3.
                if let Some(rs) = self.lookup_higher(f, children) {
                    for &q in rs { out(q); }
                }
            }
        }
    }

    fn is_accepting(&self, q: &StateId) -> bool {
        !q.is_stuck() && self.accepting.contains(q.index())
    }
}

impl DetBottomUpTa for Explicit {
    fn step_det(&self, f: Symbol, children: &[StateId]) -> Option<StateId> {
        // Returns Some iff the matching map has exactly one entry.
        // If multiple, returns None (caller should use step instead).
    }
}

impl IndexedBottomUpTa for Explicit { ... }
impl TopDownTa for Explicit { ... }
```

### 5.3 Implementation note: borrowed-key lookup for higher-arity

`hashbrown::HashMap::raw_entry()` lets us look up `(Symbol, &[StateId])` against a stored `HigherKey(Symbol, Box<[StateId]>)` without allocating a temporary key. The trick:

```rust
fn lookup_higher(&self, f: Symbol, children: &[StateId]) -> Option<&SmallVec<[StateId; 2]>> {
    let mut hasher = self.higher.hasher().build_hasher();
    (f, children).hash(&mut hasher);
    let hash = hasher.finish();
    self.higher
        .raw_entry()
        .from_hash(hash, |k| k.0 == f && &*k.1 == children)
        .map(|(_, v)| v)
}
```

This requires that the `Hash` impl for `HigherKey` matches the `Hash` impl for `(Symbol, &[StateId])`. Verify with a unit test.

### 5.4 Other inherent methods on Explicit

Algorithms that fundamentally require enumerating the full rule set live as inherent methods on `Explicit`, **not** on the trait:

```rust
impl Explicit {
    /// Returns true iff L(self) is empty. Reachability from nullary rules.
    pub fn is_empty(&self) -> bool;

    /// Returns the set of states reachable from nullary rules via any
    /// number of rule applications.
    pub fn reachable_states(&self) -> fixedbitset::FixedBitSet;

    /// Minimize a deterministic automaton via Hopcroft-style partition
    /// refinement. Panics if self is not deterministic.
    pub fn minimize_det(&self) -> Explicit;

    /// Iterate over all rules. Order unspecified but stable across calls.
    pub fn rules(&self) -> impl Iterator<Item = Rule<'_>>;
}

pub struct Rule<'a> {
    pub symbol: Symbol,
    pub children: &'a [StateId],
    pub result: StateId,
}
```

Phase 1 implements `is_empty`, `reachable_states`, and `rules`. `minimize_det` is phase 3.

## 6. Memo<A>

```rust
/// Memoizing adapter: caches `step` results from an inner automaton and
/// exposes them as dense `StateId`s.
///
/// Single-threaded. `RefCell` interior mutability — `Memo` is `!Sync`.
/// To share across threads, freeze into `Explicit` via `into_explicit`.
pub struct Memo<A: BottomUpTa> {
    inner: A,
    interner: std::cell::RefCell<Interner<A::State>>,
    cache: std::cell::RefCell<
        hashbrown::HashMap<CacheKey, SmallVec<[StateId; 2]>, FxBuildHasher>,
    >,
    accepting_cache: std::cell::RefCell<hashbrown::HashMap<StateId, bool, FxBuildHasher>>,
}

/// Internal cache key. Uses arity splitting like Explicit for hot paths.
enum CacheKey {
    Nullary(Symbol),
    Unary(Symbol, StateId),
    Binary(Symbol, StateId, StateId),
    Higher(Symbol, Box<[StateId]>),
}

impl<A: BottomUpTa> Memo<A> {
    pub fn new(inner: A) -> Self;

    /// Read-only access to the interner.
    pub fn interner(&self) -> std::cell::Ref<'_, Interner<A::State>> {
        self.interner.borrow()
    }

    /// Resolve a dense ID back to the original state. Panics on STUCK or
    /// unknown IDs.
    pub fn resolve(&self, id: StateId) -> A::State {
        self.interner.borrow().resolve(id).clone()
    }

    /// Freeze the current cache into an Explicit. Only includes rules
    /// that have been queried (and whose results have been interned).
    /// Useful as a final step after warmup.
    ///
    /// Returns the Explicit along with the consumed interner (so the
    /// caller can keep mapping IDs back to A::State).
    pub fn into_explicit(self) -> (Explicit, Interner<A::State>);
}

impl<A: BottomUpTa> BottomUpTa for Memo<A> {
    type State = StateId;

    fn step(&self, f: Symbol, children: &[StateId], out: &mut dyn FnMut(StateId)) {
        // 1. Build the CacheKey from f and children.
        // 2. Check the cache; if hit, replay cached results to `out`.
        // 3. Miss: resolve each child StateId to A::State via the interner,
        //    call inner.step(f, &resolved_children, |q_a| { intern q_a, push }).
        // 4. Store the (CacheKey -> SmallVec<StateId>) entry.
        // 5. Replay results to `out`.
    }

    fn is_accepting(&self, q: &StateId) -> bool {
        // Cache (StateId -> bool). On miss, look up A::State via interner,
        // ask inner, cache, return.
    }
}

// Forward refinement traits when possible:
impl<A: BottomUpTa + IndexedBottomUpTa> IndexedBottomUpTa for Memo<A> { ... }
impl<A: DetBottomUpTa> DetBottomUpTa for Memo<A> { ... }
impl<A: TopDownTa> TopDownTa for Memo<A> { ... }
```

**Critical invariant:** The cache must be opaque to the inner automaton. The inner automaton MUST NOT receive `StateId`s in its `step` call — it receives `A::State` values, resolved via the interner. The dense IDs are an implementation detail of `Memo`; an implementor of `A` does not know `Memo` exists.

**Critical invariant:** Once a state has been interned and assigned a `StateId`, that mapping is permanent. `StateId`s are stable across calls.

## 7. Materialization

```rust
/// Compute the explicit automaton reachable from nullary rules over the
/// given alphabet. This is the saturation construction: seed with all
/// nullary rules, repeatedly apply `step` to every (symbol, tuple) of
/// known states, until no new states appear.
///
/// Bounded by the maximum arity considered. For practical signatures this
/// is the alphabet's max arity. We don't try to handle infinite-arity
/// signatures.
///
/// Returns the explicit automaton plus the interner that maps StateIds
/// back to the original A::State.
pub fn materialize<A: BottomUpTa>(
    a: &A,
    alphabet: &[(Symbol, Arity)],
) -> (Explicit, Interner<A::State>);
```

**Algorithm:**

1. Build a `Memo<&A>` (borrowing the input). Note: this requires `Memo` to work over `&A`, which means we need `impl<A: BottomUpTa> BottomUpTa for &A`.
2. Seed worklist with all nullary symbols. For each, call `memo.step(f, &[], collect)`; every new `StateId` returned goes into a "known states" `FixedBitSet`.
3. Worklist loop: pop a known state, for each symbol of each arity, for each tuple in `known^arity` containing the popped state in at least one position, call `memo.step(f, &tuple, collect)`. (Restricting to tuples containing the popped state avoids redundant work across iterations.)
4. Continue until the worklist is empty.
5. Call `memo.into_explicit()`.
6. Build the accepting set by calling `memo.is_accepting` on every known state.

**Complexity:** Exponential in arity in the worst case, but bounded by the number of *reachable* states, which is what the construction discovers. For finite-state automata over reasonable signatures this terminates quickly. For automata with infinite state spaces, this loops forever — caller's responsibility to ensure finiteness.

## 8. Combinators

### 8.1 Product<A, B>

Two impls: a slow generic one for any pair of `BottomUpTa`, and a fast indexed one for pairs that both implement `IndexedBottomUpTa`.

```rust
pub struct Product<A, B>(pub A, pub B);

impl<A: BottomUpTa, B: BottomUpTa> BottomUpTa for Product<A, B> {
    type State = (A::State, B::State);

    fn step(&self, f: Symbol, children: &[(A::State, B::State)],
            out: &mut dyn FnMut((A::State, B::State))) {
        // Project children into (Vec<A::State>, Vec<B::State>).
        // Collect A's step results, then nest B's, output cartesian product.
    }

    fn is_accepting(&self, (qa, qb): &(A::State, B::State)) -> bool {
        self.0.is_accepting(qa) && self.1.is_accepting(qb)
    }
}

impl<A, B> IndexedBottomUpTa for Product<A, B>
where
    A: IndexedBottomUpTa,
    B: IndexedBottomUpTa,
{
    fn step_partial(
        &self,
        f: Symbol,
        i: usize,
        q_i: &(A::State, B::State),
        out: &mut dyn FnMut(&[(A::State, B::State)], (A::State, B::State)),
    ) {
        // Call A.step_partial(f, i, &q_i.0, |a_children, qa| {
        //   for each a_children, call B.step_partial(f, i, &q_i.1, |b_children, qb| {
        //     iff a_children.len() == b_children.len() (same arity), zip and emit
        //   })
        // })
        // The double indexed call is the sibling-finder-style join: we never
        // enumerate child tuples that don't appear in *both* components.
    }
}
```

The fast impl does **not** materialize all combinations; it asks each side which rules are consistent with the given child position and joins those. This is the asymptotic improvement that makes intersection-based parsing practical.

### 8.2 Determinized<A>

```rust
/// Subset construction as a lazy automaton.
///
/// State = sorted set of A::State.  Cheaper variants (bitset states when
/// |A::Q| is small) live in `determinized_bitset.rs`; this one is the
/// generic fallback.
pub struct Determinized<A>(pub A);

impl<A: BottomUpTa> BottomUpTa for Determinized<A> {
    type State = std::collections::BTreeSet<A::State>
        where A::State: Ord;
    // BTreeSet implements Ord and Hash provided element does.

    fn step(&self, f: Symbol,
            children: &[Self::State],
            out: &mut dyn FnMut(Self::State)) {
        // For each tuple in cartesian product of children sets,
        // call inner.step, accumulate results into one BTreeSet.
        // Output that BTreeSet (if nonempty) exactly once.
    }

    fn is_accepting(&self, qs: &Self::State) -> bool {
        qs.iter().any(|q| self.0.is_accepting(q))
    }
}

impl<A: BottomUpTa> DetBottomUpTa for Determinized<A>
where A::State: Ord {
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        // Compute the same set as step, return Some iff nonempty.
    }
}
```

`A::State: Ord` is required for `BTreeSet`. Document this requirement; we don't try to relax it in phase 1.

### 8.3 Mapped<A, F>

```rust
/// Relabel an automaton's symbols. Useful for renaming/aliasing.
pub struct Mapped<A, F> {
    pub inner: A,
    pub map: F,  // F: Fn(Symbol) -> Symbol
}

// BottomUpTa, etc., forwarded with symbol translation.
```

Phase 2.

## 9. Arena interface

The library does not own the arena tree. It defines a trait that the host's arena must implement:

```rust
/// A node identifier in the host arena. Must be cheap to compare and copy.
pub trait NodeId: Copy + Eq + Hash {
    /// Dense usable-as-an-index integer. Used for side tables.
    /// Implementations should return values in [0, arena.len()).
    fn index(self) -> usize;
}

/// Trait that the host arena must implement.
pub trait Arena {
    type NodeId: NodeId;
    /// Iterator over children of a node. We require a slice-or-iterator;
    /// the run code allocates a SmallVec to materialize it once per node.
    type Children<'a>: Iterator<Item = Self::NodeId> + 'a where Self: 'a;
    type PostOrder<'a>: Iterator<Item = Self::NodeId> + 'a where Self: 'a;

    /// Total number of nodes. Side tables are sized to this.
    fn len(&self) -> usize;

    /// Symbol on a node. The host owns the signature.
    fn symbol(&self, n: Self::NodeId) -> Symbol;

    fn children(&self, n: Self::NodeId) -> Self::Children<'_>;

    /// Post-order traversal from a root. Children before parents.
    /// May visit shared nodes (in a DAG) multiple times; the run code
    /// guards against this by checking the side table.
    fn post_order(&self, root: Self::NodeId) -> Self::PostOrder<'_>;
}
```

If the host arena hash-conses (i.e. is a DAG), `post_order` should ideally visit each unique node only once; the run code handles either case but is faster when shared subtrees are visited once.

## 10. Running the automaton

### 10.1 Deterministic run

```rust
/// Run a deterministic automaton over an arena tree.
/// Returns the side table (one state per node) and the root's state.
///
/// Stuck propagation: a child with STUCK causes the parent to be STUCK.
/// `state_at[node.index()] == STUCK` means the subtree is rejected.
pub struct DetRun {
    pub states: Vec<StateId>,
    pub root_state: StateId,
}

pub fn run_det<A, T>(a: &A, arena: &T, root: T::NodeId) -> DetRun
where
    A: DetBottomUpTa<State = StateId>,
    T: Arena,
{
    let mut states = vec![StateId::STUCK; arena.len()];
    let mut buf: SmallVec<[StateId; 4]> = SmallVec::new();

    for node in arena.post_order(root) {
        // If we've already computed this node (DAG case), skip.
        if !states[node.index()].is_stuck() { continue; }

        buf.clear();
        let mut any_stuck = false;
        for c in arena.children(node) {
            let cs = states[c.index()];
            if cs.is_stuck() { any_stuck = true; break; }
            buf.push(cs);
        }
        if any_stuck {
            // STUCK already initialized; leave it.
            continue;
        }

        let result = a.step_det(arena.symbol(node), &buf)
            .unwrap_or(StateId::STUCK);
        states[node.index()] = result;
    }

    DetRun { root_state: states[root.index()], states }
}
```

For deterministic runs over a non-`StateId`-state automaton, callers should first wrap with `Memo`.

### 10.2 Nondeterministic run

```rust
/// Run a nondeterministic automaton over an arena tree.
/// Each node carries a set of states; the set is empty for stuck nodes.
pub struct NonDetRun<S> {
    pub states: Vec<StateSet<S>>,
    pub root_states: StateSet<S>,
}

/// Compact set-of-states representation. Phase 1: sorted SmallVec.
/// Phase 4: optional bitset variant for dense small state spaces.
pub struct StateSet<S>(SmallVec<[S; 4]>);

impl<S: Clone + Ord> StateSet<S> {
    pub fn new() -> Self;
    pub fn insert(&mut self, s: S);  // maintains sorted, deduped
    pub fn iter(&self) -> impl Iterator<Item = &S>;
    pub fn is_empty(&self) -> bool;
    pub fn len(&self) -> usize;
}

pub fn run_nondet<A, T>(a: &A, arena: &T, root: T::NodeId) -> NonDetRun<A::State>
where
    A: BottomUpTa,
    A::State: Ord,
    T: Arena,
{
    // For each node in post-order:
    //   - Gather children's StateSets.
    //   - If any is empty, leave this node's set empty.
    //   - Otherwise, for each tuple in cartesian product (use odometer in 10.3),
    //     call a.step and collect results into the local StateSet.
    //   - Store.
}
```

### 10.3 Cartesian product helper

```rust
/// Invoke `f` once for each element of the cartesian product of `pools`.
/// Empty `pools` yields a single call with an empty slice (the empty tuple).
/// Any empty pool yields zero calls.
///
/// Allocates one buffer for the tuple, reuses it across calls.
fn cartesian_product<T: Clone>(
    pools: &[&[T]],
    mut f: impl FnMut(&[T]),
);
```

Used internally by `run_nondet` and the slow `Product` impl. Tested in isolation.

## 11. Performance requirements

These are not optional; they materially affect the library's competitiveness.

1. **FxHash everywhere.** Every `HashMap` in the crate uses `FxBuildHasher`. Wrap `hashbrown::HashMap` with the alias `type FxHashMap<K, V> = hashbrown::HashMap<K, V, fxhash::FxBuildHasher>;` and use it consistently.

2. **No allocation in hot lookup paths.** `Explicit::step` for arity ≤ 2 must allocate zero bytes per call. For arity ≥ 3 it uses `raw_entry` (see §5.3) to look up a borrowed key.

3. **STUCK as sentinel.** `DetRun.states` is `Vec<StateId>`, not `Vec<Option<StateId>>`. The size difference matters on large trees.

4. **SmallVec for child buffers.** Inline up to 4 states. Most arena nodes have arity ≤ 4; spilling to heap is the slow path.

5. **DAG-friendly run.** The `if !states[node.index()].is_stuck() { continue; }` skip in `run_det` lets a hash-consed arena trivially memoize shared subtree evaluations.

6. **Lazy index construction in Explicit.** The `Indexes` field is `OnceCell`. Users who never call `step_partial` never pay the index-building cost.

7. **Memo cache metric exposure.** Add `Memo::stats() -> MemoStats { hits: u64, misses: u64, num_states: u32 }`. Don't track this in release mode by default — gate behind a `cfg(feature = "stats")` or check whether the compiler can constant-fold a no-op tracker.

## 12. Phased implementation order

**Phase 1: foundations.** Implement in this order; each phase has working tests before the next begins.

1. `ids.rs`: `StateId`, `Symbol`, `Arity`, `StateId::STUCK`.
2. `interner.rs`: `Interner<T>`.
3. `traits.rs`: `BottomUpTa`, `DetBottomUpTa` only. Skip refinement traits for now.
4. `explicit.rs`: `Explicit`, `ExplicitBuilder`. Implement `BottomUpTa` and `DetBottomUpTa`. Skip `IndexedBottomUpTa`. Implement `is_empty`, `reachable_states`, `rules`.
5. `memo.rs`: `Memo<A>` implementing `BottomUpTa` and `DetBottomUpTa`. Skip refinement-trait forwarding.
6. `arena.rs`: define `NodeId`, `Arena` traits. Implement a test arena (`TestArena`) that stores nodes as `Vec<(Symbol, Vec<NodeIdx>)>`.
7. `run.rs`: `run_det`, `run_nondet`, `cartesian_product`. Side-table types.
8. `combinators/product.rs`: slow `Product<A, B>: BottomUpTa` impl only.
9. `combinators/determinized.rs`: `Determinized<A>`.
10. `materialize.rs`: `materialize` function.

**Acceptance tests for phase 1:**

- Round-trip: build an `Explicit` with `ExplicitBuilder`, run it on a tree, verify accepting state.
- Determinism: deterministic `Explicit` answers `step_det` consistently with `step`.
- Materialize identity: `materialize(&e, alphabet)` of an explicit `e` produces an equivalent automaton (same language).
- Determinized correctness: `Determinized<NondetExplicit>` accepts exactly the same language as the input.
- Product correctness: language of `Product(a, b)` is the intersection of `L(a)` and `L(b)` on small hand-built examples.
- Memo behavior: `Memo<implicit>` answers the same queries as the underlying implicit automaton, and `into_explicit` produces a working automaton equivalent on its discovered fragment.

**Phase 2: refinement traits.**

11. `IndexedBottomUpTa` trait. Implement for `Explicit` (build `Indexes` lazily). Implement fast `Product` over `IndexedBottomUpTa`. Forward through `Memo` and `Determinized`.
12. `TopDownTa` trait. Implement for `Explicit` (precompute or use a top-down index). Forward through wrappers where possible.
13. `Mapped<A, F>` combinator.

**Phase 3: heavier algorithms.**

14. `minimize_det` on `Explicit` (Hopcroft).
15. `CondensedTa` trait and `Explicit` impl.
16. Bitset state-set variant for `Determinized` when `|Q| ≤ 64` (or arbitrary, via `FixedBitSet`).

**Phase 4: niceties.**

17. `serde` feature.
18. Optional concurrent `Memo` via `dashmap` (feature-gated).
19. Property-based tests (`proptest`) over random small automata and trees.

## 13. Testing strategy

- **Unit tests** per file. Each public function has at least one happy-path and one edge-case test.
- **Edge cases to cover explicitly:** empty alphabet, nullary-only automaton, automaton with no accepting states, single-node tree, DAG with shared leaves (must not double-count states), STUCK propagation through deep trees, `Memo` cache hit on second identical query, `materialize` on a finite implicit automaton, `Determinized` of an already-deterministic input (should be a no-op modulo state representation).
- **Property tests** (phase 4): generate small random automata via `proptest`, build with `ExplicitBuilder`, check that `run_det(Determinized(memo(a)))` accepts the same trees as a reference enumeration.
- **Benchmarks** (separate `benches/` directory, criterion): a synthetic CFG-like grammar over a string-shaped tree, measured at various sizes. Compare `step` throughput between `Explicit`, `Memo<Explicit>`, and a deeper composition.

## 14. Documentation requirements

Every public item gets a doc comment. The crate root (`lib.rs`) has a top-level explanation including:

- The oracle-trait insight (explicit = materialized implicit).
- Why refinement traits exist (asymptotic enumeration matters).
- When to use `Memo` vs `materialize` vs raw composition.
- The `StateId::STUCK` convention.
- A worked example: building an `Explicit` for "tree of `f(a, a)`" and running it.

Examples in `examples/` directory:

- `examples/simple.rs`: build a tiny explicit automaton by hand, run on a tree.
- `examples/implicit.rs`: define a custom implicit automaton (states are `Arc<str>`), wrap in `Memo`, run.
- `examples/intersection.rs`: intersect two automata using `Product`.

## 15. Out of scope (initial release)

- Weighted automata (`WeightedBottomUpTa`). Specified in conversation; not implemented in phase 1–3. The trait surface is designed to extend cleanly later.
- Epsilon transitions. Closure on `Explicit` only, deferred.
- Top-down deterministic minimization.
- Tree transducers (this is recognition only).
- IRTG-style algebras and homomorphisms. The library is the engine layer; an IRTG layer goes on top later.

---

End of design document.
