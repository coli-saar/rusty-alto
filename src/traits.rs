use crate::Symbol;
use smallvec::SmallVec;
use std::hash::Hash;

/// A bottom-up tree automaton queried as an oracle.
///
/// Implement this trait when you want the library to run or combine your
/// automaton. The method [`BottomUpTa::step`] receives a node symbol and the
/// states already assigned to the node's children. It reports every possible
/// state for the parent by calling the callback.
///
/// Implementations may be explicit table lookups, like [`crate::Explicit`], or
/// implicit computations, such as a type checker or derivative construction.
/// `step` should behave like a pure function: the same symbol and child states
/// should produce the same parent states, without duplicates.
pub trait BottomUpTa {
    /// State type carried by the automaton.
    ///
    /// Rich implicit automata can use application-level states here. Wrap them
    /// in [`crate::Memo`] when a dense [`crate::StateId`] representation is
    /// needed.
    type State: Clone + Eq + Hash;

    /// Report all possible parent states for `f(children...)`.
    ///
    /// Call `out(q)` once for each valid result state `q`. If no rule applies,
    /// do not call `out`. The order is not specified, but duplicate states
    /// should not be emitted.
    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State));

    /// Return whether `q` is an accepting state.
    ///
    /// A tree is accepted when the root receives at least one accepting state.
    fn is_accepting(&self, q: &Self::State) -> bool;
}

impl<A: BottomUpTa + ?Sized> BottomUpTa for &A {
    type State = A::State;

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        (**self).step(f, children, out);
    }

    fn is_accepting(&self, q: &Self::State) -> bool {
        (**self).is_accepting(q)
    }
}

/// Faster interface for deterministic bottom-up automata.
///
/// Deterministic automata have at most one parent state for each symbol and
/// child-state tuple. Implementing this trait lets [`crate::run_det`] avoid
/// allocating state sets and avoid callback overhead.
pub trait DetBottomUpTa: BottomUpTa {
    /// Return the unique result state, or `None` if no transition exists.
    ///
    /// This method must agree with [`BottomUpTa::step`]: if it returns
    /// `Some(q)`, then `step` should emit exactly `q`; if it returns `None`,
    /// then `step` should emit no states.
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State>;

    /// Group key for symbols that share a transition function.
    ///
    /// Any two symbols returning the same `det_group` value must yield the same
    /// [`step_det`](DetBottomUpTa::step_det) result for every child tuple. The
    /// default puts each symbol in its own group (`f.0`), i.e. no sharing.
    /// Condensed automata override this so a caller can compute one transition
    /// per group and reuse it for every symbol in the group (e.g. `InvHom`, whose
    /// transition depends only on the image term shared by a whole symbol set).
    fn det_group(&self, f: Symbol) -> u32 {
        f.0
    }
}

impl<A: DetBottomUpTa + ?Sized> DetBottomUpTa for &A {
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        (**self).step_det(f, children)
    }

    fn det_group(&self, f: Symbol) -> u32 {
        (**self).det_group(f)
    }
}

/// Finite enumeration of an automaton's state space.
///
/// Most oracle-style automata only need to answer local transition queries.
/// Some complete algorithms, such as condensed inverse homomorphism for a bare
/// variable image, also need to enumerate every possible inner state. Keep this
/// as a separate refinement so infinite or very large implicit automata can
/// still implement [`BottomUpTa`] without promising finite enumeration.
pub trait StateUniverse: BottomUpTa {
    /// Report every state in the finite universe exactly once.
    fn all_states(&self, out: &mut dyn FnMut(Self::State));
}

impl<A: StateUniverse + ?Sized> StateUniverse for &A {
    fn all_states(&self, out: &mut dyn FnMut(Self::State)) {
        (**self).all_states(out);
    }
}

/// Indexed bottom-up rule enumeration for sibling-finder-style joins.
///
/// [`BottomUpTa::step`] answers a complete transition query. This refinement
/// answers a partial query: given a symbol, child position, and state at that
/// position, enumerate the full rules that match. Product and parsing
/// algorithms can use this to join compatible rules without enumerating child
/// tuples that never occur in either component.
pub trait IndexedBottomUpTa: BottomUpTa {
    /// Report every rule `f(children...) -> q` where `children[position]`
    /// equals `state_at_position`.
    ///
    /// `children` is borrowed from the implementation and is valid only for
    /// the callback. Implementations must not emit duplicate rules.
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &Self::State,
        out: &mut dyn FnMut(&[Self::State], Self::State),
    );
}

impl<A: IndexedBottomUpTa + ?Sized> IndexedBottomUpTa for &A {
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &Self::State,
        out: &mut dyn FnMut(&[Self::State], Self::State),
    ) {
        (**self).step_partial(f, position, state_at_position, out);
    }
}

/// Optional top-down view of a bottom-up automaton.
///
/// Not every automaton can enumerate rules by parent state. Implement this
/// refinement when algorithms need to ask: given a parent state, which symbols
/// and child-state tuples can produce it?
pub trait TopDownTa: BottomUpTa {
    /// Report every rule `f(children...) -> parent`.
    ///
    /// `children` is borrowed from the implementation and is valid only for
    /// the callback.
    fn step_topdown(&self, parent: &Self::State, out: &mut dyn FnMut(Symbol, &[Self::State]));

    /// Report the initial states of the top-down view.
    ///
    /// For bottom-up automata these are exactly the accepting states.
    fn initial_states(&self, out: &mut dyn FnMut(Self::State));
}

impl<A: TopDownTa + ?Sized> TopDownTa for &A {
    fn step_topdown(&self, parent: &Self::State, out: &mut dyn FnMut(Symbol, &[Self::State])) {
        (**self).step_topdown(parent, out);
    }

    fn initial_states(&self, out: &mut dyn FnMut(Self::State)) {
        (**self).initial_states(out);
    }
}

/// Compact sorted set of symbols, used by [`CondensedTa`] to group rules.
///
/// Internally a sorted, deduplicated inline vector. Lookup is O(log n) via
/// binary search. Most label sets are tiny (1–4 symbols).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SymbolSet(SmallVec<[Symbol; 4]>);

impl SymbolSet {
    /// Create an empty set.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a symbol, maintaining sorted and deduplicated order.
    #[inline]
    pub fn insert(&mut self, s: Symbol) {
        match self.0.binary_search(&s) {
            Ok(_) => {}
            Err(idx) => self.0.insert(idx, s),
        }
    }

    /// Return whether the set contains `s`.
    #[inline]
    pub fn contains(&self, s: Symbol) -> bool {
        self.0.binary_search(&s).is_ok()
    }

    /// Iterate over symbols in sorted order.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.0.iter().copied()
    }

    /// Return the number of symbols.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Return whether the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Remove all symbols from the set.
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl FromIterator<Symbol> for SymbolSet {
    fn from_iter<I: IntoIterator<Item = Symbol>>(iter: I) -> Self {
        let mut set = Self::new();
        for s in iter {
            set.insert(s);
        }
        set
    }
}

/// Refinement of [`BottomUpTa`] that enumerates rules grouped by transition shape.
///
/// For each distinct `(children, result)` pair that occurs in any rule, the
/// automaton collects all symbols `f` such that `f(children) -> result` into a
/// [`SymbolSet`] and emits them together.
///
/// The main use case is efficient materialization when multiple source symbols
/// share the same homomorphic image: rather than invoking the term evaluator
/// once per symbol, a single evaluation covers the entire label set.
pub trait CondensedTa: BottomUpTa {
    /// Enumerate every distinct `(children, result)` pair, reporting the set of
    /// symbols that have that shape.
    ///
    /// Each shape is emitted exactly once. `children` is borrowed from the
    /// implementation; the slice is only valid for the duration of the callback.
    #[allow(clippy::type_complexity)]
    fn condensed_rules(&self, out: &mut dyn FnMut(&[Self::State], &SymbolSet, Self::State));

    /// Enumerate condensed nullary rules.
    ///
    /// The default implementation filters [`CondensedTa::condensed_rules`].
    /// Implementations on hot paths should override this when nullary rules can
    /// be produced or indexed more cheaply than the full condensed relation.
    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, Self::State)) {
        self.condensed_rules(&mut |children, symbols, result| {
            if children.is_empty() {
                out(symbols, result);
            }
        });
    }

    /// Enumerate condensed rules whose child at `position` is `state`.
    ///
    /// The default implementation filters [`CondensedTa::condensed_rules`].
    /// Implementations on hot paths should override this to avoid materializing
    /// or scanning unrelated condensed rules.
    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &Self::State,
        out: &mut dyn FnMut(&[Self::State], &SymbolSet, Self::State),
    ) {
        self.condensed_rules(&mut |children, symbols, result| {
            if children.get(position) == Some(state) {
                out(children, symbols, result);
            }
        });
    }
}

/// Optional parent-indexed view of a condensed automaton.
///
/// This is the condensed analogue of [`TopDownTa`]: given a parent state,
/// enumerate all outgoing rule shapes, grouping all compatible symbols in a
/// [`SymbolSet`]. Implementations should stream results and avoid materializing
/// the whole condensed relation.
pub trait CondensedTopDownTa: BottomUpTa {
    /// Report every condensed rule `symbols(children...) -> parent`.
    ///
    /// `children` and `symbols` are borrowed from the implementation and are
    /// valid only for the duration of the callback.
    fn condensed_rules_by_parent(
        &self,
        parent: &Self::State,
        out: &mut dyn FnMut(&SymbolSet, &[Self::State]),
    );

    /// Report initial states of the top-down view.
    fn condensed_initial_states(&self, out: &mut dyn FnMut(Self::State));
}

impl<A: CondensedTopDownTa + ?Sized> CondensedTopDownTa for &A {
    fn condensed_rules_by_parent(
        &self,
        parent: &Self::State,
        out: &mut dyn FnMut(&SymbolSet, &[Self::State]),
    ) {
        (**self).condensed_rules_by_parent(parent, out);
    }

    fn condensed_initial_states(&self, out: &mut dyn FnMut(Self::State)) {
        (**self).condensed_initial_states(out);
    }
}
