use crate::{
    BottomUpTa, DetBottomUpTa, Explicit, ExplicitBuilder, FxHashMap, IndexedBottomUpTa, Interner,
    StateId, Symbol, TopDownTa,
};
use smallvec::SmallVec;
use std::cell::{Ref, RefCell};
use std::hash::Hash;

type Results = SmallVec<[StateId; 2]>;

/// Runtime cache counters for [`Memo`].
///
/// Hit and miss counters are collected only when the `stats` feature is
/// enabled. Without that feature they are reported as zero, while `num_states`
/// is always available.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MemoStats {
    /// Number of transition queries answered from the cache.
    pub hits: u64,
    /// Number of transition queries forwarded to the inner automaton.
    pub misses: u64,
    /// Number of distinct inner states that have been assigned dense IDs.
    pub num_states: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum CacheKey {
    Nullary(Symbol),
    Unary(Symbol, StateId),
    Binary(Symbol, StateId, StateId),
    Higher(Symbol, Box<[StateId]>),
}

impl CacheKey {
    fn new(f: Symbol, children: &[StateId]) -> Self {
        match children.len() {
            0 => Self::Nullary(f),
            1 => Self::Unary(f, children[0]),
            2 => Self::Binary(f, children[0], children[1]),
            _ => Self::Higher(f, Box::from(children)),
        }
    }

    fn symbol(&self) -> Symbol {
        match self {
            Self::Nullary(f) | Self::Unary(f, _) | Self::Binary(f, _, _) | Self::Higher(f, _) => *f,
        }
    }

    fn children_vec(&self) -> Vec<StateId> {
        match self {
            Self::Nullary(_) => Vec::new(),
            Self::Unary(_, q) => vec![*q],
            Self::Binary(_, q0, q1) => vec![*q0, *q1],
            Self::Higher(_, children) => children.to_vec(),
        }
    }
}

/// Memoizing adapter from implicit automata to dense [`StateId`] states.
///
/// `Memo` lets an automaton with rich states act like an automaton over
/// [`StateId`]. On a cache miss, it resolves child IDs back to the inner state
/// type, asks the inner automaton for results, interns those results, and
/// caches the dense IDs. On a cache hit, it replays the stored IDs directly.
///
/// This type uses interior mutability and is intended for single-threaded
/// execution. To keep a snapshot of the discovered rules, call
/// [`Memo::into_explicit`].
pub struct Memo<A: BottomUpTa> {
    inner: A,
    interner: RefCell<Interner<A::State>>,
    cache: RefCell<FxHashMap<CacheKey, Results>>,
    accepting_cache: RefCell<FxHashMap<StateId, bool>>,
    #[cfg(feature = "stats")]
    hits: RefCell<u64>,
    #[cfg(feature = "stats")]
    misses: RefCell<u64>,
}

impl<A: BottomUpTa> Memo<A> {
    /// Wrap an automaton in an empty memoization cache.
    pub fn new(inner: A) -> Self {
        Self {
            inner,
            interner: RefCell::new(Interner::new()),
            cache: RefCell::new(FxHashMap::default()),
            accepting_cache: RefCell::new(FxHashMap::default()),
            #[cfg(feature = "stats")]
            hits: RefCell::new(0),
            #[cfg(feature = "stats")]
            misses: RefCell::new(0),
        }
    }

    /// Borrow the interner that maps inner states to dense IDs.
    ///
    /// This is useful for inspection. Prefer [`Memo::resolve`] when you only
    /// need to map one ID back to an inner state.
    pub fn interner(&self) -> Ref<'_, Interner<A::State>> {
        self.interner.borrow()
    }

    /// Resolve a dense ID back to the wrapped automaton's state type.
    ///
    /// Panics if the ID has not been discovered by this memoizer, or if it is
    /// [`StateId::STUCK`].
    pub fn resolve(&self, id: StateId) -> A::State {
        self.interner.borrow().resolve(id).clone()
    }

    /// Return current memoization statistics.
    pub fn stats(&self) -> MemoStats {
        MemoStats {
            #[cfg(feature = "stats")]
            hits: *self.hits.borrow(),
            #[cfg(not(feature = "stats"))]
            hits: 0,
            #[cfg(feature = "stats")]
            misses: *self.misses.borrow(),
            #[cfg(not(feature = "stats"))]
            misses: 0,
            num_states: self.interner.borrow().len() as u32,
        }
    }

    /// Freeze all queried transitions into an [`Explicit`] automaton.
    ///
    /// The result contains only the fragment that has actually been queried.
    /// If a transition was never requested, it will not appear in the explicit
    /// automaton. The returned [`Interner`] lets callers map the dense states
    /// back to the original inner state values.
    pub fn into_explicit(self) -> (Explicit, Interner<A::State>) {
        let num_states = self.interner.borrow().len();
        let mut accepting = Vec::new();
        for idx in 0..num_states {
            let q = StateId(idx as u32);
            if self.is_accepting(&q) {
                accepting.push(q);
            }
        }

        let interner = self.interner.into_inner();
        let cache = self.cache.into_inner();
        let mut builder = ExplicitBuilder::new();
        for _ in 0..num_states {
            builder.new_state();
        }
        for q in accepting {
            builder.add_accepting(q);
        }
        for (key, results) in cache {
            let symbol = key.symbol();
            let children = key.children_vec();
            for result in results {
                builder.add_rule(symbol, children.clone(), result);
            }
        }
        (builder.build(), interner)
    }

    fn resolve_children(&self, children: &[StateId]) -> SmallVec<[A::State; 4]> {
        let interner = self.interner.borrow();
        children
            .iter()
            .map(|&q| interner.resolve(q).clone())
            .collect()
    }

    fn intern_results(&self, results: Vec<A::State>) -> Results {
        let mut interner = self.interner.borrow_mut();
        let mut dense = Results::new();
        for q in results {
            let id = interner.intern(q);
            if !dense.contains(&id) {
                dense.push(id);
            }
        }
        dense
    }

    fn record_hit(&self) {
        #[cfg(feature = "stats")]
        {
            *self.hits.borrow_mut() += 1;
        }
    }

    fn record_miss(&self) {
        #[cfg(feature = "stats")]
        {
            *self.misses.borrow_mut() += 1;
        }
    }
}

impl<A: BottomUpTa> BottomUpTa for Memo<A> {
    type State = StateId;

    fn step(&self, f: Symbol, children: &[StateId], out: &mut dyn FnMut(StateId)) {
        let key = CacheKey::new(f, children);
        {
            let cache = self.cache.borrow();
            if let Some(results) = cache.get(&key) {
                self.record_hit();
                for &q in results {
                    out(q);
                }
                return;
            }
        }

        self.record_miss();
        let resolved = self.resolve_children(children);
        let mut raw = Vec::new();
        self.inner.step(f, &resolved, &mut |q| raw.push(q));
        let dense = self.intern_results(raw);
        self.cache.borrow_mut().insert(key.clone(), dense);
        let cache = self.cache.borrow();
        if let Some(results) = cache.get(&key) {
            for &q in results {
                out(q);
            }
        }
    }

    fn is_accepting(&self, q: &StateId) -> bool {
        if q.is_stuck() {
            return false;
        }
        if let Some(&accepting) = self.accepting_cache.borrow().get(q) {
            return accepting;
        }
        let state = self.interner.borrow().resolve(*q).clone();
        let accepting = self.inner.is_accepting(&state);
        self.accepting_cache.borrow_mut().insert(*q, accepting);
        accepting
    }
}

impl<A: DetBottomUpTa> DetBottomUpTa for Memo<A> {
    fn step_det(&self, f: Symbol, children: &[StateId]) -> Option<StateId> {
        let key = CacheKey::new(f, children);
        {
            let cache = self.cache.borrow();
            if let Some(results) = cache.get(&key) {
                self.record_hit();
                return (results.len() == 1).then_some(results[0]);
            }
        }

        self.record_miss();
        let resolved = self.resolve_children(children);
        let mut dense = Results::new();
        if let Some(q) = self.inner.step_det(f, &resolved) {
            let id = self.interner.borrow_mut().intern(q);
            dense.push(id);
        }
        let answer = (dense.len() == 1).then_some(dense[0]);
        self.cache.borrow_mut().insert(key, dense);
        answer
    }
}

impl<A: IndexedBottomUpTa> IndexedBottomUpTa for Memo<A> {
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &StateId,
        out: &mut dyn FnMut(&[StateId], StateId),
    ) {
        if state_at_position.is_stuck() {
            return;
        }

        let inner_state = self.interner.borrow().resolve(*state_at_position).clone();
        let mut raw = Vec::new();
        self.inner
            .step_partial(f, position, &inner_state, &mut |children, result| {
                raw.push((children.to_vec(), result));
            });

        for (children, result) in raw {
            let mut interner = self.interner.borrow_mut();
            let dense_children: SmallVec<[StateId; 4]> = children
                .into_iter()
                .map(|child| interner.intern(child))
                .collect();
            let dense_result = interner.intern(result);
            drop(interner);
            out(&dense_children, dense_result);
        }
    }
}

impl<A: TopDownTa> TopDownTa for Memo<A> {
    fn step_topdown(&self, parent: &StateId, out: &mut dyn FnMut(Symbol, &[StateId])) {
        if parent.is_stuck() {
            return;
        }

        let inner_parent = self.interner.borrow().resolve(*parent).clone();
        let mut raw = Vec::new();
        self.inner
            .step_topdown(&inner_parent, &mut |symbol, children| {
                raw.push((symbol, children.to_vec()));
            });

        for (symbol, children) in raw {
            let mut interner = self.interner.borrow_mut();
            let dense_children: SmallVec<[StateId; 4]> = children
                .into_iter()
                .map(|child| interner.intern(child))
                .collect();
            drop(interner);
            out(symbol, &dense_children);
        }
    }

    fn initial_states(&self, out: &mut dyn FnMut(StateId)) {
        let mut raw = Vec::new();
        self.inner.initial_states(&mut |q| raw.push(q));
        let mut interner = self.interner.borrow_mut();
        for q in raw {
            out(interner.intern(q));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct Leaf;

    impl BottomUpTa for Leaf {
        type State = &'static str;

        fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
            if f == Symbol(0) && children.is_empty() {
                out("leaf");
            }
            if f == Symbol(1) && children == ["leaf", "leaf"] {
                out("root");
            }
        }

        fn is_accepting(&self, q: &Self::State) -> bool {
            *q == "root"
        }
    }

    impl IndexedBottomUpTa for Leaf {
        fn step_partial(
            &self,
            f: Symbol,
            position: usize,
            state_at_position: &&'static str,
            out: &mut dyn FnMut(&[&'static str], &'static str),
        ) {
            if f == Symbol(1) && position < 2 && *state_at_position == "leaf" {
                out(&["leaf", "leaf"], "root");
            }
        }
    }

    impl TopDownTa for Leaf {
        fn step_topdown(
            &self,
            parent: &&'static str,
            out: &mut dyn FnMut(Symbol, &[&'static str]),
        ) {
            match *parent {
                "leaf" => out(Symbol(0), &[]),
                "root" => out(Symbol(1), &["leaf", "leaf"]),
                _ => {}
            }
        }

        fn initial_states(&self, out: &mut dyn FnMut(&'static str)) {
            out("root");
        }
    }

    #[test]
    fn memo_answers_like_inner() {
        let memo = Memo::new(Leaf);
        let mut leaves = Vec::new();
        memo.step(Symbol(0), &[], &mut |q| leaves.push(q));
        let mut roots = Vec::new();
        memo.step(Symbol(1), &[leaves[0], leaves[0]], &mut |q| roots.push(q));
        assert_eq!(memo.resolve(roots[0]), "root");
        assert!(memo.is_accepting(&roots[0]));
    }

    #[test]
    fn into_explicit_preserves_discovered_fragment() {
        let memo = Memo::new(Leaf);
        let mut leaves = Vec::new();
        memo.step(Symbol(0), &[], &mut |q| leaves.push(q));
        let mut roots = Vec::new();
        memo.step(Symbol(1), &[leaves[0], leaves[0]], &mut |q| roots.push(q));
        let (explicit, interner) = memo.into_explicit();
        assert_eq!(interner.resolve(roots[0]), &"root");
        assert_eq!(
            explicit.step_det(Symbol(1), &[leaves[0], leaves[0]]),
            Some(roots[0])
        );
        assert!(explicit.is_accepting(&roots[0]));
    }

    #[test]
    fn indexed_partial_forwards_through_memo() {
        let memo = Memo::new(Leaf);
        let mut leaves = Vec::new();
        memo.step(Symbol(0), &[], &mut |q| leaves.push(q));

        let mut found = Vec::new();
        memo.step_partial(Symbol(1), 0, &leaves[0], &mut |children, result| {
            found.push((children.to_vec(), result));
        });

        assert_eq!(found.len(), 1);
        assert_eq!(found[0].0, vec![leaves[0], leaves[0]]);
        assert_eq!(memo.resolve(found[0].1), "root");
    }

    #[test]
    fn topdown_forwards_through_memo() {
        let memo = Memo::new(Leaf);
        let mut initials = Vec::new();
        memo.initial_states(&mut |q| initials.push(q));

        let mut rules = Vec::new();
        memo.step_topdown(&initials[0], &mut |symbol, children| {
            rules.push((symbol, children.to_vec()));
        });

        assert_eq!(memo.resolve(initials[0]), "root");
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].0, Symbol(1));
        assert_eq!(rules[0].1.len(), 2);
    }
}
