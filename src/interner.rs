//! Stable interning from hashable values to dense [`StateId`]s.

use crate::{FxHashMap, StateId};
use std::hash::Hash;

/// Bidirectional map between user states and dense [`StateId`]s.
///
/// An interner is useful when an implicit automaton naturally uses rich states
/// but an algorithm wants compact integer IDs. Inserting the same value twice
/// returns the same ID, and IDs remain stable for the lifetime of the interner.
#[derive(Clone, Debug)]
pub struct Interner<T: Clone + Eq + Hash> {
    forward: FxHashMap<T, StateId>,
    backward: Vec<T>,
}

impl<T: Clone + Eq + Hash> Default for Interner<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Eq + Hash> Interner<T> {
    /// Create an empty interner.
    pub fn new() -> Self {
        Self {
            forward: FxHashMap::default(),
            backward: Vec::new(),
        }
    }

    /// Return the number of distinct values that have been interned.
    pub fn len(&self) -> usize {
        self.backward.len()
    }

    /// Return whether no values have been interned yet.
    pub fn is_empty(&self) -> bool {
        self.backward.is_empty()
    }

    /// Return the existing ID for `t`, or insert a fresh ID.
    ///
    /// Fresh IDs are assigned densely in insertion order: `StateId(0)`,
    /// `StateId(1)`, and so on. [`StateId::STUCK`] is never assigned.
    pub fn intern(&mut self, t: T) -> StateId {
        if let Some(&id) = self.forward.get(&t) {
            return id;
        }
        let raw = u32::try_from(self.backward.len()).expect("too many states for StateId");
        assert_ne!(raw, StateId::STUCK.0, "cannot allocate StateId::STUCK");
        let id = StateId(raw);
        self.backward.push(t.clone());
        self.forward.insert(t, id);
        id
    }

    /// Look up a value without inserting it.
    pub fn get(&self, t: &T) -> Option<StateId> {
        self.forward.get(t).copied()
    }

    /// Resolve an ID to its interned value.
    ///
    /// Panics if `id` is [`StateId::STUCK`] or out of range.
    pub fn resolve(&self, id: StateId) -> &T {
        assert!(!id.is_stuck(), "cannot resolve StateId::STUCK");
        self.backward
            .get(id.index())
            .expect("state id not present in interner")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_stably() {
        let mut interner = Interner::new();
        let a = interner.intern("a");
        let b = interner.intern("b");
        assert_eq!(a, interner.intern("a"));
        assert_ne!(a, b);
        assert_eq!(interner.resolve(a), &"a");
        assert_eq!(interner.get(&"b"), Some(b));
    }
}
