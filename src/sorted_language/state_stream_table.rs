//! Dense optional storage for runtime data keyed by state ID.

use crate::StateId;
use std::ops::Index;

#[derive(Clone, Debug)]
pub(crate) struct StateStreamTable<V> {
    values: Vec<Option<V>>,
}

impl<V> StateStreamTable<V> {
    pub(crate) fn new(state_count: usize) -> Self {
        let mut values = Vec::with_capacity(state_count);
        values.resize_with(state_count, || None);
        Self { values }
    }

    #[inline]
    pub(crate) fn contains_key(&self, state: &StateId) -> bool {
        self.values[state.index()].is_some()
    }

    #[inline]
    pub(crate) fn insert(&mut self, state: StateId, value: V) {
        let slot = &mut self.values[state.index()];
        debug_assert!(slot.is_none());
        *slot = Some(value);
    }

    #[inline]
    pub(crate) fn get_mut(&mut self, state: &StateId) -> Option<&mut V> {
        self.values[state.index()].as_mut()
    }
}

impl<V> Index<&StateId> for StateStreamTable<V> {
    type Output = V;

    #[inline]
    fn index(&self, state: &StateId) -> &Self::Output {
        self.values[state.index()]
            .as_ref()
            .expect("state stream must exist")
    }
}
