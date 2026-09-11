//! Adaptive sparse storage for runtime data keyed by dense state IDs.

use crate::{FxHashMap, StateId};
use std::ops::Index;

const PAGE_SIZE: usize = 64;
const PAGING_THRESHOLD: usize = 4_096;
const EMPTY_SLOT: u8 = u8::MAX;

/// A sparse state map that keeps direct hash entries while small and switches
/// to compact pages once hash-bucket payload size would dominate cache use.
#[derive(Clone, Debug)]
pub(crate) struct StateStreamTable<V> {
    storage: Storage<V>,
}

#[derive(Clone, Debug)]
enum Storage<V> {
    Direct(FxHashMap<StateId, V>),
    Paged(FxHashMap<usize, StreamPage<V>>),
}

impl<V> Default for StateStreamTable<V> {
    fn default() -> Self {
        Self {
            storage: Storage::Direct(FxHashMap::default()),
        }
    }
}

#[derive(Clone, Debug)]
struct StreamPage<V> {
    slots: [u8; PAGE_SIZE],
    values: Vec<V>,
}

impl<V> StreamPage<V> {
    fn new() -> Self {
        Self {
            slots: [EMPTY_SLOT; PAGE_SIZE],
            values: Vec::new(),
        }
    }

    fn insert(&mut self, slot: usize, value: V) {
        debug_assert_eq!(self.slots[slot], EMPTY_SLOT);
        self.slots[slot] = self.values.len() as u8;
        self.values.push(value);
    }

    fn get(&self, slot: usize) -> Option<&V> {
        let index = self.slots[slot];
        (index != EMPTY_SLOT).then(|| &self.values[index as usize])
    }

    fn get_mut(&mut self, slot: usize) -> Option<&mut V> {
        let index = self.slots[slot];
        (index != EMPTY_SLOT).then(|| &mut self.values[index as usize])
    }
}

impl<V> StateStreamTable<V> {
    #[inline]
    pub(crate) fn contains_key(&self, state: &StateId) -> bool {
        self.get(state).is_some()
    }

    #[inline]
    pub(crate) fn insert(&mut self, state: StateId, value: V) {
        if matches!(&self.storage, Storage::Direct(map) if map.len() == PAGING_THRESHOLD) {
            self.promote();
        }
        match &mut self.storage {
            Storage::Direct(map) => {
                debug_assert!(!map.contains_key(&state));
                map.insert(state, value);
            }
            Storage::Paged(pages) => {
                let (page, slot) = page_slot(state);
                pages
                    .entry(page)
                    .or_insert_with(StreamPage::new)
                    .insert(slot, value);
            }
        }
    }

    #[inline]
    pub(crate) fn get(&self, state: &StateId) -> Option<&V> {
        match &self.storage {
            Storage::Direct(map) => map.get(state),
            Storage::Paged(pages) => {
                let (page, slot) = page_slot(*state);
                pages.get(&page)?.get(slot)
            }
        }
    }

    #[inline]
    pub(crate) fn get_mut(&mut self, state: &StateId) -> Option<&mut V> {
        match &mut self.storage {
            Storage::Direct(map) => map.get_mut(state),
            Storage::Paged(pages) => {
                let (page, slot) = page_slot(*state);
                pages.get_mut(&page)?.get_mut(slot)
            }
        }
    }

    fn promote(&mut self) {
        let Storage::Direct(direct) = &mut self.storage else {
            return;
        };
        let mut pages = FxHashMap::default();
        for (state, value) in direct.drain() {
            let (page, slot) = page_slot(state);
            pages
                .entry(page)
                .or_insert_with(StreamPage::new)
                .insert(slot, value);
        }
        self.storage = Storage::Paged(pages);
    }
}

impl<V> Index<&StateId> for StateStreamTable<V> {
    type Output = V;

    #[inline]
    fn index(&self, state: &StateId) -> &Self::Output {
        self.get(state).expect("state stream must exist")
    }
}

#[inline]
fn page_slot(state: StateId) -> (usize, usize) {
    let index = state.index();
    (index / PAGE_SIZE, index % PAGE_SIZE)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retains_sparse_values_across_promotion() {
        let mut table = StateStreamTable::default();
        for index in 0..=PAGING_THRESHOLD {
            let state = StateId((index * 67) as u32);
            table.insert(state, index);
        }
        assert!(matches!(table.storage, Storage::Paged(_)));
        for index in 0..=PAGING_THRESHOLD {
            let state = StateId((index * 67) as u32);
            assert_eq!(table[&state], index);
        }
    }
}
