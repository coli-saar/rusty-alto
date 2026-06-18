use super::RightStateInterner;
use crate::{
    CondensedTa, FxHashMap, KeySet, StateId,
    materialize::{IndexedCondensedIntersectionStats, OwnedCondensedRule},
};
use fixedbitset::FixedBitSet;
use std::hash::Hash;

#[derive(Default)]
pub(super) struct GenericCandidateSource;

#[derive(Default)]
pub(super) struct ChildStateRightRuleIndex {
    cache: FxHashMap<(usize, StateId), Vec<usize>>,
}

impl ChildStateRightRuleIndex {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn rule_ids_for_trigger_into<R, I>(
        &mut self,
        right: &R,
        right_interner: &mut I,
        right_rules: &mut Vec<OwnedCondensedRule<StateId>>,
        stats: &mut IndexedCondensedIntersectionStats,
        position: usize,
        right_state: StateId,
        out: &mut Vec<usize>,
    ) where
        R: CondensedTa,
        R::State: Clone + Eq + Hash,
        I: RightStateInterner<R::State>,
    {
        out.clear();
        let cache_key = (position, right_state);
        if !self.cache.contains_key(&cache_key) {
            stats.right_indexed_queries += 1;
            let raw_state = right_interner.resolve(right_state).clone();
            let mut collected = Vec::new();
            right.condensed_rules_by_child(
                position,
                &raw_state,
                &mut |children, symbols, result| {
                    let rule_id = right_rules.len();
                    right_rules.push(OwnedCondensedRule {
                        children: children
                            .iter()
                            .cloned()
                            .map(|child| right_interner.intern(child))
                            .collect(),
                        symbols: symbols.clone(),
                        result: right_interner.intern(result),
                    });
                    collected.push(rule_id);
                },
            );
            self.cache.insert(cache_key, collected);
        }
        out.extend_from_slice(
            self.cache
                .get(&cache_key)
                .expect("cache entry was just inserted"),
        );
    }
}

#[derive(Default)]
pub(super) struct PartnerSet {
    states: Vec<StateId>,
    bits: FixedBitSet,
    products_by_left: Vec<Option<StateId>>,
}

impl PartnerSet {
    pub(super) fn insert(&mut self, state: StateId, product: StateId) -> bool {
        if self.bits.len() <= state.index() {
            self.bits.grow(state.index() + 1);
        }
        if self.products_by_left.len() <= state.index() {
            self.products_by_left.resize(state.index() + 1, None);
        }
        if self.bits.contains(state.index()) {
            return false;
        }
        self.bits.set(state.index(), true);
        self.products_by_left[state.index()] = Some(product);
        self.states.push(state);
        true
    }

    pub(super) fn len(&self) -> usize {
        self.states.len()
    }

    pub(super) fn product_for(&self, state: StateId) -> Option<StateId> {
        self.products_by_left.get(state.index()).and_then(|&p| p)
    }
}

impl KeySet<StateId> for PartnerSet {
    fn len(&self) -> usize {
        self.states.len()
    }

    fn contains(&self, key: &StateId) -> bool {
        key.index() < self.bits.len() && self.bits.contains(key.index())
    }

    fn for_each(&self, out: &mut dyn FnMut(&StateId)) {
        for state in &self.states {
            out(state);
        }
    }
}
