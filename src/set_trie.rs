use crate::FxHashMap;
use std::hash::{BuildHasher, Hash};

/// Trie from key sequences to values with efficient set-constrained traversal.
///
/// The main query is: given one set of allowed keys per depth, visit all values
/// whose key tuple chooses an allowed key at every depth. At each trie node the
/// traversal iterates over whichever side is smaller: the allowed set at this
/// depth or the actually present outgoing trie edges.
#[derive(Clone, Debug)]
pub struct SetTrie<K, V> {
    next: FxHashMap<K, SetTrie<K, V>>,
    value: Option<V>,
}

impl<K, V> Default for SetTrie<K, V> {
    fn default() -> Self {
        Self {
            next: FxHashMap::default(),
            value: None,
        }
    }
}

impl<K, V> SetTrie<K, V>
where
    K: Clone + Eq + Hash,
{
    /// Create an empty trie.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the value for `key`, inserting one from `make` if absent.
    pub fn get_or_insert_with(&mut self, key: &[K], make: impl FnOnce() -> V) -> &mut V {
        let mut node = self;
        for part in key {
            node = node.next.entry(part.clone()).or_default();
        }
        node.value.get_or_insert_with(make)
    }

    /// Return the value for `key`, if present.
    pub fn get(&self, key: &[K]) -> Option<&V> {
        let mut node = self;
        for part in key {
            node = node.next.get(part)?;
        }
        node.value.as_ref()
    }

    /// Visit every value whose key tuple is accepted by `key_sets`.
    ///
    /// `key_sets[d]` is the set of allowed keys at depth `d`. Values stored at
    /// shorter or longer key lengths are not visited.
    pub fn for_each_value_for_key_sets<S>(&self, key_sets: &[S], mut out: impl FnMut(&V))
    where
        S: KeySet<K>,
    {
        self.for_each_value_for_key_sets_at(0, key_sets, &mut out);
    }

    fn for_each_value_for_key_sets_at<S>(
        &self,
        depth: usize,
        key_sets: &[S],
        out: &mut dyn FnMut(&V),
    ) where
        S: KeySet<K>,
    {
        if depth == key_sets.len() {
            if let Some(value) = &self.value {
                out(value);
            }
            return;
        }

        let keys = &key_sets[depth];
        if keys.len() < self.next.len() {
            keys.for_each(&mut |key| {
                if let Some(next) = self.next.get(key) {
                    next.for_each_value_for_key_sets_at(depth + 1, key_sets, out);
                }
            });
        } else {
            for (key, next) in &self.next {
                if keys.contains(key) {
                    next.for_each_value_for_key_sets_at(depth + 1, key_sets, out);
                }
            }
        }
    }
}

/// A set-like collection that can drive [`SetTrie`] traversal.
pub trait KeySet<K> {
    /// Number of keys in the set.
    fn len(&self) -> usize;

    /// Return whether the set contains `key`.
    fn contains(&self, key: &K) -> bool;

    /// Visit every key in the set.
    fn for_each(&self, out: &mut dyn FnMut(&K));
}

impl<K, S> KeySet<K> for hashbrown::HashSet<K, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.len()
    }

    fn contains(&self, key: &K) -> bool {
        self.contains(key)
    }

    fn for_each(&self, out: &mut dyn FnMut(&K)) {
        for key in self {
            out(key);
        }
    }
}

impl<K, T> KeySet<K> for &T
where
    T: KeySet<K> + ?Sized,
{
    fn len(&self) -> usize {
        (**self).len()
    }

    fn contains(&self, key: &K) -> bool {
        (**self).contains(key)
    }

    fn for_each(&self, out: &mut dyn FnMut(&K)) {
        (**self).for_each(out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FxHashSet;

    #[test]
    fn visits_values_matching_key_sets() {
        let mut trie = SetTrie::new();
        trie.get_or_insert_with(&[1, 2], Vec::new).push("a");
        trie.get_or_insert_with(&[1, 3], Vec::new).push("b");
        trie.get_or_insert_with(&[4, 2], Vec::new).push("c");

        let first = FxHashSet::from_iter([1]);
        let second = FxHashSet::from_iter([2, 3]);
        let mut values = Vec::new();
        trie.for_each_value_for_key_sets(&[&first, &second], |found| {
            values.extend(found.iter().copied());
        });
        values.sort_unstable();

        assert_eq!(values, vec!["a", "b"]);
    }
}
