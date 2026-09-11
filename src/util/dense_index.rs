//! Compact indexes from dense integer keys to variable-length value slices.

/// A compressed-sparse-row index for keys in `0..key_count`.
///
/// Construction makes two linear passes over a cloneable pair iterator. Values
/// for each key retain their input order. Lookup is constant time and the index
/// uses two contiguous allocations regardless of the number of non-empty keys.
#[derive(Clone, Debug)]
pub(crate) struct DenseIndex<V> {
    offsets: Box<[usize]>,
    values: Box<[V]>,
}

impl<V: Copy + Default> DenseIndex<V> {
    pub(crate) fn from_pairs<I>(key_count: usize, pairs: I) -> Self
    where
        I: Iterator<Item = (usize, V)> + Clone,
    {
        let mut offsets = vec![0usize; key_count + 1];
        for (key, _) in pairs.clone() {
            assert!(key < key_count, "dense-index key out of bounds");
            offsets[key + 1] += 1;
        }
        for key in 0..key_count {
            offsets[key + 1] += offsets[key];
        }

        let mut write_offsets = offsets[..key_count].to_vec();
        let mut values = vec![V::default(); offsets[key_count]];
        for (key, value) in pairs {
            let slot = &mut write_offsets[key];
            values[*slot] = value;
            *slot += 1;
        }

        Self {
            offsets: offsets.into_boxed_slice(),
            values: values.into_boxed_slice(),
        }
    }

    #[inline]
    pub(crate) fn values(&self, key: usize) -> &[V] {
        &self.values[self.offsets[key]..self.offsets[key + 1]]
    }

    #[inline]
    pub(crate) fn get(&self, key: usize) -> Option<&[V]> {
        (key + 1 < self.offsets.len()).then(|| self.values(key))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn groups_values_stably_and_keeps_empty_keys() {
        let pairs = [(2, 7u32), (0, 3), (2, 8), (3, 9)];
        let index = DenseIndex::from_pairs(5, pairs.into_iter());
        assert_eq!(index.values(0), &[3]);
        assert_eq!(index.values(1), &[]);
        assert_eq!(index.values(2), &[7, 8]);
        assert_eq!(index.values(3), &[9]);
        assert_eq!(index.values(4), &[]);
    }
}
