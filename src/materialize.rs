use crate::{
    Arity, BottomUpTa, CondensedTa, Explicit, ExplicitBuilder, Interner, Memo, StateId, Symbol,
    SymbolSet, run::cartesian_product,
};
use fixedbitset::FixedBitSet;
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::hash::Hash;

type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;

/// Explore a finite automaton and return an equivalent explicit fragment.
///
/// `materialize` starts from all nullary symbols in `alphabet`, repeatedly
/// queries transitions over already discovered states, and freezes every
/// queried rule into an [`Explicit`] automaton. The returned [`Interner`] maps
/// the explicit [`StateId`] values back to the original state type.
///
/// The caller must provide a finite alphabet as `(symbol, arity)` pairs. The
/// construction terminates when the reachable state space is finite. If the
/// implicit automaton can keep producing fresh states forever, this function
/// will also keep exploring.
///
/// Arity 0, 1, and 2 are handled directly. Higher arities are supported but can
/// be expensive because the number of state tuples grows exponentially.
pub fn materialize<A: BottomUpTa>(
    a: &A,
    alphabet: &[(Symbol, Arity)],
) -> (Explicit, Interner<A::State>) {
    let memo = Memo::new(a);
    let mut known = Vec::<StateId>::new();
    let mut known_bits = FixedBitSet::new();
    let mut worklist = Vec::<StateId>::new();

    for &(symbol, arity) in alphabet {
        if arity == 0 {
            collect_step(
                &memo,
                symbol,
                &[],
                &mut known,
                &mut known_bits,
                &mut worklist,
            );
        }
    }

    while let Some(popped) = worklist.pop() {
        let snapshot = known.clone();
        for &(symbol, arity) in alphabet {
            match arity {
                0 => {}
                1 => collect_step(
                    &memo,
                    symbol,
                    &[popped],
                    &mut known,
                    &mut known_bits,
                    &mut worklist,
                ),
                2 => {
                    for &other in &snapshot {
                        collect_step(
                            &memo,
                            symbol,
                            &[popped, other],
                            &mut known,
                            &mut known_bits,
                            &mut worklist,
                        );
                        if other != popped {
                            collect_step(
                                &memo,
                                symbol,
                                &[other, popped],
                                &mut known,
                                &mut known_bits,
                                &mut worklist,
                            );
                        }
                    }
                }
                n => {
                    let pools = vec![snapshot.as_slice(); n as usize];
                    cartesian_product(&pools, |tuple| {
                        if tuple.contains(&popped) {
                            collect_step(
                                &memo,
                                symbol,
                                tuple,
                                &mut known,
                                &mut known_bits,
                                &mut worklist,
                            );
                        }
                    });
                }
            }
        }
    }

    memo.into_explicit()
}

fn collect_step<A: BottomUpTa>(
    memo: &Memo<&A>,
    symbol: Symbol,
    children: &[StateId],
    known: &mut Vec<StateId>,
    known_bits: &mut FixedBitSet,
    worklist: &mut Vec<StateId>,
) {
    memo.step(symbol, children, &mut |q| {
        if !known_bits.contains(q.index()) {
            known_bits.grow(q.index() + 1);
            known_bits.set(q.index(), true);
            known.push(q);
            worklist.push(q);
        }
    });
}

/// Counters collected by [`materialize_indexed_condensed_intersection`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct IndexedCondensedIntersectionStats {
    /// Number of product states in the materialized intersection.
    pub output_states: usize,
    /// Number of product rules in the materialized intersection.
    pub output_rules: usize,
    /// Number of right-side condensed nullary rule shapes visited.
    pub right_nullary_rules: usize,
    /// Number of right-side indexed condensed queries issued.
    pub right_indexed_queries: usize,
}

impl IndexedCondensedIntersectionStats {
    /// Total number of right-side nullary shapes plus indexed queries.
    pub fn right_queries(&self) -> usize {
        self.right_nullary_rules + self.right_indexed_queries
    }
}

#[derive(Clone)]
struct OwnedRule {
    symbol: Symbol,
    children: SmallVec<[StateId; 2]>,
    result: StateId,
}

#[derive(Clone)]
struct OwnedCondensedRule<S> {
    children: SmallVec<[S; 2]>,
    symbols: SymbolSet,
    result: S,
}

#[derive(Default)]
struct LeftIndex {
    nullary_by_symbol: FxHashMap<Symbol, Vec<usize>>,
    by_state: FxHashMap<StateId, Vec<(Symbol, usize, usize)>>,
}

impl LeftIndex {
    fn build(rules: &[OwnedRule]) -> Self {
        let mut index = Self::default();
        for (rule_idx, rule) in rules.iter().enumerate() {
            if rule.children.is_empty() {
                index
                    .nullary_by_symbol
                    .entry(rule.symbol)
                    .or_default()
                    .push(rule_idx);
            }
            for (position, &child) in rule.children.iter().enumerate() {
                index
                    .by_state
                    .entry(child)
                    .or_default()
                    .push((rule.symbol, position, rule_idx));
            }
        }
        index
    }
}

/// Materialize the intersection of an explicit grammar automaton with a
/// condensed right automaton using indexed condensed right-side queries.
///
/// The right automaton is not eagerly enumerated. Nullary rules are driven from
/// right condensed nullary shapes, and non-nullary rules are queried by
/// `(child_position, right_child_state)` as product states become reachable.
/// The returned interner maps the right component of product states back to
/// right automaton states; output state IDs are dense product-state IDs.
pub fn materialize_indexed_condensed_intersection<R>(
    left: &Explicit,
    right: &R,
) -> (
    Explicit,
    Interner<R::State>,
    IndexedCondensedIntersectionStats,
)
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let left_rules: Vec<_> = left
        .rules()
        .map(|rule| OwnedRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
        })
        .collect();
    let left_index = LeftIndex::build(&left_rules);

    let mut right_interner = Interner::new();
    let mut product_ids = FxHashMap::<(StateId, StateId), StateId>::default();
    let mut product_pairs = Vec::<(StateId, StateId)>::new();
    let mut queue = VecDeque::<(StateId, StateId)>::new();
    let mut builder = ExplicitBuilder::new();
    let mut right_by_child_cache =
        FxHashMap::<(usize, StateId), Vec<OwnedCondensedRule<StateId>>>::default();
    let mut stats = IndexedCondensedIntersectionStats::default();

    right.condensed_nullary_rules(&mut |symbols, right_result| {
        stats.right_nullary_rules += 1;
        let right_result = right_interner.intern(right_result);
        for symbol in symbols.iter() {
            let Some(left_rule_indexes) = left_index.nullary_by_symbol.get(&symbol) else {
                continue;
            };
            for &left_rule_idx in left_rule_indexes {
                let left_rule = &left_rules[left_rule_idx];
                let (parent, is_new) = intern_product(
                    left_rule.result,
                    right_result,
                    left,
                    right,
                    &mut product_ids,
                    &mut product_pairs,
                    &right_interner,
                    &mut builder,
                );
                if is_new {
                    queue.push_back((left_rule.result, right_result));
                }
                builder.add_rule(symbol, Vec::new(), parent);
            }
        }
    });

    while let Some((left_state, right_state)) = queue.pop_front() {
        let Some(left_occurrences) = left_index.by_state.get(&left_state) else {
            continue;
        };

        for &(symbol, position, left_rule_idx) in left_occurrences {
            let left_rule = &left_rules[left_rule_idx];
            let cache_key = (position, right_state);
            let right_rules = right_by_child_cache.entry(cache_key).or_insert_with(|| {
                stats.right_indexed_queries += 1;
                let raw_state = right_interner.resolve(right_state).clone();
                let mut collected = Vec::new();
                right.condensed_rules_by_child(
                    position,
                    &raw_state,
                    &mut |children, symbols, result| {
                        collected.push(OwnedCondensedRule {
                            children: children
                                .iter()
                                .cloned()
                                .map(|child| right_interner.intern(child))
                                .collect(),
                            symbols: symbols.clone(),
                            result: right_interner.intern(result),
                        });
                    },
                );
                collected
            });

            for right_rule in right_rules {
                if !right_rule.symbols.contains(symbol)
                    || right_rule.children.len() != left_rule.children.len()
                {
                    continue;
                }

                let mut children = Vec::with_capacity(left_rule.children.len());
                let mut ok = true;
                for (&left_child, &right_child) in
                    left_rule.children.iter().zip(&right_rule.children)
                {
                    if let Some(&child) = product_ids.get(&(left_child, right_child)) {
                        children.push(child);
                    } else {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }

                let (parent, is_new) = intern_product(
                    left_rule.result,
                    right_rule.result,
                    left,
                    right,
                    &mut product_ids,
                    &mut product_pairs,
                    &right_interner,
                    &mut builder,
                );
                if is_new {
                    queue.push_back((left_rule.result, right_rule.result));
                }
                builder.add_rule(symbol, children, parent);
            }
        }
    }

    stats.output_states = product_pairs.len();
    let explicit = builder.build();
    stats.output_rules = explicit.rules().count();
    (explicit, right_interner, stats)
}

#[allow(clippy::too_many_arguments)]
fn intern_product<R>(
    left_state: StateId,
    right_state: StateId,
    left: &Explicit,
    right: &R,
    ids: &mut FxHashMap<(StateId, StateId), StateId>,
    pairs: &mut Vec<(StateId, StateId)>,
    right_interner: &Interner<R::State>,
    builder: &mut ExplicitBuilder,
) -> (StateId, bool)
where
    R: CondensedTa,
{
    if let Some(&id) = ids.get(&(left_state, right_state)) {
        return (id, false);
    }
    let id = builder.new_state();
    ids.insert((left_state, right_state), id);
    pairs.push((left_state, right_state));
    if left.is_accepting(&left_state) && right.is_accepting(right_interner.resolve(right_state)) {
        builder.add_accepting(id);
    }
    (id, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BottomUpTa, ExplicitBuilder};

    #[test]
    fn materializes_explicit_identity_fragment() {
        let a = Symbol(0);
        let f = Symbol(1);
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let root = b.new_state();
        b.add_rule(a, vec![], leaf);
        b.add_rule(f, vec![leaf, leaf], root);
        b.add_accepting(root);
        let explicit = b.build();

        let (mat, _interner) = materialize(&explicit, &[(a, 0), (f, 2)]);
        let mut leaves = Vec::new();
        mat.step(a, &[], &mut |q| leaves.push(q));
        let mut roots = Vec::new();
        mat.step(f, &[leaves[0], leaves[0]], &mut |q| roots.push(q));
        assert_eq!(roots.len(), 1);
        assert!(mat.is_accepting(&roots[0]));
    }
}
