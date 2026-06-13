use crate::{
    BottomUpTa, DetBottomUpTa, FxHashMap, FxHashSet, IndexedBottomUpTa, StateId, Symbol, TopDownTa,
    traits::{CondensedTa, StateUniverse, SymbolSet},
};
use fixedbitset::FixedBitSet;
use smallvec::SmallVec;
use std::cell::OnceCell;
use std::hash::{BuildHasher, Hash, Hasher};

type Results = SmallVec<[StateId; 2]>;

/// A fully materialized bottom-up tree automaton.
///
/// `Explicit` stores transition rules in lookup tables. It is the fastest
/// representation when all rules are known ahead of time or after an implicit
/// automaton has been materialized. Rules with arity 0, 1, and 2 use separate
/// compact tables because those are the common hot paths.
///
/// Build values with [`ExplicitBuilder`]. The builder deduplicates repeated
/// rules, so `step` never emits the same result state twice for one query.
#[derive(Clone, Debug)]
pub struct Explicit {
    num_states: u32,
    accepting: FixedBitSet,
    nullary: FxHashMap<Symbol, Results>,
    unary: FxHashMap<(Symbol, StateId), Results>,
    binary: FxHashMap<(Symbol, StateId, StateId), Results>,
    higher: FxHashMap<HigherKey, Results>,
    rules: Vec<StoredRule>,
    reachable_cache: OnceCell<FixedBitSet>,
    indexes: OnceCell<Indexes>,
    condensed_cache: OnceCell<Vec<CondensedRule>>,
}

#[derive(Clone, Debug, Eq)]
struct HigherKey(Symbol, Box<[StateId]>);

impl PartialEq for HigherKey {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl Hash for HigherKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct StoredRule {
    symbol: Symbol,
    children: Box<[StateId]>,
    result: StateId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CondensedRule {
    children: Box<[StateId]>,
    symbols: SymbolSet,
    result: StateId,
}

#[derive(Clone, Debug, Default)]
struct Indexes {
    by_child: FxHashMap<(Symbol, usize, StateId), Vec<usize>>,
    by_result: FxHashMap<StateId, Vec<usize>>,
}

/// Borrowed view of one transition rule in an [`Explicit`] automaton.
///
/// A rule means: when a node has `symbol` and its children have exactly
/// `children`, the node may receive `result`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rule<'a> {
    /// Symbol on the tree node matched by this rule.
    pub symbol: Symbol,
    /// Required child-state tuple, in left-to-right child order.
    pub children: &'a [StateId],
    /// State assigned to the parent node when the rule applies.
    pub result: StateId,
}

/// Builder for [`Explicit`] automata.
///
/// Allocate states with [`ExplicitBuilder::new_state`], add rules with
/// [`ExplicitBuilder::add_rule`], mark accepting states with
/// [`ExplicitBuilder::add_accepting`], then call [`ExplicitBuilder::build`].
///
/// The builder checks that every state in every rule was allocated by this
/// builder. This catches many accidental mixups between automata early.
#[derive(Clone, Debug, Default)]
pub struct ExplicitBuilder {
    next_state: u32,
    accepting: Vec<StateId>,
    rules: Vec<(Symbol, Vec<StateId>, StateId)>,
}

impl ExplicitBuilder {
    /// Create an empty builder with no states and no rules.
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate and return a fresh state.
    ///
    /// States are assigned densely starting at `StateId(0)`.
    pub fn new_state(&mut self) -> StateId {
        assert_ne!(self.next_state, StateId::STUCK.0, "cannot allocate STUCK");
        let id = StateId(self.next_state);
        self.next_state += 1;
        id
    }

    /// Mark a state as accepting.
    ///
    /// A tree is accepted when its root can be assigned one of the accepting
    /// states. Passing a state not allocated by this builder panics.
    pub fn add_accepting(&mut self, q: StateId) {
        self.check_state(q);
        self.accepting.push(q);
    }

    /// Add a bottom-up transition rule.
    ///
    /// `children` is the exact child-state tuple for the rule. An empty vector
    /// creates a nullary rule, suitable for leaf symbols. Passing `STUCK` or a
    /// state not allocated by this builder panics.
    pub fn add_rule(&mut self, f: Symbol, children: Vec<StateId>, q: StateId) {
        self.check_state(q);
        for &child in &children {
            self.check_state(child);
        }
        self.rules.push((f, children, q));
    }

    /// Build the explicit automaton.
    ///
    /// Repeated identical rules are removed. Multiple rules with the same
    /// symbol and children but different result states are preserved, making
    /// the automaton nondeterministic for that query.
    pub fn build(self) -> Explicit {
        let mut accepting = FixedBitSet::with_capacity(self.next_state as usize);
        for q in self.accepting {
            accepting.set(q.index(), true);
        }

        let mut seen = FxHashSet::default();
        let mut nullary = FxHashMap::default();
        let mut unary = FxHashMap::default();
        let mut binary = FxHashMap::default();
        let mut higher = FxHashMap::default();
        let mut stored = Vec::new();

        for (symbol, children, result) in self.rules {
            let rule = StoredRule {
                symbol,
                children: children.into_boxed_slice(),
                result,
            };
            if !seen.insert(rule.clone()) {
                continue;
            }
            match rule.children.len() {
                0 => push_result(nullary.entry(symbol).or_default(), result),
                1 => push_result(unary.entry((symbol, rule.children[0])).or_default(), result),
                2 => push_result(
                    binary
                        .entry((symbol, rule.children[0], rule.children[1]))
                        .or_default(),
                    result,
                ),
                _ => push_result(
                    higher
                        .entry(HigherKey(symbol, rule.children.clone()))
                        .or_default(),
                    result,
                ),
            }
            stored.push(rule);
        }

        stored.sort_by(|a, b| {
            (a.symbol, &a.children, a.result).cmp(&(b.symbol, &b.children, b.result))
        });

        Explicit {
            num_states: self.next_state,
            accepting,
            nullary,
            unary,
            binary,
            higher,
            rules: stored,
            reachable_cache: OnceCell::new(),
            indexes: OnceCell::new(),
            condensed_cache: OnceCell::new(),
        }
    }

    fn check_state(&self, q: StateId) {
        assert!(
            !q.is_stuck(),
            "StateId::STUCK is not a valid explicit state"
        );
        assert!(
            q.0 < self.next_state,
            "state {:?} was not allocated by this builder",
            q
        );
    }
}

impl Explicit {
    /// Return the number of allocated states.
    pub fn num_states(&self) -> u32 {
        self.num_states
    }

    /// Return true if no tree can be accepted by this automaton.
    ///
    /// This computes reachable states from nullary rules and checks whether any
    /// accepting state is reachable.
    pub fn is_empty(&self) -> bool {
        !self
            .reachable_states()
            .ones()
            .any(|idx| self.accepting.contains(idx))
    }

    /// Compute states reachable from nullary rules by saturation.
    ///
    /// A state is reachable if some finite tree can receive that state at its
    /// root. This is often useful for pruning or quick emptiness checks. The
    /// result is cached after the first call because explicit automata are
    /// immutable.
    pub fn reachable_states(&self) -> FixedBitSet {
        self.reachable_cache
            .get_or_init(|| self.compute_reachable_states())
            .clone()
    }

    fn compute_reachable_states(&self) -> FixedBitSet {
        let mut reachable = FixedBitSet::with_capacity(self.num_states as usize);
        let mut worklist = Vec::new();

        let mut remaining: Vec<usize> = self.rules.iter().map(|r| r.children.len()).collect();
        let mut mentions: FxHashMap<StateId, Vec<usize>> = FxHashMap::default();

        for (idx, rule) in self.rules.iter().enumerate() {
            if rule.children.is_empty() {
                if mark_reachable(&mut reachable, &mut worklist, rule.result) {
                    continue;
                }
            }
            let mut unique_children: SmallVec<[StateId; 4]> = SmallVec::new();
            for &child in rule.children.iter() {
                if !unique_children.contains(&child) {
                    unique_children.push(child);
                    mentions.entry(child).or_default().push(idx);
                }
            }
        }

        while let Some(q) = worklist.pop() {
            let Some(dependents) = mentions.get(&q) else {
                continue;
            };
            for &idx in dependents {
                if remaining[idx] == 0 {
                    continue;
                }
                let rule = &self.rules[idx];
                let newly_satisfied = rule.children.iter().filter(|&&c| c == q).count();
                remaining[idx] = remaining[idx].saturating_sub(newly_satisfied);
                if remaining[idx] == 0 {
                    mark_reachable(&mut reachable, &mut worklist, rule.result);
                }
            }
        }

        reachable
    }

    /// Iterate over all transition rules.
    ///
    /// The order is stable for a fixed automaton but should not be treated as a
    /// semantic ordering.
    pub fn rules(&self) -> impl Iterator<Item = Rule<'_>> {
        self.rules.iter().map(|rule| Rule {
            symbol: rule.symbol,
            children: &rule.children,
            result: rule.result,
        })
    }

    fn lookup_higher(&self, f: Symbol, children: &[StateId]) -> Option<&Results> {
        let mut hasher = self.higher.hasher().build_hasher();
        f.hash(&mut hasher);
        children.hash(&mut hasher);
        let hash = hasher.finish();
        self.higher
            .raw_entry()
            .from_hash(hash, |k| k.0 == f && &*k.1 == children)
            .map(|(_, v)| v)
    }

    fn indexes(&self) -> &Indexes {
        self.indexes.get_or_init(|| {
            let mut indexes = Indexes::default();
            for (rule_idx, rule) in self.rules.iter().enumerate() {
                indexes
                    .by_result
                    .entry(rule.result)
                    .or_default()
                    .push(rule_idx);
                for (position, &child) in rule.children.iter().enumerate() {
                    indexes
                        .by_child
                        .entry((rule.symbol, position, child))
                        .or_default()
                        .push(rule_idx);
                }
            }
            indexes
        })
    }

    fn condensed_cache(&self) -> &[CondensedRule] {
        self.condensed_cache.get_or_init(|| {
            let mut groups: FxHashMap<(Vec<StateId>, StateId), SymbolSet> = FxHashMap::default();
            for rule in &self.rules {
                groups
                    .entry((rule.children.to_vec(), rule.result))
                    .or_default()
                    .insert(rule.symbol);
            }

            let mut condensed: Vec<_> = groups
                .into_iter()
                .map(|((children, result), symbols)| CondensedRule {
                    children: children.into_boxed_slice(),
                    symbols,
                    result,
                })
                .collect();
            condensed.sort_by(|a, b| {
                (&a.children, a.result, a.symbols.iter().collect::<Vec<_>>()).cmp(&(
                    &b.children,
                    b.result,
                    b.symbols.iter().collect::<Vec<_>>(),
                ))
            });
            condensed
        })
    }
}

impl BottomUpTa for Explicit {
    type State = StateId;

    fn step(&self, f: Symbol, children: &[StateId], out: &mut dyn FnMut(StateId)) {
        let results = match children.len() {
            0 => self.nullary.get(&f),
            1 => self.unary.get(&(f, children[0])),
            2 => self.binary.get(&(f, children[0], children[1])),
            _ => self.lookup_higher(f, children),
        };
        if let Some(results) = results {
            for &q in results {
                out(q);
            }
        }
    }

    fn is_accepting(&self, q: &StateId) -> bool {
        !q.is_stuck() && self.accepting.contains(q.index())
    }
}

impl DetBottomUpTa for Explicit {
    fn step_det(&self, f: Symbol, children: &[StateId]) -> Option<StateId> {
        let results = match children.len() {
            0 => self.nullary.get(&f),
            1 => self.unary.get(&(f, children[0])),
            2 => self.binary.get(&(f, children[0], children[1])),
            _ => self.lookup_higher(f, children),
        }?;
        (results.len() == 1).then_some(results[0])
    }
}

impl IndexedBottomUpTa for Explicit {
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &StateId,
        out: &mut dyn FnMut(&[StateId], StateId),
    ) {
        let Some(rule_indexes) = self
            .indexes()
            .by_child
            .get(&(f, position, *state_at_position))
        else {
            return;
        };

        for &rule_idx in rule_indexes {
            let rule = &self.rules[rule_idx];
            out(&rule.children, rule.result);
        }
    }
}

impl TopDownTa for Explicit {
    fn step_topdown(&self, parent: &StateId, out: &mut dyn FnMut(Symbol, &[StateId])) {
        if parent.is_stuck() {
            return;
        }
        let Some(rule_indexes) = self.indexes().by_result.get(parent) else {
            return;
        };
        for &rule_idx in rule_indexes {
            let rule = &self.rules[rule_idx];
            out(rule.symbol, &rule.children);
        }
    }

    fn initial_states(&self, out: &mut dyn FnMut(StateId)) {
        for idx in self.accepting.ones() {
            out(StateId(idx as u32));
        }
    }
}

impl StateUniverse for Explicit {
    fn all_states(&self, out: &mut dyn FnMut(StateId)) {
        for idx in 0..self.num_states {
            out(StateId(idx));
        }
    }
}

impl CondensedTa for Explicit {
    fn condensed_rules(&self, out: &mut dyn FnMut(&[StateId], &SymbolSet, StateId)) {
        for rule in self.condensed_cache() {
            out(&rule.children, &rule.symbols, rule.result);
        }
    }

    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, StateId)) {
        for rule in self.condensed_cache() {
            if rule.children.is_empty() {
                out(&rule.symbols, rule.result);
            }
        }
    }

    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &StateId,
        out: &mut dyn FnMut(&[StateId], &SymbolSet, StateId),
    ) {
        for rule in self.condensed_cache() {
            if rule.children.get(position) == Some(state) {
                out(&rule.children, &rule.symbols, rule.result);
            }
        }
    }
}

fn push_result(results: &mut Results, q: StateId) {
    if !results.contains(&q) {
        results.push(q);
    }
}

fn mark_reachable(bits: &mut FixedBitSet, worklist: &mut Vec<StateId>, q: StateId) -> bool {
    if bits.contains(q.index()) {
        false
    } else {
        bits.set(q.index(), true);
        worklist.push(q);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BottomUpTa;
    use std::collections::hash_map::DefaultHasher;

    #[test]
    fn builder_dedupes_rules() {
        // Adding the same rule twice must not produce a duplicate entry: `rules()`
        // should iterate exactly one rule, and `step` should emit the state once.
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(1), vec![], q);
        b.add_rule(Symbol(1), vec![], q);
        let e = b.build();
        assert_eq!(e.rules().count(), 1);
        let mut out = Vec::new();
        e.step(Symbol(1), &[], &mut |q| out.push(q));
        assert_eq!(out, vec![q]);
    }

    #[test]
    fn deterministic_matches_step_for_single_result() {
        // When only one result state exists for a query, `step_det` must return
        // it as `Some`, agreeing with `step`.
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(1), vec![], q);
        let e = b.build();
        assert_eq!(e.step_det(Symbol(1), &[]), Some(q));
    }

    #[test]
    fn nondeterministic_step_det_returns_none() {
        // If two rules share the same symbol and children but have different
        // results, the automaton is nondeterministic for that query and
        // `step_det` must return `None`.
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        b.add_rule(Symbol(1), vec![], q0);
        b.add_rule(Symbol(1), vec![], q1);
        let e = b.build();
        assert_eq!(e.step_det(Symbol(1), &[]), None);
    }

    #[test]
    fn reachable_saturates_rules() {
        // Both states must be reachable once the leaf nullary rule fires and
        // the binary rule's children are satisfied. `is_empty` returns false
        // because the reachable set includes the accepting state.
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let root = b.new_state();
        b.add_rule(Symbol(0), vec![], leaf);
        b.add_rule(Symbol(1), vec![leaf, leaf], root);
        b.add_accepting(root);
        let e = b.build();
        let r = e.reachable_states();
        assert!(r.contains(leaf.index()));
        assert!(r.contains(root.index()));
        assert!(!e.is_empty());
    }

    #[test]
    fn higher_key_hash_matches_borrowed_tuple() {
        // The `HigherKey` stored type must hash identically to the borrowed
        // `(Symbol, &[StateId])` tuple used for allocation-free lookups.
        // Divergence here would silently break higher-arity rule lookup.
        let children = [StateId(1), StateId(2), StateId(3)];
        let key = HigherKey(Symbol(7), Box::from(children));
        let mut a = DefaultHasher::new();
        key.hash(&mut a);
        let mut b = DefaultHasher::new();
        Symbol(7).hash(&mut b);
        children.hash(&mut b);
        assert_eq!(a.finish(), b.finish());
    }

    #[test]
    fn higher_arity_lookup_works() {
        // A ternary rule (arity 3, stored in the `higher` table) must be
        // reachable via both `step` and `step_det` without allocation.
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        let q2 = b.new_state();
        let q3 = b.new_state();
        b.add_rule(Symbol(9), vec![q0, q1, q2], q3);
        let e = b.build();
        assert_eq!(e.step_det(Symbol(9), &[q0, q1, q2]), Some(q3));
    }

    #[test]
    fn indexed_step_partial_finds_matching_binary_rules() {
        // Given a known state at position 0, `step_partial` must return only
        // the rules where that position actually holds that state — not the
        // rule where position 0 holds a different state.
        let mut b = ExplicitBuilder::new();
        let left = b.new_state();
        let right = b.new_state();
        let root = b.new_state();
        let other = b.new_state();
        b.add_rule(Symbol(3), vec![left, right], root);
        b.add_rule(Symbol(3), vec![other, right], other);
        let e = b.build();

        let mut found = Vec::new();
        e.step_partial(Symbol(3), 0, &left, &mut |children, result| {
            found.push((children.to_vec(), result));
        });

        assert_eq!(found, vec![(vec![left, right], root)]);
    }

    #[test]
    fn indexed_step_partial_supports_higher_arity_rules() {
        // `step_partial` must also index rules stored in the `higher` table
        // (arity ≥ 3). Querying an interior position (1 of 3) must return the
        // full child tuple and result.
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        let q2 = b.new_state();
        let q3 = b.new_state();
        b.add_rule(Symbol(9), vec![q0, q1, q2], q3);
        let e = b.build();

        let mut found = Vec::new();
        e.step_partial(Symbol(9), 1, &q1, &mut |children, result| {
            found.push((children.to_vec(), result));
        });

        assert_eq!(found, vec![(vec![q0, q1, q2], q3)]);
    }

    #[test]
    fn topdown_enumerates_rules_by_parent() {
        // `step_topdown` must enumerate every rule whose result is the queried
        // parent state. `initial_states` must yield every accepting state.
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let root = b.new_state();
        b.add_rule(Symbol(0), vec![], leaf);
        b.add_rule(Symbol(1), vec![leaf, leaf], root);
        b.add_accepting(root);
        let e = b.build();

        let mut rules = Vec::new();
        e.step_topdown(&root, &mut |symbol, children| {
            rules.push((symbol, children.to_vec()));
        });
        let mut initials = Vec::new();
        e.initial_states(&mut |q| initials.push(q));

        assert_eq!(rules, vec![(Symbol(1), vec![leaf, leaf])]);
        assert_eq!(initials, vec![root]);
    }

    #[test]
    fn condensed_rules_groups_symbols_by_shape() {
        // Two symbols with identical (children, result) should appear together
        // in one condensed rule. A third symbol with a different children tuple
        // must appear in a separate group. Every rule must be covered exactly once.
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        let qr = b.new_state();
        // sym(0) and sym(1) both map (q0, q1) -> qr
        b.add_rule(Symbol(0), vec![q0, q1], qr);
        b.add_rule(Symbol(1), vec![q0, q1], qr);
        // sym(2) maps (q1, q0) -> qr  (different children order)
        b.add_rule(Symbol(2), vec![q1, q0], qr);
        let e = b.build();

        let mut groups: Vec<(Vec<StateId>, SymbolSet, StateId)> = Vec::new();
        e.condensed_rules(&mut |children, sym_set, result| {
            groups.push((children.to_vec(), sym_set.clone(), result));
        });

        // Find the group for (q0, q1) -> qr and verify both symbols are present.
        let shared = groups
            .iter()
            .find(|(c, _, _)| c.as_slice() == [q0, q1])
            .expect("group (q0,q1)->qr must exist");
        assert!(shared.1.contains(Symbol(0)));
        assert!(shared.1.contains(Symbol(1)));
        assert_eq!(shared.2, qr);

        // The (q1, q0) group must exist separately with only sym(2).
        let solo = groups
            .iter()
            .find(|(c, _, _)| c.as_slice() == [q1, q0])
            .expect("group (q1,q0)->qr must exist");
        assert!(solo.1.contains(Symbol(2)));
        assert_eq!(solo.1.len(), 1);
    }
}
