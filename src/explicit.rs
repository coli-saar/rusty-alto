use crate::{BottomUpTa, DetBottomUpTa, FxHashMap, FxHashSet, StateId, Symbol};
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
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(1), vec![], q);
        let e = b.build();
        assert_eq!(e.step_det(Symbol(1), &[]), Some(q));
    }

    #[test]
    fn nondeterministic_step_det_returns_none() {
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
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        let q2 = b.new_state();
        let q3 = b.new_state();
        b.add_rule(Symbol(9), vec![q0, q1, q2], q3);
        let e = b.build();
        assert_eq!(e.step_det(Symbol(9), &[q0, q1, q2]), Some(q3));
    }
}
