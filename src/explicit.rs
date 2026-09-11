//! Dense explicit weighted tree automata and their builder.

use crate::{
    BottomUpTa, DetBottomUpTa, FxHashMap, FxHashSet, IndexedBottomUpTa, StateId, Symbol, TopDownTa,
    language_analysis::{RuleInput, analyze_for_trimming, analyze_productive_for_trimming},
    traits::{CondensedTa, CondensedTopDownTa, StateUniverse, SymbolSet},
    util::dense_index::DenseIndex,
};
use fixedbitset::FixedBitSet;
use smallvec::SmallVec;
use std::hash::{BuildHasher, Hash, Hasher};
use std::sync::OnceLock;
use thiserror::Error;

type Results = SmallVec<[StateId; 2]>;

/// A fully materialized bottom-up tree automaton.
///
/// `Explicit` stores transition rules in lookup tables. It is the fastest
/// representation when all rules are known ahead of time or after an implicit
/// automaton has been materialized. Rules with arity 0, 1, and 2 use separate
/// compact tables because those are the common hot paths.
///
/// Build values with [`ExplicitBuilder`]. Every transition rule has a weight;
/// callers that do not have natural weights can use `1.0`.
#[derive(Clone, Debug)]
pub struct Explicit {
    num_states: u32,
    accepting: FixedBitSet,
    rules: Vec<StoredRule>,
    probability_weights: bool,
    bottom_up_indexes: OnceLock<BottomUpIndexes>,
    reachable_cache: OnceLock<FixedBitSet>,
    result_index: OnceLock<DenseIndex<RuleId>>,
    indexes: OnceLock<Indexes>,
    condensed_cache: OnceLock<Vec<CondensedRule>>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct RuleId(u32);

impl RuleId {
    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
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

#[derive(Clone, Debug)]
pub(crate) struct StoredRule {
    symbol: Symbol,
    children: SmallVec<[StateId; 2]>,
    result: StateId,
    weight: f64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RuleKey {
    symbol: Symbol,
    children: SmallVec<[StateId; 2]>,
    result: StateId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CondensedRule {
    children: Box<[StateId]>,
    symbols: SymbolSet,
    result: StateId,
}

#[derive(Clone, Debug, Default)]
struct BottomUpIndexes {
    nullary: FxHashMap<Symbol, Results>,
    unary: FxHashMap<(Symbol, StateId), Results>,
    binary: FxHashMap<(Symbol, StateId, StateId), Results>,
    higher: FxHashMap<HigherKey, Results>,
}

#[derive(Clone, Debug, Default)]
struct Indexes {
    by_child: FxHashMap<(Symbol, usize, StateId), Vec<usize>>,
}

/// Borrowed view of one transition rule in an [`Explicit`] automaton.
///
/// A rule means: when a node has `symbol` and its children have exactly
/// `children`, the node may receive `result`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Rule<'a> {
    /// Symbol on the tree node matched by this rule.
    pub symbol: Symbol,
    /// Required child-state tuple, in left-to-right child order.
    pub children: &'a [StateId],
    /// State assigned to the parent node when the rule applies.
    pub result: StateId,
    /// Weight assigned to this transition rule.
    pub weight: f64,
}

/// Error returned when an explicit automaton cannot be built.
#[derive(Clone, Debug, Error, PartialEq)]
pub enum ExplicitBuildError {
    /// The same transition was added more than once.
    #[error("duplicate transition for symbol {symbol:?}, children {children:?}, result {result:?}")]
    DuplicateTransition {
        /// Symbol on the duplicated transition.
        symbol: Symbol,
        /// Child-state tuple on the duplicated transition.
        children: Vec<StateId>,
        /// Parent/result state on the duplicated transition.
        result: StateId,
    },
}

/// A rule weight that cannot be interpreted as a probability.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("rule {rule_index} has weight {weight}; expected a finite value in [0, 1]")]
pub struct ProbabilityWeightError {
    /// Index of the first rule with an invalid weight.
    pub rule_index: usize,
    /// Invalid rule weight.
    pub weight: f64,
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
    rules: Vec<StoredRule>,
}

/// An explicit automaton produced by trimming, together with its state remapping.
#[derive(Clone, Debug)]
pub struct TrimmedExplicit {
    /// The compact automaton containing only states and rules that participate
    /// in at least one accepting derivation.
    pub automaton: Explicit,
    /// Mapping between builder state IDs and compact automaton state IDs.
    pub state_mapping: StateMapping,
}

/// Bidirectional state-ID mapping returned by [`ExplicitBuilder::build_trimmed`].
///
/// Trimming removes useless states and therefore must compact the surviving
/// IDs. New IDs are assigned in increasing old-ID order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateMapping {
    old_to_new: Vec<Option<StateId>>,
    new_to_old: Vec<StateId>,
}

impl StateMapping {
    /// Return the compact ID for an old builder ID, or `None` if it was removed.
    pub fn new_state(&self, old: StateId) -> Option<StateId> {
        self.old_to_new.get(old.index()).copied().flatten()
    }

    /// Return the old builder ID corresponding to a compact ID.
    ///
    /// Panics if `new` is not a state of the trimmed automaton.
    pub fn old_state(&self, new: StateId) -> StateId {
        self.new_to_old[new.index()]
    }

    /// Return the number of retained states.
    pub fn len(&self) -> usize {
        self.new_to_old.len()
    }

    /// Return whether no states were retained.
    pub fn is_empty(&self) -> bool {
        self.new_to_old.is_empty()
    }
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
        self.add_weighted_rule(f, children, q, 1.0);
    }

    /// Add a bottom-up transition rule from an iterator of child states.
    ///
    /// This avoids requiring a temporary `Vec` when a caller already has an
    /// iterator or compact child tuple.
    pub fn add_rule_from_iter(
        &mut self,
        f: Symbol,
        children: impl IntoIterator<Item = StateId>,
        q: StateId,
    ) {
        self.add_weighted_rule_inline(f, children.into_iter().collect(), q, 1.0);
    }

    /// Add a weighted bottom-up transition rule.
    ///
    /// `children` is the exact child-state tuple for the rule. An empty vector
    /// creates a nullary rule, suitable for leaf symbols. Passing `STUCK` or a
    /// state not allocated by this builder panics.
    pub fn add_weighted_rule(
        &mut self,
        f: Symbol,
        children: Vec<StateId>,
        q: StateId,
        weight: f64,
    ) {
        self.add_weighted_rule_inline(f, SmallVec::from_vec(children), q, weight);
    }

    /// Add a weighted rule from an inline child tuple.
    ///
    /// This avoids round-tripping through `Vec` in internal materializers that
    /// already build child tuples in the same inline representation used by
    /// [`Explicit`].
    pub(crate) fn add_weighted_rule_inline(
        &mut self,
        f: Symbol,
        children: SmallVec<[StateId; 2]>,
        q: StateId,
        weight: f64,
    ) {
        self.check_state(q);
        for &child in &children {
            self.check_state(child);
        }
        self.rules.push(StoredRule {
            symbol: f,
            children,
            result: q,
            weight,
        });
    }

    /// Build the explicit automaton.
    ///
    /// Panics if duplicate transitions were added. Use [`Self::try_build`] to
    /// receive a typed error instead.
    pub fn build(self) -> Explicit {
        self.try_build()
            .expect("explicit automaton contains duplicate transitions")
    }

    /// Build the explicit automaton, rejecting duplicate transitions.
    ///
    /// Multiple rules with the same symbol and children but different result
    /// states are preserved, making the automaton nondeterministic for that
    /// query. The exact same `(symbol, children, result)` transition may not be
    /// added twice, regardless of weight.
    pub fn try_build(self) -> Result<Explicit, ExplicitBuildError> {
        self.finish(true)
    }

    /// Build only the states and rules that can occur in accepting derivations.
    ///
    /// Duplicate surviving rules remain errors. Duplicates confined to a
    /// discarded component do not affect the resulting automaton and are
    /// ignored. Panics on an error, matching [`Self::build`].
    pub fn build_trimmed(self) -> TrimmedExplicit {
        self.try_build_trimmed()
            .expect("explicit automaton contains duplicate transitions")
    }

    /// Build a trimmed automaton when every allocated state is known productive.
    ///
    /// This skips productivity analysis and removes only states that cannot
    /// occur below an accepting state. Callers constructing states bottom-up
    /// from rules with productive children can use this without exposing their
    /// construction bookkeeping.
    pub fn build_trimmed_assuming_productive(self) -> TrimmedExplicit {
        self.try_build_trimmed_assuming_productive()
            .expect("explicit automaton contains duplicate transitions")
    }

    /// Try to build a trimmed explicit automaton and its state remapping.
    ///
    /// A state is retained exactly when it is productive and reachable below
    /// an accepting state through productive rules. Productive cycles are
    /// retained when they can participate in acceptance. Surviving state IDs
    /// are compacted deterministically in increasing old-ID order.
    pub fn try_build_trimmed(self) -> Result<TrimmedExplicit, ExplicitBuildError> {
        self.try_build_trimmed_inner(false)
    }

    /// Try to build a trimmed automaton when every allocated state is productive.
    ///
    /// This is the fallible counterpart of
    /// [`Self::build_trimmed_assuming_productive`].
    pub fn try_build_trimmed_assuming_productive(
        self,
    ) -> Result<TrimmedExplicit, ExplicitBuildError> {
        self.try_build_trimmed_inner(true)
    }

    fn try_build_trimmed_inner(
        self,
        assume_productive: bool,
    ) -> Result<TrimmedExplicit, ExplicitBuildError> {
        let inputs = self
            .rules
            .iter()
            .map(|rule| RuleInput {
                children: &rule.children,
                result: rule.result,
            })
            .collect::<Vec<_>>();
        let analysis = if assume_productive {
            analyze_productive_for_trimming(
                self.next_state as usize,
                &inputs,
                self.accepting.iter().copied(),
            )
        } else {
            analyze_for_trimming(
                self.next_state as usize,
                &inputs,
                self.accepting.iter().copied(),
            )
        };

        let mut old_to_new = vec![None; self.next_state as usize];
        let mut new_to_old = Vec::new();
        for (old_index, &useful) in analysis.relevant.iter().enumerate() {
            if useful {
                let new = StateId(new_to_old.len() as u32);
                old_to_new[old_index] = Some(new);
                new_to_old.push(StateId(old_index as u32));
            }
        }

        let mut accepting = FixedBitSet::with_capacity(new_to_old.len());
        for old in self.accepting {
            if let Some(new) = old_to_new[old.index()] {
                accepting.set(new.index(), true);
            }
        }

        let mut rules = Vec::new();
        let mut seen = FxHashSet::default();
        for (rule_index, rule) in self.rules.into_iter().enumerate() {
            if !analysis.productive_rules[rule_index] || !analysis.relevant[rule.result.index()] {
                continue;
            }
            let stored = StoredRule {
                symbol: rule.symbol,
                children: rule
                    .children
                    .into_iter()
                    .map(|child| old_to_new[child.index()].expect("useful child must be retained"))
                    .collect(),
                result: old_to_new[rule.result.index()].expect("useful result must be retained"),
                weight: rule.weight,
            };
            let key = RuleKey {
                symbol: stored.symbol,
                children: stored.children.clone(),
                result: stored.result,
            };
            if !seen.insert(key) {
                return Err(ExplicitBuildError::DuplicateTransition {
                    symbol: stored.symbol,
                    children: stored.children.into_vec(),
                    result: stored.result,
                });
            }
            rules.push(stored);
        }

        let state_mapping = StateMapping {
            old_to_new,
            new_to_old,
        };
        let automaton = Explicit::from_parts(state_mapping.len() as u32, accepting, rules);
        Ok(TrimmedExplicit {
            automaton,
            state_mapping,
        })
    }

    /// Build without checking for duplicate transitions.
    ///
    /// This is for internal algorithms that already enforce uniqueness while
    /// generating rules. External parsers and callers should use [`Self::build`]
    /// or [`Self::try_build`] so duplicates are rejected.
    pub(crate) fn build_trusted(self) -> Explicit {
        self.finish(false)
            .expect("trusted explicit automaton build cannot fail")
    }

    fn finish(self, check_duplicates: bool) -> Result<Explicit, ExplicitBuildError> {
        let mut accepting = FixedBitSet::with_capacity(self.next_state as usize);
        for q in self.accepting {
            accepting.set(q.index(), true);
        }

        let mut seen = FxHashSet::default();
        let mut stored = Vec::with_capacity(self.rules.len());

        for rule in self.rules {
            if check_duplicates {
                let key = RuleKey {
                    symbol: rule.symbol,
                    children: rule.children.clone(),
                    result: rule.result,
                };
                if !seen.insert(key) {
                    return Err(ExplicitBuildError::DuplicateTransition {
                        symbol: rule.symbol,
                        children: rule.children.into_vec(),
                        result: rule.result,
                    });
                }
            }
            stored.push(rule);
        }

        Ok(Explicit::from_parts(self.next_state, accepting, stored))
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
    fn from_parts(num_states: u32, accepting: FixedBitSet, rules: Vec<StoredRule>) -> Self {
        assert!(
            rules.len() <= u32::MAX as usize,
            "an explicit automaton cannot contain more than u32::MAX rules"
        );
        let probability_weights = rules
            .iter()
            .all(|rule| rule.weight.is_finite() && (0.0..=1.0).contains(&rule.weight));
        Self {
            num_states,
            accepting,
            rules,
            probability_weights,
            bottom_up_indexes: OnceLock::new(),
            reachable_cache: OnceLock::new(),
            result_index: OnceLock::new(),
            indexes: OnceLock::new(),
            condensed_cache: OnceLock::new(),
        }
    }

    /// Return the number of allocated states.
    pub fn num_states(&self) -> u32 {
        self.num_states
    }

    /// Return the number of transition rules in this automaton.
    pub fn num_rules(&self) -> usize {
        self.rules.len()
    }

    /// Check that every rule weight is a finite value in `[0, 1]`.
    ///
    /// Algorithms that extend a derivation by multiplying another rule weight,
    /// such as sorted-language iteration, require this monotonicity contract.
    /// Valid automata take constant time to check; invalid automata are scanned
    /// once to identify the offending rule.
    pub fn validate_probability_weights(&self) -> Result<(), ProbabilityWeightError> {
        if self.probability_weights {
            return Ok(());
        }
        let (rule_index, rule) = self
            .rules
            .iter()
            .enumerate()
            .find(|(_, rule)| !rule.weight.is_finite() || !(0.0..=1.0).contains(&rule.weight))
            .expect("cached probability-weight validation must be consistent");
        Err(ProbabilityWeightError {
            rule_index,
            weight: rule.weight,
        })
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
        self.reachable_states_ref().clone()
    }

    pub(crate) fn reachable_states_ref(&self) -> &FixedBitSet {
        self.reachable_cache
            .get_or_init(|| self.compute_reachable_states())
    }

    fn compute_reachable_states(&self) -> FixedBitSet {
        let mut reachable = FixedBitSet::with_capacity(self.num_states as usize);
        let mut worklist = Vec::new();

        let mut remaining: Vec<usize> = self.rules.iter().map(|r| r.children.len()).collect();
        for rule in &self.rules {
            if rule.children.is_empty()
                && mark_reachable(&mut reachable, &mut worklist, rule.result)
            {
                continue;
            }
        }

        // Keep one mention per child occurrence. When a state becomes
        // reachable, each occurrence discharges one slot in `remaining`; this
        // handles repeated children without rescanning the rule. Dense state
        // IDs let us use one compact CSR index instead of a hash of vectors.
        let mentions = DenseIndex::from_pairs(
            self.num_states as usize,
            self.rules.iter().enumerate().flat_map(|(rule_idx, rule)| {
                rule.children
                    .iter()
                    .map(move |child| (child.index(), rule_idx))
            }),
        );

        while let Some(q) = worklist.pop() {
            for &idx in mentions.values(q.index()) {
                if remaining[idx] == 0 {
                    continue;
                }
                let rule = &self.rules[idx];
                remaining[idx] -= 1;
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
            children: rule.children.as_slice(),
            result: rule.result,
            weight: rule.weight,
        })
    }

    /// Iterate over rules with the given parent/result state.
    pub fn rules_topdown(&self, parent: StateId) -> impl Iterator<Item = Rule<'_>> {
        self.result_index()
            .values(parent.index())
            .iter()
            .map(|&rule_id| self.rule_by_id(rule_id))
    }

    /// Return the transition rule at the given index.
    ///
    /// Provides O(1) indexed access to a borrowed view of a rule; the children
    /// slice is not copied. The index must be less than [`Self::num_rules`];
    /// passing an out-of-bounds index panics. Rule order matches the order
    /// produced by [`Self::rules`].
    pub fn rule(&self, rule_idx: usize) -> Rule<'_> {
        let rule = &self.rules[rule_idx];
        Rule {
            symbol: rule.symbol,
            children: rule.children.as_slice(),
            result: rule.result,
            weight: rule.weight,
        }
    }

    #[inline]
    pub(crate) fn rule_by_id(&self, rule_id: RuleId) -> Rule<'_> {
        self.rule(rule_id.index())
    }

    pub(crate) fn rule_indexes_topdown(&self, parent: StateId) -> &[RuleId] {
        self.result_index().values(parent.index())
    }

    fn result_index(&self) -> &DenseIndex<RuleId> {
        self.result_index.get_or_init(|| {
            DenseIndex::from_pairs(
                self.num_states as usize,
                self.rules.iter().enumerate().map(|(rule_index, rule)| {
                    (
                        rule.result.index(),
                        RuleId(u32::try_from(rule_index).expect("rule-count invariant violated")),
                    )
                }),
            )
        })
    }

    fn bottom_up_indexes(&self) -> &BottomUpIndexes {
        self.bottom_up_indexes.get_or_init(|| {
            let mut indexes = BottomUpIndexes::default();
            for rule in &self.rules {
                match rule.children.len() {
                    0 => push_result(indexes.nullary.entry(rule.symbol).or_default(), rule.result),
                    1 => push_result(
                        indexes
                            .unary
                            .entry((rule.symbol, rule.children[0]))
                            .or_default(),
                        rule.result,
                    ),
                    2 => push_result(
                        indexes
                            .binary
                            .entry((rule.symbol, rule.children[0], rule.children[1]))
                            .or_default(),
                        rule.result,
                    ),
                    _ => push_result(
                        indexes
                            .higher
                            .entry(HigherKey(
                                rule.symbol,
                                rule.children.clone().into_vec().into_boxed_slice(),
                            ))
                            .or_default(),
                        rule.result,
                    ),
                }
            }
            indexes
        })
    }

    fn lookup_higher<'a>(
        indexes: &'a BottomUpIndexes,
        f: Symbol,
        children: &[StateId],
    ) -> Option<&'a Results> {
        let mut hasher = indexes.higher.hasher().build_hasher();
        f.hash(&mut hasher);
        children.hash(&mut hasher);
        let hash = hasher.finish();
        indexes
            .higher
            .raw_entry()
            .from_hash(hash, |k| k.0 == f && &*k.1 == children)
            .map(|(_, v)| v)
    }

    fn indexes(&self) -> &Indexes {
        self.indexes.get_or_init(|| {
            let mut indexes = Indexes::default();
            for (rule_idx, rule) in self.rules.iter().enumerate() {
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
        let indexes = self.bottom_up_indexes();
        let results = match children.len() {
            0 => indexes.nullary.get(&f),
            1 => indexes.unary.get(&(f, children[0])),
            2 => indexes.binary.get(&(f, children[0], children[1])),
            _ => Self::lookup_higher(indexes, f, children),
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
        let indexes = self.bottom_up_indexes();
        let results = match children.len() {
            0 => indexes.nullary.get(&f),
            1 => indexes.unary.get(&(f, children[0])),
            2 => indexes.binary.get(&(f, children[0], children[1])),
            _ => Self::lookup_higher(indexes, f, children),
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
        let Some(rule_indexes) = self.result_index().get(parent.index()) else {
            return;
        };
        for &rule_id in rule_indexes {
            let rule = &self.rules[rule_id.index()];
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

impl CondensedTopDownTa for Explicit {
    fn condensed_rules_by_parent(
        &self,
        parent: &StateId,
        out: &mut dyn FnMut(&SymbolSet, &[StateId]),
    ) {
        for rule in self.condensed_cache() {
            if &rule.result == parent {
                out(&rule.symbols, &rule.children);
            }
        }
    }

    fn condensed_initial_states(&self, out: &mut dyn FnMut(StateId)) {
        self.initial_states(out);
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
    fn trimming_removes_dead_states_and_maps_survivors_densely() {
        let mut b = ExplicitBuilder::new();
        let dead_leaf = b.new_state();
        let useful_leaf = b.new_state();
        let dead_cycle = b.new_state();
        let root = b.new_state();
        b.add_rule(Symbol(0), vec![], dead_leaf);
        b.add_weighted_rule(Symbol(1), vec![], useful_leaf, -0.0);
        b.add_rule(Symbol(2), vec![dead_cycle], dead_cycle);
        b.add_weighted_rule(Symbol(3), vec![useful_leaf], root, -2.5);
        b.add_accepting(root);

        let trimmed = b.build_trimmed();
        assert_eq!(trimmed.automaton.num_states(), 2);
        assert_eq!(trimmed.automaton.num_rules(), 2);
        assert_eq!(trimmed.state_mapping.new_state(dead_leaf), None);
        assert_eq!(trimmed.state_mapping.new_state(dead_cycle), None);
        assert_eq!(
            trimmed.state_mapping.new_state(useful_leaf),
            Some(StateId(0))
        );
        assert_eq!(trimmed.state_mapping.new_state(root), Some(StateId(1)));
        assert_eq!(trimmed.state_mapping.old_state(StateId(0)), useful_leaf);
        assert_eq!(trimmed.state_mapping.old_state(StateId(1)), root);
        assert!(trimmed.automaton.is_accepting(&StateId(1)));
        assert_eq!(
            trimmed.automaton.rule(0).weight.to_bits(),
            (-0.0f64).to_bits()
        );
        assert_eq!(trimmed.automaton.rule(1).weight, -2.5);
    }

    #[test]
    fn trimming_keeps_productive_cycles_and_excludes_unproductive_rules() {
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let bad = b.new_state();
        let root = b.new_state();
        b.add_rule(Symbol(0), vec![], leaf);
        b.add_rule(Symbol(1), vec![leaf], root);
        b.add_rule(Symbol(2), vec![root], leaf);
        b.add_rule(Symbol(3), vec![bad], root);
        b.add_rule(Symbol(4), vec![bad], bad);
        b.add_accepting(root);
        let trimmed = b.build_trimmed();
        assert_eq!(trimmed.automaton.num_states(), 2);
        assert_eq!(trimmed.automaton.num_rules(), 3);
        assert_eq!(
            trimmed.automaton.language_cardinality(),
            crate::LanguageCardinality::Infinite
        );
    }

    #[test]
    fn trimming_empty_language_returns_empty_mapping_and_automaton() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(0), vec![], q);
        let trimmed = b.build_trimmed();
        assert!(trimmed.state_mapping.is_empty());
        assert_eq!(trimmed.automaton.num_states(), 0);
        assert_eq!(trimmed.automaton.num_rules(), 0);
    }

    #[test]
    fn trimming_ignores_duplicates_in_dead_components() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(0), vec![], q);
        b.add_weighted_rule(Symbol(0), vec![], q, 2.0);
        let trimmed = b.try_build_trimmed().unwrap();
        assert!(trimmed.automaton.rules().next().is_none());
    }

    #[test]
    fn trimming_rejects_duplicate_surviving_transitions() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(0), vec![], q);
        b.add_weighted_rule(Symbol(0), vec![], q, 2.0);
        b.add_accepting(q);
        assert!(matches!(
            b.try_build_trimmed(),
            Err(ExplicitBuildError::DuplicateTransition { .. })
        ));
    }

    #[test]
    fn productive_trimming_matches_general_trimming() {
        fn builder() -> ExplicitBuilder {
            let mut b = ExplicitBuilder::new();
            let leaf = b.new_state();
            let middle = b.new_state();
            let root = b.new_state();
            b.add_rule(Symbol(0), vec![], leaf);
            b.add_rule(Symbol(1), vec![leaf], middle);
            b.add_rule(Symbol(2), vec![middle, leaf], root);
            b.add_rule(Symbol(3), vec![leaf], root);
            b.add_accepting(root);
            b
        }

        let general = builder().build_trimmed();
        let specialized = builder().build_trimmed_assuming_productive();
        assert_eq!(general.state_mapping, specialized.state_mapping);
        assert_eq!(
            general.automaton.rules().collect::<Vec<_>>(),
            specialized.automaton.rules().collect::<Vec<_>>()
        );
    }

    #[test]
    fn trimming_preserves_repeated_children_and_child_order() {
        let mut b = ExplicitBuilder::new();
        let first = b.new_state();
        let removed = b.new_state();
        let second = b.new_state();
        let root = b.new_state();
        b.add_rule(Symbol(0), vec![], first);
        b.add_rule(Symbol(1), vec![], second);
        b.add_rule(Symbol(2), vec![], removed);
        b.add_rule(Symbol(3), vec![second, first, second], root);
        b.add_accepting(root);
        let trimmed = b.build_trimmed();
        assert_eq!(trimmed.state_mapping.new_state(removed), None);
        assert_eq!(
            trimmed.automaton.rule(2).children,
            &[StateId(1), StateId(0), StateId(1)]
        );
    }

    #[test]
    fn trimming_a_deep_chain_is_iterative() {
        let mut b = ExplicitBuilder::new();
        let mut state = b.new_state();
        b.add_rule(Symbol(0), vec![], state);
        for _ in 0..20_000 {
            let parent = b.new_state();
            b.add_rule(Symbol(1), vec![state], parent);
            state = parent;
        }
        b.add_accepting(state);
        let trimmed = b.build_trimmed();
        assert_eq!(trimmed.automaton.num_states(), 20_001);
        assert_eq!(trimmed.automaton.num_rules(), 20_001);
    }

    #[test]
    fn add_rule_defaults_to_unit_weight() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_rule(Symbol(1), vec![], q);
        let e = b.build();
        let rule = e.rules().next().unwrap();
        assert_eq!(rule.weight, 1.0);
        let mut out = Vec::new();
        e.step(Symbol(1), &[], &mut |q| out.push(q));
        assert_eq!(out, vec![q]);
    }

    #[test]
    fn add_rule_from_iter_defaults_to_unit_weight_and_preserves_children() {
        let mut b = ExplicitBuilder::new();
        let child = b.new_state();
        let result = b.new_state();
        b.add_rule_from_iter(Symbol(1), [child, child], result);
        let e = b.build();
        let rule = e.rules().next().unwrap();
        assert_eq!(rule.children, &[child, child]);
        assert_eq!(rule.weight, 1.0);
    }

    #[test]
    fn add_weighted_rule_stores_weight() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_weighted_rule(Symbol(1), vec![], q, 0.25);
        let e = b.build();
        let rule = e.rules().next().unwrap();
        assert_eq!(rule.weight, 0.25);
    }

    #[test]
    fn add_weighted_rule_inline_preserves_child_tuple() {
        let mut b = ExplicitBuilder::new();
        let left = b.new_state();
        let right = b.new_state();
        let parent = b.new_state();
        b.add_weighted_rule_inline(
            Symbol(1),
            SmallVec::from_slice(&[left, right]),
            parent,
            0.75,
        );

        let e = b.build();
        let rule = e.rules().next().unwrap();
        assert_eq!(rule.children, &[left, right]);
        assert_eq!(rule.result, parent);
        assert_eq!(rule.weight, 0.75);
    }

    #[test]
    fn builder_rejects_duplicate_transition_with_same_weight() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_weighted_rule(Symbol(1), vec![], q, 0.5);
        b.add_weighted_rule(Symbol(1), vec![], q, 0.5);
        assert!(matches!(
            b.try_build(),
            Err(ExplicitBuildError::DuplicateTransition { .. })
        ));
    }

    #[test]
    fn builder_rejects_duplicate_transition_with_different_weight() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        b.add_weighted_rule(Symbol(1), vec![], q, 0.5);
        b.add_weighted_rule(Symbol(1), vec![], q, 0.75);
        assert!(matches!(
            b.try_build(),
            Err(ExplicitBuildError::DuplicateTransition { .. })
        ));
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
    fn bottom_up_indexes_are_built_lazily() {
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let root = b.new_state();
        b.add_rule(Symbol(0), vec![], leaf);
        b.add_rule(Symbol(1), vec![leaf], root);
        b.add_accepting(root);
        let e = b.build();

        assert!(e.bottom_up_indexes.get().is_none());

        let mut topdown_rules = Vec::new();
        e.step_topdown(&root, &mut |symbol, children| {
            topdown_rules.push((symbol, children.to_vec()));
        });
        assert_eq!(topdown_rules, vec![(Symbol(1), vec![leaf])]);
        assert!(e.bottom_up_indexes.get().is_none());

        let best = e.viterbi().unwrap();
        assert_eq!(*best.arena().get_label(best.root()), Symbol(1));
        assert!(e.bottom_up_indexes.get().is_none());

        let mut leaves = Vec::new();
        e.step(Symbol(0), &[], &mut |q| leaves.push(q));
        assert_eq!(leaves, vec![leaf]);
        assert!(e.bottom_up_indexes.get().is_some());
    }

    // Indexed access and iteration must yield identical Rule values in the same order.
    #[test]
    fn indexed_rule_access_matches_iteration() {
        let mut b = ExplicitBuilder::new();
        let q = b.new_state();
        let r = b.new_state();
        b.add_rule(Symbol(0), vec![], q);
        b.add_rule(Symbol(1), vec![q], r);
        b.add_accepting(r);
        let a = b.build();

        assert_eq!(a.num_rules(), 2);
        for (i, rule) in a.rules().enumerate() {
            assert_eq!(a.rule(i), rule);
        }
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
