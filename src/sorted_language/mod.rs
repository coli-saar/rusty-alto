//! State-agenda implementation of lazy k-best language iteration.
//!
//! The iterator keeps one persistent candidate heap per touched state, stores
//! finalized items as compact backpointers, and constructs trees only after an
//! accepting item has been selected.

mod state_stream_table;

use crate::{Explicit, StateId, Symbol, TopDownTa};
use fixedbitset::FixedBitSet;
use packed_term_arena::tree::{Tree, TreeArena};
use smallvec::SmallVec;
use state_stream_table::StateStreamTable;
use std::{cmp::Ordering, collections::BinaryHeap, mem};

/// A weighted tree produced by [`SortedLanguageIterator`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct WeightedTree {
    tree: Tree,
    weight: f64,
}

impl WeightedTree {
    /// Return this tree's root in the producing iterator's arena.
    pub fn tree(&self) -> Tree {
        self.tree
    }

    /// Return the product of the tree's rule weights.
    pub fn weight(&self) -> f64 {
        self.weight
    }
}

/// Lazily enumerate accepted derivations in descending weight order.
///
/// Runtime state streams are allocated on demand. Each stream owns one heap
/// containing candidates from all rules for that state; a popped candidate is
/// retained only as a rule-and-child-ranks backpointer. The implementation has
pub struct SortedLanguageIterator<'a> {
    automaton: &'a Explicit,
    productive: &'a FixedBitSet,
    accepting: Vec<StateId>,
    state_streams: StateStreamTable<StateStream>,
    root_agenda: BinaryHeap<RootHeapItem>,
    root_initialized: bool,
    pending_root_successor: Option<(StateId, usize)>,
    arena: TreeArena<Symbol>,
    visiting: FixedBitSet,
    next_seq: usize,
}

impl Explicit {
    /// Iterate over accepted trees in descending weight order.
    pub fn sorted_language(&self) -> SortedLanguageIterator<'_> {
        SortedLanguageIterator::new(self)
    }
}

impl<'a> SortedLanguageIterator<'a> {
    /// Construct an iterator without allocating streams for untouched states.
    pub fn new(automaton: &'a Explicit) -> Self {
        let mut accepting = Vec::new();
        automaton.initial_states(&mut |state| accepting.push(state));
        let productive = automaton.reachable_states_ref();

        Self {
            automaton,
            productive,
            accepting,
            state_streams: StateStreamTable::default(),
            root_agenda: BinaryHeap::new(),
            root_initialized: false,
            pending_root_successor: None,
            arena: TreeArena::new(),
            visiting: FixedBitSet::with_capacity(automaton.num_states() as usize),
            next_seq: 0,
        }
    }

    /// Return the arena containing trees returned so far.
    pub fn arena(&self) -> &TreeArena<Symbol> {
        &self.arena
    }

    /// Clone a generated tree into an independent arena.
    pub fn clone_tree(&self, root: Tree) -> (TreeArena<Symbol>, Tree) {
        let mut target = TreeArena::new();
        let root = self.arena.copy_into(root, &mut target);
        (target, root)
    }

    fn ensure_state_stream(&mut self, state: StateId) {
        if self.state_streams.contains_key(&state) {
            return;
        }

        let rule_count = self.automaton.rule_indexes_topdown(state).len();
        let candidates =
            PendingCandidates::new(self.productive.contains(state.index()), rule_count);

        self.state_streams.insert(
            state,
            StateStream {
                known: Vec::new(),
                materialized: Vec::new(),
                agenda: BinaryHeap::new(),
                candidates,
                next_unexpanded: 0,
            },
        );
    }

    fn state_item_weight(&mut self, state: StateId, rank: usize) -> Option<f64> {
        self.ensure_state_stream(state);
        if let Some(item) = self.state_streams[&state].known.get(rank) {
            return Some(item.weight);
        }

        let nullary_only = {
            let stream = &self.state_streams[&state];
            let rules = self.automaton.rule_indexes_topdown(state);
            stream.candidates.generated.is_empty()
                && stream.agenda.is_empty()
                && stream.next_unexpanded == stream.known.len()
                && stream.candidates.has_unstarted(rules.len())
                && rules[stream.candidates.next_rule..]
                    .iter()
                    .all(|&rule| self.automaton.rule(rule).children.is_empty())
        };
        if nullary_only {
            let rules = self.automaton.rule_indexes_topdown(state);
            let range = self
                .state_streams
                .get_mut(&state)
                .expect("state stream must exist")
                .candidates
                .take_unstarted(rules.len());
            if range.len() == 1 {
                let rule = rules[range.start];
                let candidate = ScoredCandidate {
                    rule,
                    base_rank: 0,
                    dimension: ZERO_DIMENSION,
                    weight: self.automaton.rule(rule).weight,
                };
                return Some(self.finalize_candidate(state, candidate));
            }
            let ready = rules[range]
                .iter()
                .map(|&rule| ScoredCandidate {
                    rule,
                    base_rank: 0,
                    dimension: ZERO_DIMENSION,
                    weight: self.automaton.rule(rule).weight,
                })
                .collect();
            self.extend_agenda(state, ready);
        }

        if rank == self.state_streams[&state].known.len() && !self.visiting.contains(state.index())
        {
            self.expand_pending(state);
        }

        let stream = &self.state_streams[&state];
        if rank == stream.known.len()
            && !self.visiting.contains(state.index())
            && stream.next_unexpanded == stream.known.len()
            && !stream.agenda.is_empty()
            && stream
                .candidates
                .is_empty(self.automaton.rule_indexes_topdown(state).len())
        {
            let candidate = self
                .state_streams
                .get_mut(&state)
                .expect("state stream must exist")
                .agenda
                .pop()
                .map(|entry| entry.candidate)?;
            return Some(self.finalize_candidate(state, candidate));
        }

        match self.ensure_item_recursive(state, rank, 0) {
            EnsureOutcome::Available(weight) => Some(weight),
            EnsureOutcome::Exhausted | EnsureOutcome::Blocked => None,
        }
    }

    fn ensure_item_recursive(
        &mut self,
        state: StateId,
        rank: usize,
        depth: usize,
    ) -> EnsureOutcome {
        const RECURSION_LIMIT: usize = 512;
        if depth == RECURSION_LIMIT {
            return self.ensure_item(state, rank);
        }

        self.ensure_state_stream(state);
        if let Some(item) = self.state_streams[&state].known.get(rank) {
            return EnsureOutcome::Available(item.weight);
        }
        if rank != self.state_streams[&state].known.len() || self.visiting.contains(state.index()) {
            return EnsureOutcome::Blocked;
        }

        self.visiting.set(state.index(), true);
        self.expand_pending(state);
        let rule_count = self.automaton.rule_indexes_topdown(state).len();
        let initial_rules = self
            .state_streams
            .get_mut(&state)
            .expect("state stream must exist")
            .candidates
            .take_unstarted(rule_count);
        let mut leftovers = SmallVec::<[TupleCandidate; 2]>::new();
        let mut ready = SmallVec::<[ScoredCandidate; 2]>::new();
        while let Some(candidate) = self
            .state_streams
            .get_mut(&state)
            .expect("state stream must exist")
            .candidates
            .generated
            .pop()
        {
            match self.resolve_candidate_recursive(state, candidate, depth + 1) {
                CandidateOutcome::Ready(candidate) => ready.push(candidate),
                CandidateOutcome::Blocked(candidate) => leftovers.push(candidate),
                CandidateOutcome::Dead => {}
            }
        }
        for position in initial_rules {
            let rule = self.automaton.rule_indexes_topdown(state)[position];
            if !self
                .automaton
                .rule(rule)
                .children
                .iter()
                .all(|child| self.productive.contains(child.index()))
            {
                continue;
            }
            let candidate = TupleCandidate {
                rule,
                ranks: CandidateRanks::Zero,
            };
            match self.resolve_candidate_recursive(state, candidate, depth + 1) {
                CandidateOutcome::Ready(candidate) => ready.push(candidate),
                CandidateOutcome::Blocked(candidate) => leftovers.push(candidate),
                CandidateOutcome::Dead => {}
            }
        }
        self.state_streams
            .get_mut(&state)
            .expect("state stream must exist")
            .candidates
            .generated
            .extend(leftovers);
        let popped = self.merge_ready_and_pop(state, ready);
        self.visiting.set(state.index(), false);
        if let Some(candidate) = popped {
            EnsureOutcome::Available(self.finalize_candidate(state, candidate))
        } else if self.state_streams[&state].candidates.is_empty(rule_count) {
            EnsureOutcome::Exhausted
        } else {
            EnsureOutcome::Blocked
        }
    }

    fn resolve_candidate_recursive(
        &mut self,
        owner: StateId,
        candidate: TupleCandidate,
        depth: usize,
    ) -> CandidateOutcome {
        match &candidate.ranks {
            CandidateRanks::Zero => {
                let rule = self.automaton.rule(candidate.rule);
                let weight = match rule.children {
                    [] => rule.weight,
                    &[child] => match self.ensure_item_recursive(child, 0, depth) {
                        EnsureOutcome::Available(child_weight) => rule.weight * child_weight,
                        EnsureOutcome::Exhausted => return CandidateOutcome::Dead,
                        EnsureOutcome::Blocked => return CandidateOutcome::Blocked(candidate),
                    },
                    &[left, right] => {
                        let left_weight = match self.ensure_item_recursive(left, 0, depth) {
                            EnsureOutcome::Available(weight) => weight,
                            EnsureOutcome::Exhausted => return CandidateOutcome::Dead,
                            EnsureOutcome::Blocked => {
                                return CandidateOutcome::Blocked(candidate);
                            }
                        };
                        let right_weight = match self.ensure_item_recursive(right, 0, depth) {
                            EnsureOutcome::Available(weight) => weight,
                            EnsureOutcome::Exhausted => return CandidateOutcome::Dead,
                            EnsureOutcome::Blocked => {
                                return CandidateOutcome::Blocked(candidate);
                            }
                        };
                        (rule.weight * left_weight) * right_weight
                    }
                    children => {
                        let children: SmallVec<[StateId; 2]> = children.iter().copied().collect();
                        let mut weight = rule.weight;
                        for child in children {
                            match self.ensure_item_recursive(child, 0, depth) {
                                EnsureOutcome::Available(child_weight) => weight *= child_weight,
                                EnsureOutcome::Exhausted => return CandidateOutcome::Dead,
                                EnsureOutcome::Blocked => {
                                    return CandidateOutcome::Blocked(candidate);
                                }
                            }
                        }
                        weight
                    }
                };
                CandidateOutcome::Ready(ScoredCandidate {
                    rule: candidate.rule,
                    base_rank: 0,
                    dimension: ZERO_DIMENSION,
                    weight,
                })
            }
            CandidateRanks::Bump {
                base_rank,
                dimension,
                left_factor,
                right_factor,
                ..
            } => {
                let next_rank = self.child_rank(owner, *base_rank, *dimension) + 1;
                let child = self.automaton.rule(candidate.rule).children[*dimension];
                match self.ensure_item_recursive(child, next_rank, depth) {
                    EnsureOutcome::Available(child_weight) => {
                        CandidateOutcome::Ready(ScoredCandidate {
                            rule: candidate.rule,
                            base_rank: *base_rank,
                            dimension: *dimension,
                            weight: self.bump_weight(child_weight, *left_factor, *right_factor),
                        })
                    }
                    EnsureOutcome::Exhausted => CandidateOutcome::Dead,
                    EnsureOutcome::Blocked => CandidateOutcome::Blocked(candidate),
                }
            }
        }
    }

    fn ensure_item(&mut self, state: StateId, rank: usize) -> EnsureOutcome {
        let mut frames = vec![SearchFrame::Ensure { state, rank }];
        let mut ensured = None;
        let mut resolved = None;

        while let Some(frame) = frames.pop() {
            match frame {
                SearchFrame::Ensure { state, rank } => {
                    self.ensure_state_stream(state);
                    if let Some(item) = self.state_streams[&state].known.get(rank) {
                        ensured = Some(EnsureOutcome::Available(item.weight));
                    } else if rank != self.state_streams[&state].known.len()
                        || self.visiting.contains(state.index())
                    {
                        ensured = Some(EnsureOutcome::Blocked);
                    } else {
                        self.visiting.set(state.index(), true);
                        self.expand_pending(state);
                        let rule_count = self.automaton.rule_indexes_topdown(state).len();
                        let (mut candidates, initial_rules) = self
                            .state_streams
                            .get_mut(&state)
                            .expect("state stream must exist")
                            .candidates
                            .take(rule_count);
                        candidates.extend(initial_rules.filter_map(|position| {
                            let rule = self.automaton.rule_indexes_topdown(state)[position];
                            self.automaton
                                .rule(rule)
                                .children
                                .iter()
                                .all(|child| self.productive.contains(child.index()))
                                .then_some(TupleCandidate {
                                    rule,
                                    ranks: CandidateRanks::Zero,
                                })
                        }));
                        frames.push(SearchFrame::EvaluateState {
                            state,
                            candidates: candidates.into_iter(),
                            leftovers: Vec::new(),
                            ready: Vec::new(),
                        });
                    }
                }
                SearchFrame::EvaluateState {
                    state,
                    mut candidates,
                    mut leftovers,
                    mut ready,
                } => {
                    if let Some(candidate_result) = resolved.take() {
                        match candidate_result {
                            CandidateOutcome::Ready(candidate) => ready.push(candidate),
                            CandidateOutcome::Blocked(candidate) => leftovers.push(candidate),
                            CandidateOutcome::Dead => {}
                        }
                    }

                    if let Some(candidate) = candidates.next() {
                        frames.push(SearchFrame::EvaluateState {
                            state,
                            candidates,
                            leftovers,
                            ready,
                        });
                        frames.push(SearchFrame::ResolveCandidate {
                            owner: state,
                            candidate,
                            next_child: 0,
                            weight: 0.0,
                        });
                    } else {
                        self.state_streams
                            .get_mut(&state)
                            .expect("state stream must exist")
                            .candidates
                            .generated
                            .extend(leftovers);
                        self.extend_agenda(state, ready);
                        let popped = self
                            .state_streams
                            .get_mut(&state)
                            .expect("state stream must exist")
                            .agenda
                            .pop()
                            .map(|entry| entry.candidate);
                        self.visiting.set(state.index(), false);
                        ensured = Some(if let Some(candidate) = popped {
                            EnsureOutcome::Available(self.finalize_candidate(state, candidate))
                        } else if self.state_streams[&state]
                            .candidates
                            .is_empty(self.automaton.rule_indexes_topdown(state).len())
                        {
                            EnsureOutcome::Exhausted
                        } else {
                            EnsureOutcome::Blocked
                        });
                    }
                }
                SearchFrame::ResolveCandidate {
                    owner,
                    candidate,
                    next_child,
                    mut weight,
                } => {
                    if next_child != 0 {
                        match ensured
                            .take()
                            .expect("child request must produce an outcome")
                        {
                            EnsureOutcome::Available(child_weight) => {
                                if let CandidateRanks::Bump {
                                    left_factor,
                                    right_factor,
                                    ..
                                } = &candidate.ranks
                                {
                                    weight =
                                        self.bump_weight(child_weight, *left_factor, *right_factor);
                                } else {
                                    weight *= child_weight;
                                }
                            }
                            EnsureOutcome::Exhausted => {
                                resolved = Some(CandidateOutcome::Dead);
                                continue;
                            }
                            EnsureOutcome::Blocked => {
                                resolved = Some(CandidateOutcome::Blocked(candidate));
                                continue;
                            }
                        }
                    }

                    match &candidate.ranks {
                        CandidateRanks::Zero => {
                            let rule = self.automaton.rule(candidate.rule);
                            if next_child == rule.children.len() {
                                resolved = Some(CandidateOutcome::Ready(ScoredCandidate {
                                    rule: candidate.rule,
                                    base_rank: 0,
                                    dimension: ZERO_DIMENSION,
                                    weight: if next_child == 0 { rule.weight } else { weight },
                                }));
                            } else {
                                let child = rule.children[next_child];
                                frames.push(SearchFrame::ResolveCandidate {
                                    owner,
                                    candidate,
                                    next_child: next_child + 1,
                                    weight: if next_child == 0 { rule.weight } else { weight },
                                });
                                frames.push(SearchFrame::Ensure {
                                    state: child,
                                    rank: 0,
                                });
                            }
                        }
                        CandidateRanks::Bump {
                            base_rank,
                            dimension,
                            ..
                        } => {
                            if next_child == 0 {
                                let old_rank = self.child_rank(owner, *base_rank, *dimension);
                                let child =
                                    self.automaton.rule(candidate.rule).children[*dimension];
                                frames.push(SearchFrame::ResolveCandidate {
                                    owner,
                                    candidate,
                                    next_child: 1,
                                    weight,
                                });
                                frames.push(SearchFrame::Ensure {
                                    state: child,
                                    rank: old_rank + 1,
                                });
                            } else {
                                resolved = Some(CandidateOutcome::Ready(ScoredCandidate {
                                    rule: candidate.rule,
                                    base_rank: *base_rank,
                                    dimension: *dimension,
                                    weight,
                                }));
                            }
                        }
                    }
                }
            }
        }

        ensured.expect("root request must produce an outcome")
    }

    fn finalize_candidate(&mut self, state: StateId, candidate: ScoredCandidate) -> f64 {
        let weight = candidate.weight;
        let arity = self.automaton.rule(candidate.rule).children.len();
        let ranks = if candidate.dimension == ZERO_DIMENSION {
            SmallVec::from_elem(0, arity)
        } else {
            let mut ranks = self.copy_child_ranks(state, candidate.base_rank, arity);
            ranks[candidate.dimension] += 1;
            ranks
        };
        let child_ranks = match ranks.as_slice() {
            [] => ChildRanks::Zero,
            &[child_rank] => ChildRanks::Unary(child_rank),
            &[left_rank, right_rank] => ChildRanks::Binary {
                left_rank,
                right_rank,
            },
            _ => ChildRanks::Nary(ranks.into_boxed_slice()),
        };
        let stream = self
            .state_streams
            .get_mut(&state)
            .expect("state stream must exist");
        stream.known.push(StateItem {
            rule: candidate.rule,
            child_ranks,
            weight,
        });
        if arity == 0 {
            stream.next_unexpanded += 1;
        }
        if arity == 1 {
            let item_rank = self.state_streams[&state].known.len() - 1;
            self.expand_successors(state, item_rank);
            self.state_streams
                .get_mut(&state)
                .expect("state stream must exist")
                .next_unexpanded += 1;
        }
        weight
    }

    fn bump_weight(&self, bumped_weight: f64, left_factor: f64, right_factor: f64) -> f64 {
        (left_factor * bumped_weight) * right_factor
    }

    fn child_rank(&self, state: StateId, item_rank: usize, dimension: usize) -> usize {
        self.state_streams[&state].known[item_rank]
            .child_ranks
            .child_rank(dimension)
    }

    fn copy_child_ranks(
        &self,
        state: StateId,
        item_rank: usize,
        _arity: usize,
    ) -> SmallVec<[usize; 2]> {
        self.state_streams[&state].known[item_rank]
            .child_ranks
            .child_ranks()
    }

    fn expand_successors(&mut self, state: StateId, item_rank: usize) {
        let item = &self.state_streams[&state].known[item_rank];
        let rule_index = item.rule;
        let rule = self.automaton.rule(rule_index);
        let arity = rule.children.len();
        match arity {
            0 => return,
            1 => {
                let child_rank = item.child_ranks.child_rank(0);
                let candidate = TupleCandidate {
                    rule: rule_index,
                    ranks: CandidateRanks::Bump {
                        base_rank: item_rank,
                        dimension: 0,
                        left_factor: rule.weight,
                        right_factor: 1.0,
                    },
                };
                debug_assert!(
                    self.state_streams[&rule.children[0]].known.len() > child_rank,
                    "finalized item must point to a known child"
                );
                self.state_streams
                    .get_mut(&state)
                    .expect("state stream must exist")
                    .candidates
                    .generated
                    .push(candidate);
                return;
            }
            2 => {
                let left_rank = item.child_ranks.child_rank(0);
                let right_rank = item.child_ranks.child_rank(1);
                let left_weight = self.state_streams[&rule.children[0]].known[left_rank].weight;
                let right_weight = self.state_streams[&rule.children[1]].known[right_rank].weight;
                let first = TupleCandidate {
                    rule: rule_index,
                    ranks: CandidateRanks::Bump {
                        base_rank: item_rank,
                        dimension: 0,
                        left_factor: rule.weight,
                        right_factor: right_weight,
                    },
                };
                let second = (left_rank == 0).then_some(TupleCandidate {
                    rule: rule_index,
                    ranks: CandidateRanks::Bump {
                        base_rank: item_rank,
                        dimension: 1,
                        left_factor: rule.weight * left_weight,
                        right_factor: 1.0,
                    },
                });
                let stream = self
                    .state_streams
                    .get_mut(&state)
                    .expect("state stream must exist");
                stream.candidates.generated.push(first);
                stream.candidates.generated.extend(second);
                return;
            }
            _ => {}
        }

        let child_ranks = self.copy_child_ranks(state, item_rank, arity);
        let child_states: SmallVec<[StateId; 2]> = rule.children.iter().copied().collect();
        let rule_weight = rule.weight;
        let limit = canonical_successor_limit(&child_ranks);

        let mut child_weights = SmallVec::<[f64; 2]>::with_capacity(arity);
        for (&child_state, &child_rank) in child_states.iter().zip(&child_ranks) {
            child_weights.push(self.state_streams[&child_state].known[child_rank].weight);
        }

        let mut prefixes = SmallVec::<[f64; 3]>::with_capacity(arity + 1);
        prefixes.push(rule_weight);
        for &child_weight in &child_weights {
            prefixes.push(prefixes.last().copied().unwrap() * child_weight);
        }
        let mut suffixes = SmallVec::<[f64; 3]>::from_elem(1.0, arity + 1);
        for index in (0..arity).rev() {
            suffixes[index] = child_weights[index] * suffixes[index + 1];
        }

        let mut successors = Vec::with_capacity(limit);
        for dimension in 0..limit {
            successors.push(TupleCandidate {
                rule: rule_index,
                ranks: CandidateRanks::Bump {
                    base_rank: item_rank,
                    dimension,
                    left_factor: prefixes[dimension],
                    right_factor: suffixes[dimension + 1],
                },
            });
        }
        self.state_streams
            .get_mut(&state)
            .expect("state stream must exist")
            .candidates
            .generated
            .extend(successors);
    }

    fn expand_pending(&mut self, state: StateId) {
        loop {
            let item_rank = self.state_streams[&state].next_unexpanded;
            if item_rank == self.state_streams[&state].known.len() {
                return;
            }
            self.state_streams
                .get_mut(&state)
                .expect("state stream must exist")
                .next_unexpanded += 1;
            self.expand_successors(state, item_rank);
        }
    }

    fn extend_agenda(&mut self, state: StateId, ready: Vec<ScoredCandidate>) {
        let mut heap_items = Vec::with_capacity(ready.len());
        for candidate in ready {
            let seq = self.next_seq;
            self.next_seq += 1;
            heap_items.push(CandidateHeapItem { candidate, seq });
        }

        let agenda = &mut self
            .state_streams
            .get_mut(&state)
            .expect("state stream must exist")
            .agenda;
        if agenda.is_empty() {
            *agenda = BinaryHeap::from(heap_items);
        } else {
            agenda.extend(heap_items);
        }
    }

    fn merge_ready_and_pop(
        &mut self,
        state: StateId,
        mut ready: SmallVec<[ScoredCandidate; 2]>,
    ) -> Option<ScoredCandidate> {
        if ready.len() == 1 && self.state_streams[&state].agenda.is_empty() {
            return ready.pop();
        }

        let mut heap_items = Vec::with_capacity(ready.len());
        for candidate in ready {
            let seq = self.next_seq;
            self.next_seq += 1;
            heap_items.push(CandidateHeapItem { candidate, seq });
        }
        let agenda = &mut self
            .state_streams
            .get_mut(&state)
            .expect("state stream must exist")
            .agenda;
        if agenda.is_empty() {
            *agenda = BinaryHeap::from(heap_items);
        } else {
            agenda.extend(heap_items);
        }
        agenda.pop().map(|entry| entry.candidate)
    }

    fn initialize_root_agenda(&mut self) {
        if self.root_initialized {
            return;
        }
        self.root_initialized = true;

        let mut roots = Vec::with_capacity(self.accepting.len());
        for state in self.accepting.clone() {
            if let Some(weight) = self.state_item_weight(state, 0) {
                let seq = self.next_seq;
                self.next_seq += 1;
                roots.push(RootHeapItem {
                    state,
                    rank: 0,
                    weight,
                    seq,
                });
            }
        }
        self.root_agenda = BinaryHeap::from(roots);
    }

    fn advance_pending_root_stream(&mut self) {
        let Some((state, rank)) = self.pending_root_successor.take() else {
            return;
        };
        if let Some(weight) = self.state_item_weight(state, rank) {
            self.push_root(state, rank, weight);
        }
    }

    fn push_root(&mut self, state: StateId, rank: usize, weight: f64) {
        let seq = self.next_seq;
        self.next_seq += 1;
        self.root_agenda.push(RootHeapItem {
            state,
            rank,
            weight,
            seq,
        });
    }

    fn materialize(&mut self, state: StateId, rank: usize) -> Tree {
        let root_rule = self.state_streams[&state].known[rank].rule;
        let root = self.automaton.rule(root_rule);
        if root.children.is_empty() {
            return self.arena.add_leaf(root.symbol);
        }

        let root_ranks = self.copy_child_ranks(state, rank, root.children.len());
        let cached_children = root
            .children
            .iter()
            .copied()
            .zip(root_ranks)
            .map(|(child_state, child_rank)| {
                self.state_streams[&child_state]
                    .materialized
                    .get(child_rank)
                    .copied()
                    .flatten()
            })
            .collect::<Option<SmallVec<[Tree; 2]>>>();
        if let Some(children) = cached_children {
            return self.arena.add_node_from_slice(root.symbol, &children);
        }

        self.materialize_recursive(state, rank, false, 0)
    }

    fn materialize_recursive(
        &mut self,
        state: StateId,
        rank: usize,
        cache: bool,
        depth: usize,
    ) -> Tree {
        const RECURSION_LIMIT: usize = 1_024;
        if depth == RECURSION_LIMIT {
            return self.materialize_iterative(state, rank, cache);
        }
        if cache
            && let Some(tree) = self.state_streams[&state]
                .materialized
                .get(rank)
                .copied()
                .flatten()
        {
            return tree;
        }

        let item = &self.state_streams[&state].known[rank];
        let rule = self.automaton.rule(item.rule);
        let symbol = rule.symbol;
        let child_ranks = self.copy_child_ranks(state, rank, rule.children.len());
        let children: SmallVec<[(StateId, usize); 2]> =
            rule.children.iter().copied().zip(child_ranks).collect();
        let children: SmallVec<[Tree; 2]> = children
            .into_iter()
            .map(|(child_state, child_rank)| {
                self.materialize_recursive(child_state, child_rank, true, depth + 1)
            })
            .collect();
        let tree = self.arena.add_node_from_slice(symbol, &children);
        if cache {
            let stream = self
                .state_streams
                .get_mut(&state)
                .expect("state stream must exist");
            if stream.materialized.len() <= rank {
                stream.materialized.resize(rank + 1, None);
            }
            stream.materialized[rank] = Some(tree);
        }
        tree
    }

    fn materialize_iterative(&mut self, state: StateId, rank: usize, cache_root: bool) -> Tree {
        let mut frames = vec![MaterializeFrame::Enter {
            state,
            rank,
            cache: cache_root,
        }];
        let mut results = Vec::new();

        while let Some(frame) = frames.pop() {
            match frame {
                MaterializeFrame::Enter { state, rank, cache } => {
                    if cache
                        && let Some(tree) = self.state_streams[&state]
                            .materialized
                            .get(rank)
                            .copied()
                            .flatten()
                    {
                        results.push(tree);
                        continue;
                    }

                    let item = &self.state_streams[&state].known[rank];
                    let rule = self.automaton.rule(item.rule);
                    let child_ranks = self.copy_child_ranks(state, rank, rule.children.len());
                    let children: SmallVec<[(StateId, usize); 2]> =
                        rule.children.iter().copied().zip(child_ranks).collect();
                    frames.push(MaterializeFrame::Exit {
                        state,
                        rank,
                        cache,
                        symbol: rule.symbol,
                        child_count: children.len(),
                    });
                    frames.extend(children.into_iter().rev().map(|(state, rank)| {
                        MaterializeFrame::Enter {
                            state,
                            rank,
                            cache: true,
                        }
                    }));
                }
                MaterializeFrame::Exit {
                    state,
                    rank,
                    cache,
                    symbol,
                    child_count,
                } => {
                    let children_start = results.len() - child_count;
                    let tree = self
                        .arena
                        .add_node_from_slice(symbol, &results[children_start..]);
                    results.truncate(children_start);
                    if cache {
                        let stream = self
                            .state_streams
                            .get_mut(&state)
                            .expect("state stream must exist");
                        if stream.materialized.len() <= rank {
                            stream.materialized.resize(rank + 1, None);
                        }
                        stream.materialized[rank] = Some(tree);
                    }
                    results.push(tree);
                }
            }
        }

        results
            .pop()
            .expect("materialization must produce one root")
    }
}

enum MaterializeFrame {
    Enter {
        state: StateId,
        rank: usize,
        cache: bool,
    },
    Exit {
        state: StateId,
        rank: usize,
        cache: bool,
        symbol: Symbol,
        child_count: usize,
    },
}

impl Iterator for SortedLanguageIterator<'_> {
    type Item = WeightedTree;

    fn next(&mut self) -> Option<Self::Item> {
        self.initialize_root_agenda();
        self.advance_pending_root_stream();

        let best = self.root_agenda.pop()?;
        let tree = self.materialize(best.state, best.rank);
        if !self
            .automaton
            .rule(self.state_streams[&best.state].known[best.rank].rule)
            .children
            .is_empty()
        {
            let stream = self
                .state_streams
                .get_mut(&best.state)
                .expect("state stream must exist");
            if stream.materialized.len() <= best.rank {
                stream.materialized.resize(best.rank + 1, None);
            }
            stream.materialized[best.rank] = Some(tree);
        }
        self.pending_root_successor = Some((best.state, best.rank + 1));
        Some(WeightedTree {
            tree,
            weight: best.weight,
        })
    }
}

#[derive(Clone, Debug)]
struct StateStream {
    known: Vec<StateItem>,
    materialized: Vec<Option<Tree>>,
    agenda: BinaryHeap<CandidateHeapItem>,
    candidates: PendingCandidates,
    next_unexpanded: usize,
}

/// Lazy source of candidates for one state.
///
/// Initial rules stay in the automaton's top-down index and are addressed by a
/// cursor, so touching a deterministic state does not allocate a one-element
/// candidate vector. Only blocked candidates and generated tuple successors
/// require owned storage.
#[derive(Clone, Debug)]
struct PendingCandidates {
    generated: Vec<TupleCandidate>,
    next_rule: usize,
}

impl PendingCandidates {
    fn new(productive: bool, rule_count: usize) -> Self {
        Self {
            generated: Vec::new(),
            next_rule: if productive { 0 } else { rule_count },
        }
    }

    #[inline]
    fn has_unstarted(&self, rule_count: usize) -> bool {
        self.next_rule < rule_count
    }

    #[inline]
    fn is_empty(&self, rule_count: usize) -> bool {
        self.generated.is_empty() && !self.has_unstarted(rule_count)
    }

    fn take_unstarted(&mut self, rule_count: usize) -> std::ops::Range<usize> {
        let range = self.next_rule..rule_count;
        self.next_rule = rule_count;
        range
    }

    fn take(&mut self, rule_count: usize) -> (Vec<TupleCandidate>, std::ops::Range<usize>) {
        (
            mem::take(&mut self.generated),
            self.take_unstarted(rule_count),
        )
    }
}

#[derive(Clone, Debug)]
struct StateItem {
    rule: usize,
    child_ranks: ChildRanks,
    weight: f64,
}

#[derive(Clone, Debug)]
enum ChildRanks {
    Zero,
    Unary(usize),
    Binary { left_rank: usize, right_rank: usize },
    Nary(Box<[usize]>),
}

impl ChildRanks {
    #[inline]
    fn child_rank(&self, dimension: usize) -> usize {
        match self {
            Self::Zero => panic!("leaf has no child rank"),
            Self::Unary(child_rank) => {
                debug_assert_eq!(dimension, 0);
                *child_rank
            }
            Self::Binary {
                left_rank,
                right_rank,
                ..
            } => [*left_rank, *right_rank][dimension],
            Self::Nary(child_ranks) => child_ranks[dimension],
        }
    }

    fn child_ranks(&self) -> SmallVec<[usize; 2]> {
        match self {
            Self::Zero => SmallVec::new(),
            Self::Unary(child_rank) => smallvec::smallvec![*child_rank],
            Self::Binary {
                left_rank,
                right_rank,
                ..
            } => smallvec::smallvec![*left_rank, *right_rank],
            Self::Nary(child_ranks) => SmallVec::from_slice(child_ranks),
        }
    }
}

#[derive(Clone, Debug)]
struct TupleCandidate {
    rule: usize,
    ranks: CandidateRanks,
}

#[derive(Clone, Debug)]
struct ScoredCandidate {
    rule: usize,
    base_rank: usize,
    dimension: usize,
    weight: f64,
}

const ZERO_DIMENSION: usize = usize::MAX;

#[derive(Clone, Debug)]
enum CandidateRanks {
    Zero,
    Bump {
        base_rank: usize,
        dimension: usize,
        left_factor: f64,
        right_factor: f64,
    },
}

#[derive(Clone, Copy, Debug)]
enum EnsureOutcome {
    Available(f64),
    Exhausted,
    Blocked,
}

enum CandidateOutcome {
    Ready(ScoredCandidate),
    Blocked(TupleCandidate),
    Dead,
}

enum SearchFrame {
    Ensure {
        state: StateId,
        rank: usize,
    },
    EvaluateState {
        state: StateId,
        candidates: std::vec::IntoIter<TupleCandidate>,
        leftovers: Vec<TupleCandidate>,
        ready: Vec<ScoredCandidate>,
    },
    ResolveCandidate {
        owner: StateId,
        candidate: TupleCandidate,
        next_child: usize,
        weight: f64,
    },
}

fn canonical_successor_limit(child_ranks: &[usize]) -> usize {
    child_ranks
        .iter()
        .position(|&rank| rank != 0)
        .map_or(child_ranks.len(), |index| index + 1)
}

#[derive(Clone, Debug)]
struct CandidateHeapItem {
    candidate: ScoredCandidate,
    seq: usize,
}

impl PartialEq for CandidateHeapItem {
    fn eq(&self, other: &Self) -> bool {
        self.candidate.weight.total_cmp(&other.candidate.weight) == Ordering::Equal
            && self.seq == other.seq
    }
}

impl Eq for CandidateHeapItem {}

impl PartialOrd for CandidateHeapItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CandidateHeapItem {
    fn cmp(&self, other: &Self) -> Ordering {
        self.candidate
            .weight
            .total_cmp(&other.candidate.weight)
            .then_with(|| other.seq.cmp(&self.seq))
    }
}

#[derive(Clone, Debug)]
struct RootHeapItem {
    state: StateId,
    rank: usize,
    weight: f64,
    seq: usize,
}

impl PartialEq for RootHeapItem {
    fn eq(&self, other: &Self) -> bool {
        self.weight.total_cmp(&other.weight) == Ordering::Equal && self.seq == other.seq
    }
}

impl Eq for RootHeapItem {}

impl PartialOrd for RootHeapItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RootHeapItem {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight
            .total_cmp(&other.weight)
            .then_with(|| other.seq.cmp(&self.seq))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ExplicitBuilder;

    fn assert_weight_sequences_close(actual: &[f64], expected: &[f64]) {
        assert_eq!(actual.len(), expected.len());
        for (index, (&actual, &expected)) in actual.iter().zip(expected).enumerate() {
            let tolerance = 1e-14 * expected.abs().max(1.0);
            assert!(
                (actual - expected).abs() <= tolerance,
                "weight {index} differs: {actual} vs {expected}"
            );
        }
        assert!(actual.windows(2).all(|pair| pair[0] >= pair[1]));
    }

    #[test]
    fn recursively_generated_weights_are_sorted() {
        let mut builder = ExplicitBuilder::new();
        let q = builder.new_state();
        builder.add_weighted_rule(Symbol(0), vec![], q, 0.6);
        builder.add_weighted_rule(Symbol(1), vec![q], q, 0.4);
        builder.add_accepting(q);
        let automaton = builder.build();

        let actual = automaton
            .sorted_language()
            .take(12)
            .map(|tree| tree.weight())
            .collect::<Vec<_>>();
        let expected = (0..12)
            .map(|depth| 0.6 * 0.4_f64.powi(depth))
            .collect::<Vec<_>>();
        assert_weight_sequences_close(&actual, &expected);
    }

    #[test]
    fn branching_recursive_language_is_sorted() {
        let mut builder = ExplicitBuilder::new();
        let root = builder.new_state();
        let unary = builder.new_state();
        let binary = builder.new_state();
        builder.add_weighted_rule(Symbol(0), vec![unary, binary], root, 1.0);
        builder.add_weighted_rule(Symbol(1), vec![], unary, 1.0);
        builder.add_weighted_rule(Symbol(2), vec![unary], unary, 0.2);
        builder.add_weighted_rule(Symbol(3), vec![binary, binary], binary, 0.7);
        builder.add_weighted_rule(Symbol(4), vec![], binary, 0.3);
        builder.add_accepting(root);
        let automaton = builder.build();

        let weights = automaton
            .sorted_language()
            .take(40)
            .map(|tree| tree.weight())
            .collect::<Vec<_>>();
        assert_eq!(weights.len(), 40);
        assert!((weights[0] - 0.3).abs() < 1e-14);
        assert!((weights[1] - 0.063).abs() < 1e-14);
        assert!(weights.windows(2).all(|pair| pair[0] >= pair[1]));
    }

    #[test]
    fn canonical_successor_limit_gives_each_grid_tuple_one_predecessor() {
        assert_eq!(canonical_successor_limit(&[0, 0]), 2);
        assert_eq!(canonical_successor_limit(&[1, 0]), 1);
        assert_eq!(canonical_successor_limit(&[0, 1]), 2);
        assert_eq!(canonical_successor_limit(&[0, 0, 2, 0]), 3);
    }

    #[test]
    fn high_arity_successors_handle_zero_weights_without_division() {
        let mut builder = ExplicitBuilder::new();
        let child = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(Symbol(0), vec![], child, 1.0);
        builder.add_weighted_rule(Symbol(1), vec![], child, 0.0);
        builder.add_weighted_rule(Symbol(2), vec![child; 32], root, 0.7);
        builder.add_accepting(root);
        let automaton = builder.build();

        let weights = automaton
            .sorted_language()
            .take(40)
            .map(|tree| tree.weight())
            .collect::<Vec<_>>();
        assert_eq!(weights.len(), 40);
        assert!((weights[0] - 0.7).abs() < 1e-14);
        assert!(weights[1..].iter().all(|weight| *weight == 0.0));
    }

    #[test]
    fn deeply_nested_first_tree_does_not_use_the_process_stack() {
        let mut builder = ExplicitBuilder::new();
        let mut state = builder.new_state();
        builder.add_weighted_rule(Symbol(0), vec![], state, 0.999);
        for symbol in 1..=20_000 {
            let parent = builder.new_state();
            builder.add_weighted_rule(Symbol(symbol), vec![state], parent, 0.999);
            state = parent;
        }
        builder.add_accepting(state);
        let automaton = builder.build();
        assert!(automaton.sorted_language().next().is_some());
    }
}
