//! Lazy k-best language iteration for explicit weighted tree automata.

use crate::{Explicit, FxHashSet, StateId, Symbol, TopDownTa};
use fixedbitset::FixedBitSet;
use packed_term_arena::tree::{Tree, TreeArena};
use std::{cmp::Ordering, collections::BinaryHeap, mem};

/// A weighted tree generated from an automaton language.
///
/// The tree root refers to the arena owned by the
/// [`SortedLanguageIterator`] that produced it. This is intentionally a lean
/// handle: advancing the iterator may invalidate previously returned tree
/// handles in future implementations. Clone a tree out through
/// [`SortedLanguageIterator::clone_tree`] before advancing if it must be kept.
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

    /// Return the tree weight.
    pub fn weight(&self) -> f64 {
        self.weight
    }
}

/// Lazily enumerates trees accepted by an [`Explicit`] automaton in descending
/// weight order.
///
/// This is the Rust port of Alto's sorted language iterator. It keeps one
/// stream per state and one stream per top-down rule. Rule streams contain
/// unevaluated child-rank tuples and only ask child streams for their k-best
/// trees when the tuple is needed. Recursive states are guarded by a
/// per-expansion visiting set, so productive recursive languages can be
/// enumerated without eagerly materializing the language.
///
/// The ordering assumes the usual k-best monotonicity condition: combining a
/// rule with lower-ranked child trees must not increase the item score. For
/// the built-in evaluator this is the natural condition for non-negative
/// multiplicative weights on productive automata.
pub struct SortedLanguageIterator<'a> {
    accepting: Vec<StateId>,
    state_streams: Vec<Option<StateStream>>,
    rule_streams: Vec<RuleStream>,
    arena: TreeArena<Symbol>,
    visiting: FixedBitSet,
    _automaton: &'a Explicit,
}

impl Explicit {
    /// Iterate over accepted trees in descending rule-weight product order.
    pub fn sorted_language(&self) -> SortedLanguageIterator<'_> {
        SortedLanguageIterator::new(self)
    }
}

impl<'a> SortedLanguageIterator<'a> {
    /// Create a lazy sorted language iterator for an explicit automaton.
    pub fn new(automaton: &'a Explicit) -> Self {
        let mut accepting = Vec::new();
        automaton.initial_states(&mut |q| accepting.push(q));

        let mut state_streams = Vec::with_capacity(automaton.num_states() as usize);
        state_streams.resize_with(automaton.num_states() as usize, || None);

        Self {
            accepting,
            state_streams,
            rule_streams: Vec::new(),
            arena: TreeArena::new(),
            visiting: FixedBitSet::with_capacity(automaton.num_states() as usize),
            _automaton: automaton,
        }
    }

    /// Return the arena that contains trees produced by this iterator.
    ///
    /// [`WeightedTree::tree`] values returned by this iterator are roots in
    /// this arena. The arena is owned by the iterator so generated subtrees can
    /// be reused without reference counting or copying.
    pub fn arena(&self) -> &TreeArena<Symbol> {
        &self.arena
    }

    /// Clone a generated tree into a fresh arena.
    ///
    /// Use this before advancing the iterator if the tree must be retained
    /// independently of the iterator.
    pub fn clone_tree(&self, root: Tree) -> (TreeArena<Symbol>, Tree) {
        let mut target = TreeArena::new();
        let root = self.arena.copy_into(root, &mut target);
        (target, root)
    }

    fn ensure_state_stream(&mut self, state: StateId) {
        let idx = state.index();
        if self.state_streams[idx].is_some() {
            return;
        }

        let mut rule_streams = Vec::new();
        for rule in self._automaton.rules_topdown(state) {
            let stream_idx = self.rule_streams.len();
            self.rule_streams.push(RuleStream::new(rule.into()));
            rule_streams.push(stream_idx);
        }

        self.state_streams[idx] = Some(StateStream {
            known: Vec::new(),
            rule_streams,
            next_item: 0,
        });
    }

    fn state_stream(&self, state: StateId) -> &StateStream {
        self.state_streams[state.index()]
            .as_ref()
            .expect("state stream must be initialized")
    }

    fn state_stream_mut(&mut self, state: StateId) -> &mut StateStream {
        self.state_streams[state.index()]
            .as_mut()
            .expect("state stream must be initialized")
    }

    fn state_item(&mut self, state: StateId, k: usize) -> Option<EvaluatedItem> {
        self.ensure_state_stream(state);

        if let Some(item) = self.state_stream(state).known.get(k) {
            return Some(item.clone());
        }

        if k != self.state_stream(state).known.len() || self.visiting.contains(state.index()) {
            return None;
        }

        self.visiting.set(state.index(), true);
        let best_stream = self.best_rule_stream_for_state(state);
        let best = best_stream.and_then(|stream| self.rule_pop(stream));
        self.visiting.set(state.index(), false);

        if let Some(item) = best {
            self.state_stream_mut(state).known.push(item.clone());
            Some(item)
        } else {
            None
        }
    }

    fn state_pop_next(&mut self, state: StateId) -> Option<EvaluatedItem> {
        self.ensure_state_stream(state);
        let next = self.state_stream(state).next_item;
        let item = self.state_item(state, next)?;
        self.state_stream_mut(state).next_item += 1;
        Some(item)
    }

    fn state_is_finished(&mut self, state: StateId) -> bool {
        self.ensure_state_stream(state);
        if self.visiting.contains(state.index()) {
            return false;
        }
        let streams = self.state_stream(state).rule_streams.clone();
        streams
            .into_iter()
            .all(|stream| self.rule_is_finished(stream))
    }

    fn best_rule_stream_for_state(&mut self, state: StateId) -> Option<usize> {
        let streams = self.state_stream(state).rule_streams.clone();
        streams
            .into_iter()
            .filter_map(|stream| self.rule_peek_weight(stream).map(|weight| (stream, weight)))
            .max_by(|a, b| compare_weight(a.1, b.1))
            .map(|(stream, _)| stream)
    }

    fn rule_peek_weight(&mut self, stream: usize) -> Option<f64> {
        self.evaluate_unevaluated(stream);
        self.rule_streams[stream]
            .evaluated
            .peek()
            .map(|entry| entry.item.item_weight)
    }

    fn rule_pop(&mut self, stream: usize) -> Option<EvaluatedItem> {
        self.evaluate_unevaluated(stream);
        let item = self.rule_streams[stream].evaluated.pop()?.item;
        let popped_tuple = item.item.clone();
        let tree = self.arena.add_node(item.symbol, item.children);
        let evaluated = EvaluatedItem {
            tree,
            tree_weight: item.tree_weight,
            item_weight: item.item_weight,
        };
        self.rule_streams[stream]
            .pending_variations
            .push(popped_tuple);
        Some(evaluated)
    }

    fn rule_is_finished(&mut self, stream: usize) -> bool {
        self.evaluate_unevaluated(stream);
        self.rule_streams[stream].evaluated.is_empty()
            && self.rule_streams[stream].unevaluated.is_empty()
    }

    fn evaluate_unevaluated(&mut self, stream: usize) {
        self.expand_pending_variations(stream);
        let items = mem::take(&mut self.rule_streams[stream].unevaluated);
        if items.is_empty() {
            return;
        }

        let rule = self.rule_streams[stream].rule.clone();
        let mut leftovers = Vec::new();
        let mut evaluated = Vec::new();

        for item in items {
            if item.rule_position > 0 {
                continue;
            }

            let mut children = Vec::with_capacity(rule.children.len());
            let mut child_weight = 1.0;
            let mut available = true;
            let mut keep = true;

            for (&child_state, &rank) in rule.children.iter().zip(&item.child_positions) {
                if let Some(child_item) = self.state_item(child_state, rank) {
                    child_weight *= child_item.tree_weight;
                    children.push(child_item.tree);
                } else {
                    available = false;
                    if self.state_is_finished(child_state) {
                        keep = false;
                    }
                    break;
                }
            }

            if available {
                let tree_weight = rule.weight * child_weight;
                let eval = ScoredItem {
                    item,
                    symbol: rule.symbol,
                    children,
                    tree_weight,
                    item_weight: tree_weight,
                };
                evaluated.push(eval);
            } else if keep {
                leftovers.push(item);
            }
        }

        let rule_stream = &mut self.rule_streams[stream];
        rule_stream.unevaluated.extend(leftovers);
        for item in evaluated {
            let seq = rule_stream.next_seq;
            rule_stream.next_seq += 1;
            rule_stream.evaluated.push(HeapItem { item, seq });
        }
    }

    fn expand_pending_variations(&mut self, stream: usize) {
        let pending = mem::take(&mut self.rule_streams[stream].pending_variations);
        if pending.is_empty() {
            return;
        }

        let rule_stream = &mut self.rule_streams[stream];
        for item in pending {
            for variation in item.variations() {
                if rule_stream.discovered.insert(variation.clone()) {
                    rule_stream.unevaluated.push(variation);
                }
            }
        }
    }
}

impl Iterator for SortedLanguageIterator<'_> {
    type Item = WeightedTree;

    fn next(&mut self) -> Option<Self::Item> {
        let best_state = self
            .accepting
            .clone()
            .into_iter()
            .filter_map(|state| {
                self.ensure_state_stream(state);
                let next = self.state_stream(state).next_item;
                self.state_item(state, next)
                    .map(|item| (state, item.item_weight))
            })
            .max_by(|a, b| compare_weight(a.1, b.1))
            .map(|(state, _)| state)?;

        let item = self.state_pop_next(best_state)?;
        Some(WeightedTree {
            tree: item.tree,
            weight: item.tree_weight,
        })
    }
}

#[derive(Clone, Debug)]
struct OwnedRule {
    symbol: Symbol,
    children: Vec<StateId>,
    weight: f64,
}

impl From<crate::Rule<'_>> for OwnedRule {
    fn from(rule: crate::Rule<'_>) -> Self {
        Self {
            symbol: rule.symbol,
            children: rule.children.to_vec(),
            weight: rule.weight,
        }
    }
}

#[derive(Clone, Debug)]
struct StateStream {
    known: Vec<EvaluatedItem>,
    rule_streams: Vec<usize>,
    next_item: usize,
}

#[derive(Clone, Debug)]
struct RuleStream {
    rule: OwnedRule,
    evaluated: BinaryHeap<HeapItem>,
    unevaluated: Vec<UnevaluatedItem>,
    pending_variations: Vec<UnevaluatedItem>,
    discovered: FxHashSet<UnevaluatedItem>,
    next_seq: usize,
}

impl RuleStream {
    fn new(rule: OwnedRule) -> Self {
        let zero = UnevaluatedItem {
            rule_position: 0,
            child_positions: vec![0; rule.children.len()],
        };
        let mut discovered = FxHashSet::default();
        discovered.insert(zero.clone());

        Self {
            rule,
            evaluated: BinaryHeap::new(),
            unevaluated: vec![zero],
            pending_variations: Vec::new(),
            discovered,
            next_seq: 0,
        }
    }
}

#[derive(Clone, Debug)]
struct EvaluatedItem {
    tree: Tree,
    tree_weight: f64,
    item_weight: f64,
}

#[derive(Clone, Debug)]
struct ScoredItem {
    item: UnevaluatedItem,
    symbol: Symbol,
    children: Vec<Tree>,
    tree_weight: f64,
    item_weight: f64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct UnevaluatedItem {
    rule_position: usize,
    child_positions: Vec<usize>,
}

impl UnevaluatedItem {
    fn variations(&self) -> impl Iterator<Item = UnevaluatedItem> + '_ {
        (0..=self.child_positions.len()).map(|pos| {
            let mut item = self.clone();
            if pos == 0 {
                item.rule_position += 1;
            } else {
                item.child_positions[pos - 1] += 1;
            }
            item
        })
    }
}

#[derive(Clone, Debug)]
struct HeapItem {
    item: ScoredItem,
    seq: usize,
}

impl PartialEq for HeapItem {
    fn eq(&self, other: &Self) -> bool {
        self.item.item_weight.total_cmp(&other.item.item_weight) == Ordering::Equal
            && self.seq == other.seq
    }
}

impl Eq for HeapItem {}

impl PartialOrd for HeapItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for HeapItem {
    fn cmp(&self, other: &Self) -> Ordering {
        compare_weight(self.item.item_weight, other.item.item_weight)
            .then_with(|| other.seq.cmp(&self.seq))
    }
}

fn compare_weight(left: f64, right: f64) -> Ordering {
    left.total_cmp(&right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, Signature};

    fn symbols(names: &[(&str, usize)]) -> Signature {
        let mut sig = Signature::new();
        for &(name, arity) in names {
            sig.intern(name.to_owned(), arity).unwrap();
        }
        sig
    }

    fn show(arena: &TreeArena<Symbol>, tree: WeightedTree, signature: &Signature) -> String {
        fn rec(arena: &TreeArena<Symbol>, node: Tree, signature: &Signature, out: &mut String) {
            out.push_str(signature.resolve(*arena.get_label(node)));
            if !arena.get_children(node).is_empty() {
                out.push('(');
                for (idx, &child) in arena.get_children(node).iter().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    rec(arena, child, signature, out);
                }
                out.push(')');
            }
        }

        let mut out = String::new();
        rec(arena, tree.tree(), signature, &mut out);
        out
    }

    #[test]
    fn enumerates_nonrecursive_language_by_descending_weight() {
        let sig = symbols(&[("b", 0), ("f", 1), ("g", 1)]);
        let b = sig.get("b").unwrap();
        let f = sig.get("f").unwrap();
        let g = sig.get("g").unwrap();

        let mut builder = ExplicitBuilder::new();
        let qb = builder.new_state();
        let qa = builder.new_state();
        builder.add_weighted_rule(b, vec![], qb, 0.5);
        builder.add_weighted_rule(f, vec![qb], qa, 0.7);
        builder.add_weighted_rule(g, vec![qb], qa, 0.3);
        builder.add_accepting(qa);
        let automaton = builder.build();

        let mut it = automaton.sorted_language();
        let first = it.next().unwrap();
        assert_eq!(show(it.arena(), first, &sig), "f(b)");
        assert_eq!(first.weight(), 0.35);

        let second = it.next().unwrap();
        assert_eq!(show(it.arena(), second, &sig), "g(b)");
        assert_eq!(second.weight(), 0.15);

        assert!(it.next().is_none());
    }

    #[test]
    fn handles_recursive_productive_language_lazily() {
        let sig = symbols(&[("b", 0), ("f", 1)]);
        let b = sig.get("b").unwrap();
        let f = sig.get("f").unwrap();

        let mut builder = ExplicitBuilder::new();
        let q = builder.new_state();
        builder.add_weighted_rule(b, vec![], q, 0.5);
        builder.add_weighted_rule(f, vec![q], q, 0.5);
        builder.add_accepting(q);
        let automaton = builder.build();

        let mut it = automaton.sorted_language();
        let first = it.next().unwrap();
        let second = it.next().unwrap();
        let third = it.next().unwrap();

        assert_eq!(show(it.arena(), first, &sig), "b");
        assert_eq!(first.weight(), 0.5);
        assert_eq!(show(it.arena(), second, &sig), "f(b)");
        assert_eq!(second.weight(), 0.25);
        assert_eq!(show(it.arena(), third, &sig), "f(f(b))");
        assert_eq!(third.weight(), 0.125);
    }

    #[test]
    fn merges_multiple_accepting_state_streams() {
        let sig = symbols(&[("b", 0), ("f", 1), ("g", 1)]);
        let b = sig.get("b").unwrap();
        let f = sig.get("f").unwrap();
        let g = sig.get("g").unwrap();

        let mut builder = ExplicitBuilder::new();
        let qb = builder.new_state();
        let qa = builder.new_state();
        builder.add_weighted_rule(b, vec![], qb, 0.5);
        builder.add_weighted_rule(f, vec![qb], qb, 0.5);
        builder.add_weighted_rule(g, vec![qb], qa, 0.4);
        builder.add_accepting(qb);
        builder.add_accepting(qa);
        let automaton = builder.build();

        let mut it = automaton.sorted_language();
        let mut got = Vec::new();
        for _ in 0..5 {
            let tree = it.next().unwrap();
            got.push((show(it.arena(), tree, &sig), tree.weight()));
        }

        assert_eq!(
            got,
            vec![
                ("b".to_owned(), 0.5),
                ("f(b)".to_owned(), 0.25),
                ("g(b)".to_owned(), 0.2),
                ("f(f(b))".to_owned(), 0.125),
                ("g(f(b))".to_owned(), 0.1),
            ]
        );
    }

    #[test]
    fn empty_language_yields_no_items() {
        let sig = symbols(&[("g", 2)]);
        let g = sig.get("g").unwrap();

        let mut builder = ExplicitBuilder::new();
        let q = builder.new_state();
        let q1 = builder.new_state();
        let q2 = builder.new_state();
        builder.add_weighted_rule(g, vec![q1, q2], q, 1.0);
        builder.add_accepting(q);
        let automaton = builder.build();

        assert!(automaton.sorted_language().next().is_none());
    }

    #[test]
    fn clones_weighted_tree_to_independent_arena() {
        let sig = symbols(&[("b", 0), ("f", 1)]);
        let b = sig.get("b").unwrap();
        let f = sig.get("f").unwrap();

        let mut builder = ExplicitBuilder::new();
        let qb = builder.new_state();
        let qa = builder.new_state();
        builder.add_rule(b, vec![], qb);
        builder.add_rule(f, vec![qb], qa);
        builder.add_accepting(qa);
        let automaton = builder.build();

        let mut it = automaton.sorted_language();
        let tree = it.next().unwrap();
        let (arena, root) = it.clone_tree(tree.tree());
        assert_eq!(arena.get_label(root), &f);
        let child = arena.get_children(root)[0];
        assert_eq!(arena.get_label(child), &b);
    }

    #[test]
    fn mirrors_alto_gontrum_recursive_regression() {
        let sig = symbols(&[("r1", 2), ("r2", 0), ("r3", 1), ("r4", 2), ("r5", 0)]);
        let r1 = sig.get("r1").unwrap();
        let r2 = sig.get("r2").unwrap();
        let r3 = sig.get("r3").unwrap();
        let r4 = sig.get("r4").unwrap();
        let r5 = sig.get("r5").unwrap();

        let mut builder = ExplicitBuilder::new();
        let s = builder.new_state();
        let a = builder.new_state();
        let b = builder.new_state();
        builder.add_weighted_rule(r1, vec![a, b], s, 1.0);
        builder.add_weighted_rule(r2, vec![], a, 1.0);
        builder.add_weighted_rule(r3, vec![a], a, 0.0);
        builder.add_weighted_rule(r4, vec![b, b], b, 0.7);
        builder.add_weighted_rule(r5, vec![], b, 0.3);
        builder.add_accepting(s);
        let automaton = builder.build();

        let mut it = automaton.sorted_language();
        let first = it.next().unwrap();
        assert_eq!(show(it.arena(), first, &sig), "r1(r2,r5)");
        let second = it.next().unwrap();
        assert_eq!(show(it.arena(), second, &sig), "r1(r2,r4(r5,r5))");
    }
}
