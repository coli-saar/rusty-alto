use crate::{BottomUpTa, DetBottomUpTa, StateId, Symbol};
use fixedbitset::FixedBitSet;
use packed_term_arena::tree::{Tree, TreeArena};
use smallvec::SmallVec;

/// Side table produced by [`run_det`].
///
/// The table stores one state per arena node. Rejected nodes receive
/// [`StateId::STUCK`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DetRun {
    /// State assigned to each node, indexed by [`Tree::index`].
    pub states: Vec<StateId>,
    /// State assigned to the root, or [`StateId::STUCK`] if the tree rejected.
    pub root_state: StateId,
}

/// Small sorted set of states used by nondeterministic runs.
///
/// The set keeps states deduplicated. It stores a few states inline, which is
/// efficient for the common case where each node has only a small number of
/// possible states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateSet<S>(SmallVec<[S; 4]>);

impl<S> Default for StateSet<S> {
    fn default() -> Self {
        Self(SmallVec::new())
    }
}

impl<S: Clone + Ord> StateSet<S> {
    /// Create an empty state set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a state, preserving sorted and deduplicated order.
    pub fn insert(&mut self, s: S) {
        match self.0.binary_search(&s) {
            Ok(_) => {}
            Err(idx) => self.0.insert(idx, s),
        }
    }

    /// Iterate over states in sorted order.
    pub fn iter(&self) -> impl Iterator<Item = &S> {
        self.0.iter()
    }

    /// Return the states as a slice.
    pub fn as_slice(&self) -> &[S] {
        &self.0
    }

    /// Return whether this set contains no states.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Return the number of states in the set.
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

/// Side table produced by [`run_nondet`].
///
/// Each node can have zero or more possible states. An empty set means the
/// subtree rooted at that node is rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonDetRun<S> {
    /// State set assigned to each node, indexed by [`Tree::index`].
    pub states: Vec<StateSet<S>>,
    /// State set assigned to the root.
    pub root_states: StateSet<S>,
}

/// Run a deterministic automaton over an arena tree.
///
/// This is the fastest runner. It requires automata whose states are
/// [`StateId`] and that implement [`DetBottomUpTa`]. For implicit automata with
/// richer state values, wrap the automaton in [`crate::Memo`] first.
///
/// If a child is stuck, the parent is stuck without querying the automaton.
pub fn run_det<A>(a: &A, arena: &TreeArena<Symbol>, root: Tree) -> DetRun
where
    A: DetBottomUpTa<State = StateId>,
{
    let mut states = vec![StateId::STUCK; arena.len()];
    let mut visited = FixedBitSet::with_capacity(arena.len());
    let mut buf: SmallVec<[StateId; 4]> = SmallVec::new();

    for node in arena.post_order(root) {
        if visited.contains(node.index()) {
            continue;
        }
        visited.set(node.index(), true);

        buf.clear();
        let mut any_stuck = false;
        for &child in arena.get_children(node) {
            let cs = states[child.index()];
            if cs.is_stuck() {
                any_stuck = true;
                break;
            }
            buf.push(cs);
        }
        if any_stuck {
            continue;
        }
        states[node.index()] = a
            .step_det(*arena.get_label(node), &buf)
            .unwrap_or(StateId::STUCK);
    }

    DetRun {
        root_state: states[root.index()],
        states,
    }
}

/// Run a nondeterministic automaton over an arena tree.
///
/// This runner stores a set of possible states at every node. It is more
/// general than [`run_det`] but does more allocation and tuple enumeration, so
/// deterministic automata should prefer [`run_det`] when possible.
pub fn run_nondet<A>(a: &A, arena: &TreeArena<Symbol>, root: Tree) -> NonDetRun<A::State>
where
    A: BottomUpTa,
    A::State: Ord,
{
    let mut states = vec![StateSet::new(); arena.len()];
    let mut visited = FixedBitSet::with_capacity(arena.len());

    for node in arena.post_order(root) {
        if visited.contains(node.index()) {
            continue;
        }
        visited.set(node.index(), true);

        let local = {
            let child_ids: SmallVec<[Tree; 4]> = arena.get_children(node).iter().copied().collect();
            let mut pools: SmallVec<[&[A::State]; 4]> = SmallVec::new();
            let mut any_empty = false;
            for child in child_ids {
                let set = &states[child.index()];
                if set.is_empty() {
                    any_empty = true;
                    break;
                }
                pools.push(set.as_slice());
            }
            if any_empty {
                None
            } else {
                let mut local = StateSet::new();
                cartesian_product(&pools, |tuple| {
                    a.step(*arena.get_label(node), tuple, &mut |q| local.insert(q));
                });
                Some(local)
            }
        };

        if let Some(local) = local {
            states[node.index()] = local;
        }
    }

    NonDetRun {
        root_states: states[root.index()].clone(),
        states,
    }
}

pub(crate) fn cartesian_product<T: Clone>(pools: &[&[T]], mut f: impl FnMut(&[T])) {
    if pools.iter().any(|pool| pool.is_empty()) {
        return;
    }
    if pools.is_empty() {
        f(&[]);
        return;
    }

    let mut indices = vec![0; pools.len()];
    let mut tuple: Vec<T> = pools.iter().map(|pool| pool[0].clone()).collect();

    loop {
        f(&tuple);

        let mut pos = pools.len();
        loop {
            if pos == 0 {
                return;
            }
            pos -= 1;
            indices[pos] += 1;
            if indices[pos] < pools[pos].len() {
                tuple[pos] = pools[pos][indices[pos]].clone();
                for reset in pos + 1..pools.len() {
                    indices[reset] = 0;
                    tuple[reset] = pools[reset][0].clone();
                }
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExplicitBuilder, Symbol};

    #[test]
    fn cartesian_empty_pools_is_unit() {
        let mut tuples = Vec::<Vec<u8>>::new();
        cartesian_product::<u8>(&[], |tuple| tuples.push(tuple.to_vec()));
        assert_eq!(tuples, vec![vec![]]);
    }

    #[test]
    fn cartesian_empty_member_is_empty() {
        let a = [1, 2];
        let b: [i32; 0] = [];
        let mut count = 0;
        cartesian_product(&[&a[..], &b[..]], |_| count += 1);
        assert_eq!(count, 0);
    }

    #[test]
    fn deterministic_run_accepts_tree() {
        let a = Symbol(0);
        let f = Symbol(1);
        let mut builder = ExplicitBuilder::new();
        let leaf = builder.new_state();
        let root_state = builder.new_state();
        builder.add_rule(a, vec![], leaf);
        builder.add_rule(f, vec![leaf, leaf], root_state);
        builder.add_accepting(root_state);
        let automaton = builder.build();

        let mut arena = TreeArena::new();
        let left = arena.add_node(a, vec![]);
        let right = arena.add_node(a, vec![]);
        let root = arena.add_node(f, vec![left, right]);

        let run = run_det(&automaton, &arena, root);
        assert_eq!(run.root_state, root_state);
        assert!(automaton.is_accepting(&run.root_state));
    }

    #[test]
    fn nondeterministic_run_collects_states() {
        let a = Symbol(0);
        let mut builder = ExplicitBuilder::new();
        let q0 = builder.new_state();
        let q1 = builder.new_state();
        builder.add_rule(a, vec![], q0);
        builder.add_rule(a, vec![], q1);
        let automaton = builder.build();
        let mut arena = TreeArena::new();
        let root = arena.add_node(a, vec![]);
        let run = run_nondet(&automaton, &arena, root);
        assert_eq!(run.root_states.len(), 2);
    }

    #[test]
    fn deterministic_run_handles_shared_stuck_nodes() {
        let leaf_symbol = Symbol(0);
        let parent_symbol = Symbol(1);
        let builder = ExplicitBuilder::new();
        let automaton = builder.build();

        let mut arena = TreeArena::new();
        let shared = arena.add_node(leaf_symbol, vec![]);
        let root = arena.add_node(parent_symbol, vec![shared, shared]);

        let run = run_det(&automaton, &arena, root);
        assert!(run.states[shared.index()].is_stuck());
        assert!(run.root_state.is_stuck());
    }
}
