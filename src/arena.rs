use crate::Symbol;
use std::hash::Hash;

/// Identifier for a node in an application-owned tree arena.
///
/// The automata library does not store trees itself. Instead, runners ask your
/// arena for symbols, children, and post-order traversal. Node IDs should be
/// cheap to copy and should map to dense indexes for side tables.
pub trait NodeId: Copy + Eq + Hash {
    /// Return this node's dense index in `[0, arena.len())`.
    ///
    /// Runners use this to index side tables. Returning sparse or out-of-range
    /// values will cause panics or wasted memory.
    fn index(self) -> usize;
}

/// Tree arena interface used by [`crate::run_det`] and [`crate::run_nondet`].
///
/// Implement this trait for your existing tree storage. The only traversal
/// requirement is post-order: children must appear before their parent so that
/// bottom-up states are available when the parent is processed.
pub trait Arena {
    /// Node identifier type used by this arena.
    type NodeId: NodeId;
    /// Iterator over a node's children in semantic child order.
    type Children<'a>: Iterator<Item = Self::NodeId> + 'a
    where
        Self: 'a;
    /// Iterator that visits descendants before their parent.
    type PostOrder<'a>: Iterator<Item = Self::NodeId> + 'a
    where
        Self: 'a;

    /// Return the total number of nodes in the arena.
    ///
    /// Runners allocate side tables of this length.
    fn len(&self) -> usize;

    /// Return whether the arena contains no nodes.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the symbol stored on a node.
    ///
    /// Symbols are application-defined. The automaton and arena must agree on
    /// what each [`Symbol`] means.
    fn symbol(&self, n: Self::NodeId) -> Symbol;

    /// Return the children of a node in left-to-right order.
    fn children(&self, n: Self::NodeId) -> Self::Children<'_>;

    /// Return a post-order traversal of the subtree rooted at `root`.
    ///
    /// For DAG-like arenas with shared nodes, the iterator may visit a shared
    /// node more than once. The runners keep a visited bitset and will reuse
    /// the first computed state.
    fn post_order(&self, root: Self::NodeId) -> Self::PostOrder<'_>;
}

/// Node identifier used by [`TestArena`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TestNode(pub usize);

impl NodeId for TestNode {
    fn index(self) -> usize {
        self.0
    }
}

/// Small in-memory arena for tests, examples, and documentation.
///
/// `TestArena` is intentionally simple. It is useful for trying the library
/// without implementing [`Arena`] for your own tree type first.
#[derive(Clone, Debug, Default)]
pub struct TestArena {
    nodes: Vec<(Symbol, Vec<TestNode>)>,
}

impl TestArena {
    /// Create an empty test arena.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a node with a symbol and child list, returning its ID.
    ///
    /// Children must already have been added to the arena.
    pub fn add_node(&mut self, symbol: Symbol, children: Vec<TestNode>) -> TestNode {
        let id = TestNode(self.nodes.len());
        self.nodes.push((symbol, children));
        id
    }

    fn post_order_rec(&self, node: TestNode, out: &mut Vec<TestNode>) {
        for &child in &self.nodes[node.index()].1 {
            self.post_order_rec(child, out);
        }
        out.push(node);
    }
}

impl Arena for TestArena {
    type NodeId = TestNode;
    type Children<'a> = std::iter::Copied<std::slice::Iter<'a, TestNode>>;
    type PostOrder<'a> = std::vec::IntoIter<TestNode>;

    fn len(&self) -> usize {
        self.nodes.len()
    }

    fn symbol(&self, n: Self::NodeId) -> Symbol {
        self.nodes[n.index()].0
    }

    fn children(&self, n: Self::NodeId) -> Self::Children<'_> {
        self.nodes[n.index()].1.iter().copied()
    }

    fn post_order(&self, root: Self::NodeId) -> Self::PostOrder<'_> {
        let mut nodes = Vec::new();
        self.post_order_rec(root, &mut nodes);
        nodes.into_iter()
    }
}
