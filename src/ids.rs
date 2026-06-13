use std::fmt;

/// Dense integer identifier for an automaton state.
///
/// `StateId` is the fast state representation used by [`crate::Explicit`],
/// [`crate::Memo`], and deterministic runners. IDs are dense, starting at zero,
/// so they can be used to index vectors and bitsets.
///
/// Most users should create states with [`crate::ExplicitBuilder::new_state`]
/// or [`crate::Interner::intern`] rather than constructing `StateId` directly.
/// The one special value is [`StateId::STUCK`], which is reserved for rejected
/// subtrees and must not be used as an ordinary state.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct StateId(pub u32);

impl StateId {
    /// Sentinel meaning "this subtree has no valid state".
    ///
    /// Deterministic runs store this value in their side table when a node is
    /// rejected. Builders and interners never allocate it as a real state.
    pub const STUCK: StateId = StateId(u32::MAX);

    /// Convert this state ID to a vector or bitset index.
    ///
    /// Do not call this on [`StateId::STUCK`] unless the surrounding code has
    /// explicitly chosen to handle the sentinel as `usize::MAX`.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Return whether this ID is the stuck sentinel.
    pub fn is_stuck(self) -> bool {
        self == Self::STUCK
    }
}

impl fmt::Debug for StateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_stuck() {
            f.write_str("StateId::STUCK")
        } else {
            f.debug_tuple("StateId").field(&self.0).finish()
        }
    }
}

/// Identifier for a node label or grammar symbol.
///
/// The library deliberately does not intern or interpret symbols. Your
/// application owns the signature and maps labels such as `"a"` or `"concat"`
/// to `Symbol` values.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct Symbol(pub u32);

/// Number of children a symbol expects.
///
/// `Arity` appears mainly in [`crate::materialize()`], where the caller provides
/// the finite alphabet to explore.
pub type Arity = u8;
