use crate::StateId;
use smallvec::SmallVec;

/// Compact backpointer payload for the best pending derivation of a product.
pub(super) struct PendingEdge {
    pub(super) rule_index: u32,
    pub(super) children: SmallVec<[StateId; 2]>,
}

/// Payload stored outside the indexed agenda, one slot per product state.
pub(super) struct AgendaItem {
    pub(super) edge: PendingEdge,
}

/// Product data transferred from storage to the candidate source on finalization.
pub(super) struct FinalizedItem {
    pub(super) product: StateId,
    pub(super) edge: PendingEdge,
    pub(super) inside: f64,
    pub(super) merit: f64,
    pub(super) left_state: StateId,
    pub(super) right_state: StateId,
    pub(super) is_goal: bool,
}
