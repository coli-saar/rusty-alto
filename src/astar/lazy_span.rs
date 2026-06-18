//! Lazy candidate generation for the deterministic binary string-span A* path
//! (perf item N10), `Θ(n³ log n)` heap-successor variant.
//!
//! The eager span path, on each finalized product, immediately enumerates every
//! `siblings × rules` combination, resolves each parent product id, and offers it
//! to the per-product agenda. Most of those candidates are dominated or belong to
//! products that never finalize before the goal, yet each still pays a product-id
//! hash and a sift on the large parent agenda.
//!
//! The lazy frontier keeps the eager combination rule unchanged — the
//! later-finalized child is the trigger, combined with already-finalized siblings
//! recorded in the shared [`SpanProductSiblingFinder`] — but defers
//! *realization*. When a product finalizes it spawns one [`SpanGenerator`] per
//! `(position, sibling-left group)`. Each generator computes its candidates'
//! merits once and stores them in a **binary heap ordered by merit**, so its
//! next-best is a heap pop in `O(log siblings)` rather than a rescan in
//! `O(siblings)` — the difference between `Θ(n³ log n)` and `Θ(n⁴)` over the
//! chart (see `docs/n10-asymptotics.md`). Only when a generator is popped (its
//! best beats the parent agenda's best realized edge) does it resolve product ids
//! and push that sibling's rules onto the parent agenda.
//!
//! The cost of the heap successor is memory: each generator stores one entry per
//! sibling product in its snapshot (`Θ(n³)` live entries worst case), versus the
//! `O(1)` consumed-mask of the earlier rescan variant.

use super::AstarAgenda;
use crate::StateId;
use crate::algebras::{SpanAstarLeftIndex, SpanProductSiblingFinder};
use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// One sibling of a generator, keyed by the best merit achievable by combining
/// the generator's trigger with this sibling (the max over the group's rules).
/// `BinaryHeap` is a max-heap, so the top is the highest-merit unrealized sibling.
#[derive(Clone, Copy, Debug)]
pub(super) struct SiblingEntry {
    pub(super) merit: f64,
    /// Index of the sibling within the generator's snapshot prefix of the shared
    /// finder slice (stable: the finder's per-`[boundary][left]` vectors only
    /// grow, so this index keeps pointing at the same product).
    pub(super) sibling_index: u32,
}

impl PartialEq for SiblingEntry {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for SiblingEntry {}
impl PartialOrd for SiblingEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SiblingEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher merit is greater (pops first). Ties broken toward the lower
        // sibling index for a deterministic, reproducible realization order.
        self.merit
            .total_cmp(&other.merit)
            .then_with(|| other.sibling_index.cmp(&self.sibling_index))
    }
}

/// A single binary combination site rooted at one finalized trigger product.
///
/// The generator computes the merit of every sibling once (at creation) and
/// holds them in `pending`, a max-heap by merit. Realizing pops the top sibling
/// and re-derives that sibling's rules from the shared finder; no rescan.
pub(super) struct SpanGenerator {
    /// The finalized trigger product (later-finalized child of the combination).
    pub(super) trigger: StateId,
    /// The trigger's right (span) state; resolves to the trigger span.
    pub(super) trigger_right: StateId,
    /// The trigger's left (grammar) state; selects the binary group list.
    pub(super) trigger_left: StateId,
    /// Child slot the trigger fills: `0` = left child, `1` = right child.
    pub(super) position: u8,
    /// Index into `binary_groups(trigger_left, position)`.
    pub(super) group_idx: u32,
    /// Unrealized siblings, ordered by merit (max-heap).
    pub(super) pending: BinaryHeap<SiblingEntry>,
}

/// Owns the shared sibling index, the generator arena, and the frontier heap.
///
/// Lives for the duration of one lazy candidate-source run, alongside the
/// existing per-product agenda in [`super::AstarContext`].
#[derive(Default)]
pub(super) struct SpanLazyFrontier {
    /// Shared per-`[boundary][left]` index of finalized products, reused exactly
    /// as on the eager span path (populated via `activate_product`).
    pub(super) finder: SpanProductSiblingFinder,
    /// Generator arena; a generator's id is its index here.
    pub(super) generators: Vec<SpanGenerator>,
    /// Frontier heap keyed by each active generator's best unrealized merit
    /// (reuses [`AstarAgenda`], which negates the key for max-merit order).
    pub(super) frontier: AstarAgenda,
}

impl SpanLazyFrontier {
    pub(super) fn new() -> Self {
        Self::default()
    }
}

/// Explicit experimental candidate source used only by lazy-frontier
/// equivalence tests and benchmark entry points.
pub(super) struct LazyStringAstarSource<'a> {
    pub(super) left_index: &'a SpanAstarLeftIndex,
    pub(super) frontier: SpanLazyFrontier,
}

impl<'a> LazyStringAstarSource<'a> {
    pub(super) fn new(left_index: &'a SpanAstarLeftIndex) -> Self {
        Self {
            left_index,
            frontier: SpanLazyFrontier::new(),
        }
    }
}
