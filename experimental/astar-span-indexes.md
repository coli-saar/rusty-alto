# Experimental A* Span Indexes

This file keeps two string-specific indexing ideas that were useful while
profiling A* candidate generation, but are not part of the current fast path.

They are intentionally not compiled. The current implementation in `src/astar.rs`
uses the generic right child cache for fallback cases and the product-aware span
sibling finder for the string fast path.

## Right-state-only span sibling finder

This finder indexes finalized right span states by boundary only. It reduced the
number of set-trie joins, but still returned huge numbers of adjacent right spans
that did not have the left sibling product required by the current grammar rule.
The product-aware finder replaced it.

```rust
#[derive(Debug, Default)]
struct SpanSiblingFinder {
    left_seen_by_end: Vec<Vec<StateId>>,
    right_seen_by_start: Vec<Vec<StateId>>,
    seen_left: FixedBitSet,
    seen_right: FixedBitSet,
}

impl SpanSiblingFinder {
    fn activate(&mut self, state: StateId, span: Span, position: usize) -> bool {
        match position {
            0 => {
                if self.seen_left.len() <= state.index() {
                    self.seen_left.grow(state.index() + 1);
                }
                if self.seen_left.contains(state.index()) {
                    return false;
                }
                self.seen_left.set(state.index(), true);
                if self.left_seen_by_end.len() <= span.end {
                    self.left_seen_by_end.resize_with(span.end + 1, Vec::new);
                }
                self.left_seen_by_end[span.end].push(state);
                true
            }
            1 => {
                if self.seen_right.len() <= state.index() {
                    self.seen_right.grow(state.index() + 1);
                }
                if self.seen_right.contains(state.index()) {
                    return false;
                }
                self.seen_right.set(state.index(), true);
                if self.right_seen_by_start.len() <= span.start {
                    self.right_seen_by_start.resize_with(span.start + 1, Vec::new);
                }
                self.right_seen_by_start[span.start].push(state);
                true
            }
            _ => false,
        }
    }

    fn partners_into(
        &self,
        state: StateId,
        span: Span,
        position: usize,
        out: &mut Vec<[StateId; 2]>,
    ) {
        out.clear();
        match position {
            0 => {
                if let Some(siblings) = self.right_seen_by_start.get(span.end) {
                    out.extend(siblings.iter().map(|&sibling| [state, sibling]));
                }
            }
            1 => {
                if let Some(siblings) = self.left_seen_by_end.get(span.start) {
                    out.extend(siblings.iter().map(|&sibling| [sibling, state]));
                }
            }
            _ => {}
        }
    }
}
```

## Span-boundary right-rule index

This index cached right-side rules by span boundary and exact binary right child
pair. It did reduce some rule scans, but the later product-aware sibling finder
made this machinery unnecessary for the normal string fast path. Keeping the
generic child-state cache in `astar.rs` is simpler and good enough for the
higher-arity fallback.

```rust
#[derive(Default)]
struct SpanBoundaryRightRuleIndex {
    by_child: FxHashMap<(usize, StateId), Rc<[usize]>>,
    rule_ids_by_shape: FxHashMap<(SmallVec<[StateId; 2]>, SymbolSet, StateId), usize>,
    by_binary_children: Vec<FxHashMap<StateId, Vec<usize>>>,
    finalized_by_start: Vec<Vec<StateId>>,
    finalized_by_end: Vec<Vec<StateId>>,
    finalized_right: FixedBitSet,
}
```
