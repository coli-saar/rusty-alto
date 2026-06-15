use crate::{
    FxHashMap, Interner, Span, StateId, Symbol, algebras::SpanProductSiblingFinder,
    materialize::OwnedRule,
};
use fixedbitset::FixedBitSet;

pub(super) struct SpanBinarySymbolGroup {
    pub(super) symbol: Symbol,
    pub(super) rule_indexes: Vec<usize>,
}

pub(super) struct SpanBinarySiblingGroup {
    pub(super) sibling_left: StateId,
    pub(super) symbol_groups: Vec<SpanBinarySymbolGroup>,
}

/// Left-rule index used by the span-state A* specialization.
///
/// The generic A* expansion asks the right automaton for all rules containing
/// the finalized right child, then joins those rules against the left set trie.
/// For string spans, most useful rules are unary or binary. Binary span
/// siblings are determined by adjacency, so we can group left rules by the
/// finalized left child, the child position, the required sibling left state,
/// and the symbol. At expansion time this lets us retrieve only finalized
/// product siblings that can actually combine with the current left rule group.
///
/// Rules of arity greater than two are marked here and handled by the generic
/// expansion path for correctness.
#[derive(Default)]
pub(super) struct SpanAstarLeftIndex {
    unary_by_left: Vec<Vec<usize>>,
    binary_groups: Vec<[Vec<SpanBinarySiblingGroup>; 2]>,
    binary_positions_by_left: Vec<u8>,
    higher_arity_left: FixedBitSet,
}

impl SpanAstarLeftIndex {
    pub(super) fn build(left_rules: &[OwnedRule]) -> Self {
        let mut index = Self::default();
        let mut binary_rules: FxHashMap<(StateId, usize, StateId), FxHashMap<Symbol, Vec<usize>>> =
            FxHashMap::default();

        for (rule_idx, rule) in left_rules.iter().enumerate() {
            match rule.children.len() {
                0 => {}
                1 => {
                    let left = rule.children[0];
                    if index.unary_by_left.len() <= left.index() {
                        index.unary_by_left.resize_with(left.index() + 1, Vec::new);
                    }
                    index.unary_by_left[left.index()].push(rule_idx);
                }
                2 => {
                    for position in 0..2 {
                        let trigger_left = rule.children[position];
                        let sibling_left = rule.children[1 - position];
                        if index.binary_positions_by_left.len() <= trigger_left.index() {
                            index
                                .binary_positions_by_left
                                .resize(trigger_left.index() + 1, 0);
                        }
                        index.binary_positions_by_left[trigger_left.index()] |= 1 << position;
                        binary_rules
                            .entry((trigger_left, position, sibling_left))
                            .or_default()
                            .entry(rule.symbol)
                            .or_default()
                            .push(rule_idx);
                    }
                }
                _ => {
                    for &child in &rule.children {
                        if index.higher_arity_left.len() <= child.index() {
                            index.higher_arity_left.grow(child.index() + 1);
                        }
                        index.higher_arity_left.set(child.index(), true);
                    }
                }
            }
        }

        for ((trigger_left, position, sibling_left), rules_by_symbol) in binary_rules {
            let mut symbol_groups: Vec<_> = rules_by_symbol
                .into_iter()
                .map(|(symbol, mut rule_indexes)| {
                    rule_indexes.sort_unstable();
                    SpanBinarySymbolGroup {
                        symbol,
                        rule_indexes,
                    }
                })
                .collect();
            symbol_groups.sort_by_key(|group| group.symbol);
            if index.binary_groups.len() <= trigger_left.index() {
                index
                    .binary_groups
                    .resize_with(trigger_left.index() + 1, || [Vec::new(), Vec::new()]);
            }
            index.binary_groups[trigger_left.index()][position].push(SpanBinarySiblingGroup {
                sibling_left,
                symbol_groups,
            });
        }

        for slots in &mut index.binary_groups {
            for groups in slots {
                groups.sort_by_key(|group| group.sibling_left);
            }
        }

        index
    }

    pub(super) fn unary_rules(&self, left: StateId) -> Option<&[usize]> {
        self.unary_by_left.get(left.index()).map(Vec::as_slice)
    }

    pub(super) fn binary_groups(
        &self,
        left: StateId,
        position: usize,
    ) -> Option<&[SpanBinarySiblingGroup]> {
        self.binary_groups
            .get(left.index())
            .and_then(|slots| slots.get(position))
            .map(Vec::as_slice)
    }

    pub(super) fn has_higher_arity(&self, left: StateId) -> bool {
        left.index() < self.higher_arity_left.len() && self.higher_arity_left.contains(left.index())
    }

    pub(super) fn has_any_higher_arity(&self) -> bool {
        self.higher_arity_left.ones().next().is_some()
    }

    pub(super) fn activate_product(
        &self,
        finder: &mut SpanProductSiblingFinder,
        product: StateId,
        left_state: StateId,
        right_state: StateId,
        span: Span,
    ) {
        // Insert a product only for child positions where its left state occurs
        // in a binary left rule. This keeps the sibling finder smaller than a
        // table that records every finalized product at every position.
        let Some(&mask) = self.binary_positions_by_left.get(left_state.index()) else {
            return;
        };
        if mask & 0b01 != 0 {
            finder.activate(product, left_state, right_state, span, 0);
        }
        if mask & 0b10 != 0 {
            finder.activate(product, left_state, right_state, span, 1);
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct SpanInterner {
    n: usize,
    spans: Vec<Span>,
}

impl SpanInterner {
    pub(super) fn new(n: usize) -> Self {
        let mut spans = Vec::with_capacity(n.saturating_mul(n + 1) / 2);
        for start in 0..n {
            for end in (start + 1)..=n {
                spans.push(Span::new(start, end));
            }
        }
        Self { n, spans }
    }

    #[inline]
    pub(super) fn intern(&mut self, span: Span) -> StateId {
        assert!(
            span.start < span.end && span.end <= self.n,
            "invalid string span {:?} for sentence length {}",
            span,
            self.n
        );
        let before_start = span.start * self.n - span.start.saturating_sub(1) * span.start / 2;
        let index = before_start + (span.end - span.start - 1);
        StateId(u32::try_from(index).expect("too many spans for StateId"))
    }

    #[inline]
    pub(super) fn resolve(&self, id: StateId) -> &Span {
        self.spans
            .get(id.index())
            .expect("span state id not present in interner")
    }

    pub(super) fn into_interner(self) -> Interner<Span> {
        let mut interner = Interner::new();
        for span in self.spans {
            let id = interner.intern(span);
            debug_assert_eq!(id.index(), interner.len() - 1);
        }
        interner
    }
}
