use super::Algebra;
use crate::{
    BottomUpTa, CondensedTa, Explicit, FxHashMap, IndexedBottomUpTa, InvHom, ProbabilityScorer,
    Signature, StateId, StateUniverse, Symbol, SymbolSet, TopDownTa, WeightScorer,
    heuristic::IntersectionHeuristic,
    homomorphism::{HomLabel, Homomorphism},
};
use fixedbitset::FixedBitSet;
use smallvec::SmallVec;
use std::convert::Infallible;

/// Reserved concatenation operation name for [`StringAlgebra`].
pub const CONCAT: &str = "*";

/// A half-open input span `[start, end)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Span {
    /// Inclusive start position.
    pub start: usize,
    /// Exclusive end position.
    pub end: usize,
}

impl Span {
    /// Construct a span.
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Return the span length.
    pub fn len(self) -> usize {
        self.end - self.start
    }

    /// Return whether this span is empty.
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// A finalized product item that can serve as a binary string sibling.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SpanProductSibling {
    pub(crate) product: StateId,
    pub(crate) right_state: StateId,
}

/// Product-aware sibling finder for binary string span rules.
///
/// The index includes the required left state as well as the span boundary.
/// Queries therefore return only finalized product states that can actually fill
/// the sibling slot of the current left rule.
#[derive(Debug, Default)]
pub(crate) struct SpanProductSiblingFinder {
    left_seen_by_end: Vec<Vec<Vec<SpanProductSibling>>>,
    right_seen_by_start: Vec<Vec<Vec<SpanProductSibling>>>,
    seen_left: FixedBitSet,
    seen_right: FixedBitSet,
}

impl SpanProductSiblingFinder {
    /// Activate `product` as available at child `position`.
    ///
    /// Returns `true` only the first time the `(position, product)` pair is seen.
    pub(crate) fn activate(
        &mut self,
        product: StateId,
        left_state: StateId,
        right_state: StateId,
        span: Span,
        position: usize,
    ) -> bool {
        match position {
            0 => {
                if self.seen_left.len() <= product.index() {
                    self.seen_left.grow(product.index() + 1);
                }
                if self.seen_left.contains(product.index()) {
                    return false;
                }
                self.seen_left.set(product.index(), true);
                if self.left_seen_by_end.len() <= span.end {
                    self.left_seen_by_end.resize_with(span.end + 1, Vec::new);
                }
                let by_left = &mut self.left_seen_by_end[span.end];
                if by_left.len() <= left_state.index() {
                    by_left.resize_with(left_state.index() + 1, Vec::new);
                }
                by_left[left_state.index()].push(SpanProductSibling {
                    product,
                    right_state,
                });
                true
            }
            1 => {
                if self.seen_right.len() <= product.index() {
                    self.seen_right.grow(product.index() + 1);
                }
                if self.seen_right.contains(product.index()) {
                    return false;
                }
                self.seen_right.set(product.index(), true);
                if self.right_seen_by_start.len() <= span.start {
                    self.right_seen_by_start
                        .resize_with(span.start + 1, Vec::new);
                }
                let by_left = &mut self.right_seen_by_start[span.start];
                if by_left.len() <= left_state.index() {
                    by_left.resize_with(left_state.index() + 1, Vec::new);
                }
                by_left[left_state.index()].push(SpanProductSibling {
                    product,
                    right_state,
                });
                true
            }
            _ => false,
        }
    }

    /// Write active sibling products for `span` at `position`.
    pub(crate) fn sibling_products_into(
        &self,
        span: Span,
        position: usize,
        required_left: StateId,
        out: &mut Vec<SpanProductSibling>,
    ) {
        out.clear();
        match position {
            0 => {
                if let Some(siblings) = self
                    .right_seen_by_start
                    .get(span.end)
                    .and_then(|by_left| by_left.get(required_left.index()))
                {
                    out.extend_from_slice(siblings);
                }
            }
            1 => {
                if let Some(siblings) = self
                    .left_seen_by_end
                    .get(span.start)
                    .and_then(|by_left| by_left.get(required_left.index()))
                {
                    out.extend_from_slice(siblings);
                }
            }
            _ => {}
        }
    }
}

/// Binary string algebra over token symbols.
///
/// Values are token-symbol vectors. The reserved concat operation appends two
/// vectors; every other nullary symbol evaluates to the one-token string
/// containing that symbol.
#[derive(Clone, Debug)]
pub struct StringAlgebra {
    signature: Signature,
    concat: Symbol,
}

impl StringAlgebra {
    /// Create a string algebra with the reserved concat symbol.
    pub fn new() -> Self {
        let mut signature = Signature::new();
        let concat = signature.intern(CONCAT.to_owned(), 2).unwrap();
        Self { signature, concat }
    }

    /// Create a string algebra from an existing operation signature.
    pub fn with_signature(mut signature: Signature) -> Self {
        let concat = signature.intern(CONCAT.to_owned(), 2).unwrap();
        Self { signature, concat }
    }

    /// Return the concat operation symbol.
    pub fn concat_symbol(&self) -> Symbol {
        self.concat
    }

    /// Intern a token symbol.
    pub fn intern_word(&mut self, word: impl Into<String>) -> Symbol {
        self.signature.intern(word.into(), 0).unwrap()
    }

    /// Parse a whitespace-separated string into token symbols.
    pub fn parse_string(&mut self, input: &str) -> Vec<Symbol> {
        input
            .split_whitespace()
            .map(|word| self.intern_word(word.to_owned()))
            .collect()
    }

    /// Build the optimized lazy decomposition automaton for `sentence`.
    pub fn decompose(&self, sentence: Vec<Symbol>) -> StringDecompositionAutomaton {
        StringDecompositionAutomaton::new(self.concat, sentence)
    }
}

impl Default for StringAlgebra {
    fn default() -> Self {
        Self::new()
    }
}

impl Algebra for StringAlgebra {
    type Value = Vec<Symbol>;
    type ParseError = Infallible;

    fn signature(&self) -> &Signature {
        &self.signature
    }

    fn evaluate(&self, symbol: Symbol, children: &[Self::Value]) -> Option<Self::Value> {
        if symbol == self.concat {
            let [left, right] = children else {
                return None;
            };
            let mut out = Vec::with_capacity(left.len() + right.len());
            out.extend_from_slice(left);
            out.extend_from_slice(right);
            Some(out)
        } else if children.is_empty() {
            Some(vec![symbol])
        } else {
            None
        }
    }

    fn parse_object(&mut self, input: &str) -> Result<Self::Value, Self::ParseError> {
        Ok(self.parse_string(input))
    }
}

/// Lazy CKY-style string decomposition automaton.
#[derive(Clone, Debug)]
pub struct StringDecompositionAutomaton {
    concat: Symbol,
    sentence: Vec<Symbol>,
    positions_by_word: FxHashMap<Symbol, Vec<usize>>,
}

impl StringDecompositionAutomaton {
    /// Build a lazy decomposition automaton for `sentence`.
    pub fn new(concat: Symbol, sentence: Vec<Symbol>) -> Self {
        let mut positions_by_word = FxHashMap::default();
        for (position, &word) in sentence.iter().enumerate() {
            positions_by_word
                .entry(word)
                .or_insert_with(Vec::new)
                .push(position);
        }
        Self {
            concat,
            sentence,
            positions_by_word,
        }
    }

    /// Return the concat operation symbol.
    pub fn concat_symbol(&self) -> Symbol {
        self.concat
    }

    /// Return the sentence length.
    pub fn len(&self) -> usize {
        self.sentence.len()
    }

    /// Return whether the sentence is empty.
    pub fn is_empty(&self) -> bool {
        self.sentence.is_empty()
    }

    /// Count explicit CKY-style decomposition rules without materializing them.
    pub fn rule_count(&self) -> usize {
        let n = self.len();
        n + n.saturating_sub(1) * n * (n + 1) / 6
    }

    fn valid_span(&self, span: Span) -> bool {
        span.start < span.end && span.end <= self.len()
    }
}

impl BottomUpTa for StringDecompositionAutomaton {
    type State = Span;

    fn step(&self, f: Symbol, children: &[Span], out: &mut dyn FnMut(Span)) {
        if f == self.concat {
            let [left, right] = children else {
                return;
            };
            if self.valid_span(*left) && self.valid_span(*right) && left.end == right.start {
                out(Span::new(left.start, right.end));
            }
            return;
        }

        if !children.is_empty() {
            return;
        }
        if let Some(positions) = self.positions_by_word.get(&f) {
            for &i in positions {
                out(Span::new(i, i + 1));
            }
        }
    }

    fn is_accepting(&self, q: &Span) -> bool {
        *q == Span::new(0, self.len())
    }
}

impl StateUniverse for StringDecompositionAutomaton {
    fn all_states(&self, out: &mut dyn FnMut(Span)) {
        for start in 0..self.len() {
            for end in start + 1..=self.len() {
                out(Span::new(start, end));
            }
        }
    }
}

impl IndexedBottomUpTa for StringDecompositionAutomaton {
    fn step_partial(
        &self,
        f: Symbol,
        position: usize,
        state_at_position: &Span,
        out: &mut dyn FnMut(&[Span], Span),
    ) {
        if f != self.concat || !self.valid_span(*state_at_position) {
            return;
        }

        match position {
            0 => {
                let left = *state_at_position;
                for end in left.end + 1..=self.len() {
                    let right = Span::new(left.end, end);
                    let children = [left, right];
                    out(&children, Span::new(left.start, end));
                }
            }
            1 => {
                let right = *state_at_position;
                for start in 0..right.start {
                    let left = Span::new(start, right.start);
                    let children = [left, right];
                    out(&children, Span::new(start, right.end));
                }
            }
            _ => {}
        }
    }
}

impl TopDownTa for StringDecompositionAutomaton {
    fn step_topdown(&self, parent: &Span, out: &mut dyn FnMut(Symbol, &[Span])) {
        if !self.valid_span(*parent) {
            return;
        }
        if parent.len() == 1 {
            let word = self.sentence[parent.start];
            out(word, &[]);
            return;
        }
        for split in parent.start + 1..parent.end {
            let children = [Span::new(parent.start, split), Span::new(split, parent.end)];
            out(self.concat, &children);
        }
    }

    fn initial_states(&self, out: &mut dyn FnMut(Span)) {
        if !self.is_empty() {
            out(Span::new(0, self.len()));
        }
    }
}

impl CondensedTa for StringDecompositionAutomaton {
    fn condensed_rules(&self, out: &mut dyn FnMut(&[Span], &SymbolSet, Span)) {
        let mut lexical_children = SmallVec::<[Span; 0]>::new();
        for (i, &word) in self.sentence.iter().enumerate() {
            let mut symbols = SymbolSet::new();
            symbols.insert(word);
            out(&lexical_children, &symbols, Span::new(i, i + 1));
            lexical_children.clear();
        }

        let mut concat_symbols = SymbolSet::new();
        concat_symbols.insert(self.concat);
        for start in 0..self.len() {
            for split in start + 1..self.len() {
                for end in split + 1..=self.len() {
                    let children = [Span::new(start, split), Span::new(split, end)];
                    out(&children, &concat_symbols, Span::new(start, end));
                }
            }
        }
    }

    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, Span)) {
        for (i, &word) in self.sentence.iter().enumerate() {
            let mut symbols = SymbolSet::new();
            symbols.insert(word);
            out(&symbols, Span::new(i, i + 1));
        }
    }

    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &Span,
        out: &mut dyn FnMut(&[Span], &SymbolSet, Span),
    ) {
        if !self.valid_span(*state) {
            return;
        }

        let mut symbols = SymbolSet::new();
        symbols.insert(self.concat);
        match position {
            0 => {
                let left = *state;
                for end in left.end + 1..=self.len() {
                    let children = [left, Span::new(left.end, end)];
                    out(&children, &symbols, Span::new(left.start, end));
                }
            }
            1 => {
                let right = *state;
                for start in 0..right.start {
                    let children = [Span::new(start, right.start), right];
                    out(&children, &symbols, Span::new(start, right.end));
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// SX heuristic (Klein & Manning 2003)
// ---------------------------------------------------------------------------

/// A token in the yield template for a grammar rule symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum YieldToken {
    /// A word constant (leaf in the homomorphism term).
    Word,
    /// A grammar child reference (variable in the homomorphism term).
    Child(usize),
}

/// Walk the frontier of a homomorphism term left-to-right, producing yield tokens.
fn walk_frontier(
    arena: &rusty_tree::tree::TreeArena<HomLabel>,
    node: rusty_tree::tree::Tree,
) -> Vec<YieldToken> {
    match *arena.get_label(node) {
        HomLabel::Var(i) => vec![YieldToken::Child(i)],
        HomLabel::Symbol(_) => {
            let children = arena.get_children(node);
            if children.is_empty() {
                vec![YieldToken::Word]
            } else {
                children
                    .iter()
                    .flat_map(|&c| walk_frontier(arena, c))
                    .collect()
            }
        }
    }
}

/// A yield template derived from a homomorphism RHS term.
#[derive(Clone, Debug)]
struct YieldTemplate {
    /// The flat frontier tokens in left-to-right order.
    tokens: Vec<YieldToken>,
}

impl YieldTemplate {
    /// Count the Word tokens.
    fn word_count(&self) -> usize {
        self.tokens
            .iter()
            .filter(|&&t| t == YieldToken::Word)
            .count()
    }

    /// Return the child indices in order of their first appearance.
    fn children_in_order(&self) -> Vec<usize> {
        let mut seen = Vec::new();
        for &t in &self.tokens {
            if let YieldToken::Child(i) = t {
                if !seen.contains(&i) {
                    seen.push(i);
                }
            }
        }
        seen
    }

    /// Count Word tokens strictly to the left of child position `p` in the frontier.
    fn words_left_of_child(&self, p: usize) -> usize {
        let mut count = 0;
        for &t in &self.tokens {
            match t {
                YieldToken::Word => count += 1,
                YieldToken::Child(i) if i == p => break,
                _ => {}
            }
        }
        count
    }

    /// Count Word tokens strictly to the right of child position `p` in the frontier.
    fn words_right_of_child(&self, p: usize) -> usize {
        let mut count = 0;
        let mut after = false;
        for &t in &self.tokens {
            match t {
                YieldToken::Child(i) if i == p => after = true,
                YieldToken::Word if after => count += 1,
                _ => {}
            }
        }
        count
    }

    /// Returns the child indices that appear to the left of child `p` in the frontier.
    fn children_left_of(&self, p: usize) -> Vec<usize> {
        let mut result = Vec::new();
        for &t in &self.tokens {
            match t {
                YieldToken::Child(i) if i == p => break,
                YieldToken::Child(i) => {
                    if !result.contains(&i) {
                        result.push(i);
                    }
                }
                _ => {}
            }
        }
        result
    }

    /// Returns the child indices that appear to the right of child `p` in the frontier.
    fn children_right_of(&self, p: usize) -> Vec<usize> {
        let mut result = Vec::new();
        let mut after = false;
        for &t in &self.tokens {
            match t {
                YieldToken::Child(i) if i == p => after = true,
                YieldToken::Child(i) if after => {
                    if !result.contains(&i) {
                        result.push(i);
                    }
                }
                _ => {}
            }
        }
        result
    }
}

/// String-specific outside heuristic (Klein & Manning 2003).
///
/// `SxHeuristic` precomputes best inside weights `BI(X, w)` (the best weight
/// to derive exactly `w` words from grammar state `X`) and outside weights
/// `SX(X, l, r)` (the best context weight with `l` words to the left and `r`
/// words to the right). The `outside_estimate` then looks up `SX(X, l, r)`
/// where `l = span.start` and `r = n - span.end`.
pub(crate) struct SxHeuristic {
    /// sx[state_idx][l*(n+1) + r] = best outside weight
    sx: Vec<Box<[f64]>>,
    /// Sentence length.
    n: usize,
    /// Stride for the second dimension (= n+1).
    stride: usize,
    /// Score for impossible/out-of-range entries.
    zero: f64,
}

impl IntersectionHeuristic<StringDecompositionAutomaton> for SxHeuristic {
    fn outside_estimate(&self, left: StateId, span: &Span) -> f64 {
        let l = span.start;
        let r = self.n.saturating_sub(span.end);
        self.sx
            .get(left.index())
            .and_then(|row| row.get(l * self.stride + r))
            .copied()
            .unwrap_or(self.zero)
    }
}

impl IntersectionHeuristic<InvHom<'_, StringDecompositionAutomaton>> for SxHeuristic {
    fn outside_estimate(&self, left: StateId, span: &Span) -> f64 {
        // InvHom<StringDecompositionAutomaton>::State = Span, so delegate directly.
        <Self as IntersectionHeuristic<StringDecompositionAutomaton>>::outside_estimate(
            self, left, span,
        )
    }
}

impl SxHeuristic {
    fn lookup_lr(&self, left: StateId, l: usize, r: usize) -> f64 {
        self.sx
            .get(left.index())
            .and_then(|row| row.get(l * self.stride + r))
            .copied()
            .unwrap_or(self.zero)
    }

    /// Build the SX heuristic for a grammar intersected with a string of length `n`.
    ///
    /// `grammar` is the left (grammar) automaton; `hom` is the string homomorphism
    /// mapping grammar symbols to string-algebra terms; `concat` is the concat symbol
    /// in the string algebra.
    pub fn new(grammar: &Explicit, hom: &Homomorphism, concat: Symbol, n: usize) -> Self {
        Self::new_with(grammar, hom, concat, n, &ProbabilityScorer)
    }

    pub fn new_with<S: WeightScorer>(
        grammar: &Explicit,
        hom: &Homomorphism,
        concat: Symbol,
        n: usize,
        scorer: &S,
    ) -> Self {
        let num_states = grammar.num_states() as usize;
        let arena = hom.arena();

        // Build yield templates for every grammar rule.
        // For each rule, look up the homomorphic image of the rule symbol and
        // walk its frontier to get the yield template.
        let rules: Vec<_> = grammar.rules().collect();

        // For each rule, compute the yield template.
        // If the rule symbol has no homomorphic image, treat it as unknown (skip it).
        let templates: Vec<Option<YieldTemplate>> = rules
            .iter()
            .map(|rule| {
                hom.get(rule.symbol).map(|term| {
                    let tokens = walk_frontier(arena, term);
                    // Filter out any concat wrapper — the frontier walk already handles this
                    // by recursing into concat nodes. But we need to remove concat symbol tokens
                    // that are inner nodes (they will appear as Symbol(concat) nodes with children
                    // and will be recursed into, not emitted as Word). So frontier is already correct.
                    let _ = concat; // concat used for reference; walk_frontier handles it
                    YieldTemplate { tokens }
                })
            })
            .collect();

        // -----------------------------------------------------------------------
        // Precompute minwidth(X): minimum number of words any derivation from X
        // must yield. Initialized to a large sentinel.
        // -----------------------------------------------------------------------
        const INF: usize = usize::MAX / 2;
        let mut minwidth = vec![INF; num_states];

        // Fixpoint: iterate until no change.
        let mut changed = true;
        while changed {
            changed = false;
            for (rule_idx, rule) in rules.iter().enumerate() {
                let Some(tmpl) = &templates[rule_idx] else {
                    continue;
                };
                let t_words = tmpl.word_count();
                let children = tmpl.children_in_order();
                let arity = children.len();

                // Compute the minimum width contribution from children.
                let child_min_sum: usize = if arity == 0 {
                    0
                } else {
                    let mut sum: usize = 0;
                    let mut feasible = true;
                    for &ci in &children {
                        let child_state = rule.children.get(ci).copied();
                        let child_state = match child_state {
                            Some(s) if !s.is_stuck() => s,
                            _ => {
                                feasible = false;
                                break;
                            }
                        };
                        let mw = minwidth[child_state.index()];
                        if mw == INF {
                            feasible = false;
                            break;
                        }
                        sum = sum.saturating_add(mw);
                    }
                    if !feasible {
                        continue;
                    }
                    sum
                };

                let new_min = t_words.saturating_add(child_min_sum);
                let ri = rule.result.index();
                if new_min < minwidth[ri] {
                    minwidth[ri] = new_min;
                    changed = true;
                }
            }
        }

        // -----------------------------------------------------------------------
        // BI(X, w) = best inside weight to derive exactly w words from state X.
        // Shape: [num_states][n+1]
        // -----------------------------------------------------------------------
        let mut bi = vec![vec![scorer.zero(); n + 1]; num_states];

        // Process rules in increasing target width (outer loop = w).
        // For binarized grammars this is O(n^2) per rule.

        // Iterate over rules grouped by arity:
        // 0: lexical
        // 1, t_words=0: unary width-preserving
        // general: iterate over splits

        // We do multiple passes to handle unary chains. The outer loop runs n+1 times
        // and for each width, we saturate unary rules. For binary rules, we enumerate splits.

        // First pass: lexical rules (arity 0, t_words > 0)
        for (rule_idx, rule) in rules.iter().enumerate() {
            let Some(tmpl) = &templates[rule_idx] else {
                continue;
            };
            let t_words = tmpl.word_count();
            let children = tmpl.children_in_order();
            if !children.is_empty() {
                continue;
            } // not lexical
            if t_words == 0 || t_words > n {
                continue;
            }
            let ri = rule.result.index();
            let candidate = scorer.rule_score(rule.weight);
            if scorer.better(candidate, bi[ri][t_words]) {
                bi[ri][t_words] = candidate;
            }
        }

        // For each width w, process rules that can produce exactly w words.
        // We need to handle unary (width-preserving) rules iteratively.
        for w in 0..=n {
            // Saturate unary width-preserving rules at this width.
            let mut inner_changed = true;
            while inner_changed {
                inner_changed = false;
                for (rule_idx, rule) in rules.iter().enumerate() {
                    let Some(tmpl) = &templates[rule_idx] else {
                        continue;
                    };
                    let t_words = tmpl.word_count();
                    let children = tmpl.children_in_order();
                    if children.len() != 1 || t_words != 0 {
                        continue;
                    }
                    let child_idx = children[0];
                    let child_state = match rule.children.get(child_idx) {
                        Some(&s) if !s.is_stuck() => s,
                        _ => continue,
                    };
                    let child_bi = bi[child_state.index()][w];
                    if child_bi == scorer.zero() {
                        continue;
                    }
                    let candidate = scorer.times(scorer.rule_score(rule.weight), child_bi);
                    let ri = rule.result.index();
                    if scorer.better(candidate, bi[ri][w]) {
                        bi[ri][w] = candidate;
                        inner_changed = true;
                    }
                }
            }

            // General case: rules with arity >= 1 and t_words > 0, or arity >= 2.
            // For each such rule, enumerate splits of w words among children + word tokens.
            for (rule_idx, rule) in rules.iter().enumerate() {
                let Some(tmpl) = &templates[rule_idx] else {
                    continue;
                };
                let t_words = tmpl.word_count();
                let children = tmpl.children_in_order();
                let arity = children.len();

                // Skip lexical (handled above) and unary-preserving (handled above)
                if arity == 0 {
                    continue;
                }
                if arity == 1 && t_words == 0 {
                    continue;
                }

                // Check feasibility: total must be at least t_words + sum(minwidth(child))
                if t_words > w {
                    continue;
                }
                let remaining = w - t_words;

                if arity == 1 {
                    // Single child, specific word count contribution
                    let child_idx = children[0];
                    let child_state = match rule.children.get(child_idx) {
                        Some(&s) if !s.is_stuck() => s,
                        _ => continue,
                    };
                    let w_child = remaining;
                    if w_child > n {
                        continue;
                    }
                    let child_bi = bi[child_state.index()][w_child];
                    if child_bi == scorer.zero() {
                        continue;
                    }
                    let candidate = scorer.times(scorer.rule_score(rule.weight), child_bi);
                    let ri = rule.result.index();
                    if scorer.better(candidate, bi[ri][w]) {
                        bi[ri][w] = candidate;
                    }
                } else if arity == 2 {
                    // Binary: split `remaining` between child 0 and child 1
                    let child0_idx = children[0];
                    let child1_idx = children[1];
                    let child0_state = match rule.children.get(child0_idx) {
                        Some(&s) if !s.is_stuck() => s,
                        _ => continue,
                    };
                    let child1_state = match rule.children.get(child1_idx) {
                        Some(&s) if !s.is_stuck() => s,
                        _ => continue,
                    };
                    let mw0 = minwidth[child0_state.index()];
                    let mw1 = minwidth[child1_state.index()];

                    for w0 in mw0..=remaining.saturating_sub(if mw1 < INF { mw1 } else { break }) {
                        let w1 = remaining - w0;
                        if w1 < mw1 || mw1 == INF {
                            continue;
                        }
                        let bi0 = bi[child0_state.index()][w0];
                        if bi0 == scorer.zero() {
                            continue;
                        }
                        let bi1 = bi[child1_state.index()][w1];
                        if bi1 == scorer.zero() {
                            continue;
                        }
                        let candidate =
                            scorer.times(scorer.times(scorer.rule_score(rule.weight), bi0), bi1);
                        let ri = rule.result.index();
                        if scorer.better(candidate, bi[ri][w]) {
                            bi[ri][w] = candidate;
                        }
                    }
                } else {
                    // Higher arity: enumerate all splits
                    let child_states: Vec<_> = children
                        .iter()
                        .map(|&ci| rule.children.get(ci).copied().filter(|s| !s.is_stuck()))
                        .collect();
                    if child_states.iter().any(|s| s.is_none()) {
                        continue;
                    }
                    let child_states: Vec<StateId> =
                        child_states.into_iter().map(|s| s.unwrap()).collect();
                    let mins: Vec<usize> =
                        child_states.iter().map(|s| minwidth[s.index()]).collect();
                    if mins.iter().any(|&m| m == INF) {
                        continue;
                    }
                    let min_sum: usize = mins.iter().sum();
                    if remaining < min_sum {
                        continue;
                    }

                    // Enumerate all splits (recursive helper via stack)
                    let mut best_prod = scorer.zero();
                    enumerate_splits(
                        &child_states,
                        &mins,
                        remaining,
                        0,
                        1.0,
                        rule.weight,
                        &bi,
                        scorer,
                        &mut |prod| {
                            if scorer.better(prod, best_prod) {
                                best_prod = prod;
                            }
                        },
                    );
                    if best_prod != scorer.zero() {
                        let ri = rule.result.index();
                        if scorer.better(best_prod, bi[ri][w]) {
                            bi[ri][w] = best_prod;
                        }
                    }
                }
            }
        }

        // -----------------------------------------------------------------------
        // SX(X, l, r) = best outside weight with l words left, r words right.
        // Shape: [num_states][(n+1)*(n+1)]; stride = n+1.
        // Process BFS by increasing l+r (= decreasing parent width n-l-r).
        // -----------------------------------------------------------------------
        let stride = n + 1;
        let mut sx = vec![vec![scorer.zero(); stride * stride]; num_states];

        // Seed: accepting states get SX(a, 0, 0) = 1.0
        grammar.initial_states(&mut |state| {
            if !state.is_stuck() && state.index() < num_states {
                sx[state.index()][0] = scorer.one(); // l=0, r=0 -> index 0*stride+0=0
            }
        });

        // Process BFS by level lr = l + r = 0, 1, ..., n
        for lr in 0..=n {
            // At each level, we may need to fix unary width-preserving rules within the level.
            // For those, SX(child, l, r) >= SX(parent, l, r) * rule.weight when l+r = parent's lr.
            // Iterate until fixpoint for unary rules at this level.
            let mut level_changed = true;
            while level_changed {
                level_changed = false;
                for (rule_idx, rule) in rules.iter().enumerate() {
                    let Some(tmpl) = &templates[rule_idx] else {
                        continue;
                    };
                    let t_words = tmpl.word_count();
                    let children = tmpl.children_in_order();
                    if children.len() != 1 || t_words != 0 {
                        continue;
                    }

                    let child_idx = children[0];
                    let child_state = match rule.children.get(child_idx) {
                        Some(&s) if !s.is_stuck() => s,
                        _ => continue,
                    };

                    let parent_state = rule.result;
                    // For all (l, r) with l+r = lr
                    for l in 0..=lr {
                        let r = lr - l;
                        if l + r > n {
                            continue;
                        }
                        let idx = l * stride + r;
                        let parent_sx = sx[parent_state.index()][idx];
                        if parent_sx == scorer.zero() {
                            continue;
                        }
                        let candidate = scorer.times(parent_sx, scorer.rule_score(rule.weight));
                        if scorer.better(candidate, sx[child_state.index()][idx]) {
                            sx[child_state.index()][idx] = candidate;
                            level_changed = true;
                        }
                    }
                }
            }

            // Now process non-unary rules: for each settled (A, l_A, r_A) with l_A+r_A = lr,
            // expand top-down to children.
            for (rule_idx, rule) in rules.iter().enumerate() {
                let Some(tmpl) = &templates[rule_idx] else {
                    continue;
                };
                let t_words = tmpl.word_count();
                let children_order = tmpl.children_in_order();
                let arity = children_order.len();

                if arity == 0 {
                    continue;
                } // no children to update

                // Unary width-preserving already handled above
                if arity == 1 && t_words == 0 {
                    continue;
                }

                let parent_state = rule.result;

                for l_a in 0..=lr {
                    let r_a = lr - l_a;
                    if l_a + r_a > n {
                        continue;
                    }
                    let parent_sx = sx[parent_state.index()][l_a * stride + r_a];
                    if parent_sx == scorer.zero() {
                        continue;
                    }

                    let parent_width = n - l_a - r_a;
                    if t_words > parent_width {
                        continue;
                    }
                    let remaining_for_children = parent_width - t_words;

                    if arity == 1 {
                        // arity=1, t_words > 0: child gets all remaining width
                        let child_idx = children_order[0];
                        let child_state = match rule.children.get(child_idx) {
                            Some(&s) if !s.is_stuck() => s,
                            _ => continue,
                        };
                        let wl_p = tmpl.words_left_of_child(child_idx);
                        let wr_p = tmpl.words_right_of_child(child_idx);
                        // Words to the left/right of the child from the parent perspective
                        let l_c = l_a + wl_p;
                        let r_c = r_a + wr_p;
                        if l_c + r_c > n {
                            continue;
                        }
                        let candidate = scorer.times(parent_sx, scorer.rule_score(rule.weight));
                        if scorer.better(candidate, sx[child_state.index()][l_c * stride + r_c]) {
                            sx[child_state.index()][l_c * stride + r_c] = candidate;
                        }
                    } else if arity == 2 {
                        // Binary fast path
                        let child0_idx = children_order[0];
                        let child1_idx = children_order[1];
                        let child0_state = match rule.children.get(child0_idx) {
                            Some(&s) if !s.is_stuck() => s,
                            _ => continue,
                        };
                        let child1_state = match rule.children.get(child1_idx) {
                            Some(&s) if !s.is_stuck() => s,
                            _ => continue,
                        };
                        let mw0 = minwidth[child0_state.index()];
                        let mw1 = minwidth[child1_state.index()];
                        let wl0 = tmpl.words_left_of_child(child0_idx);
                        let wr0 = tmpl.words_right_of_child(child0_idx);
                        let wl1 = tmpl.words_left_of_child(child1_idx);
                        let wr1 = tmpl.words_right_of_child(child1_idx);

                        // For child 0: for each w1 of child 1
                        if mw1 < INF {
                            let max_w1 = remaining_for_children.saturating_sub(if mw0 < INF {
                                mw0
                            } else {
                                0
                            });
                            for w1 in mw1..=max_w1 {
                                let w0 = remaining_for_children - w1;
                                if mw0 < INF && w0 < mw0 {
                                    continue;
                                }
                                let bi1 = bi[child1_state.index()][w1];
                                if bi1 == scorer.zero() {
                                    continue;
                                }
                                // child 1 is to the right of child 0 in frontier
                                // l_c0 = l_a + wl0 (words left of child0 in template)
                                // r_c0 = r_a + wr0 + w1 (words strictly right of child0 = wr0 from template + w1 from sibling)
                                let l_c0 = l_a + wl0;
                                let r_c0 = r_a + wr0 + w1;
                                if l_c0 + r_c0 > n {
                                    continue;
                                }
                                let candidate = scorer.times(
                                    scorer.times(parent_sx, scorer.rule_score(rule.weight)),
                                    bi1,
                                );
                                if scorer.better(
                                    candidate,
                                    sx[child0_state.index()][l_c0 * stride + r_c0],
                                ) {
                                    sx[child0_state.index()][l_c0 * stride + r_c0] = candidate;
                                }
                            }
                        }

                        // For child 1: for each w0 of child 0
                        if mw0 < INF {
                            let max_w0 = remaining_for_children.saturating_sub(if mw1 < INF {
                                mw1
                            } else {
                                0
                            });
                            for w0 in mw0..=max_w0 {
                                let w1 = remaining_for_children - w0;
                                if mw1 < INF && w1 < mw1 {
                                    continue;
                                }
                                let bi0 = bi[child0_state.index()][w0];
                                if bi0 == scorer.zero() {
                                    continue;
                                }
                                // l_c1 = l_a + wl1 + w0 (words left of child1 = wl1 from template + w0 from sibling)
                                // r_c1 = r_a + wr1
                                let l_c1 = l_a + wl1 + w0;
                                let r_c1 = r_a + wr1;
                                if l_c1 + r_c1 > n {
                                    continue;
                                }
                                let candidate = scorer.times(
                                    scorer.times(parent_sx, scorer.rule_score(rule.weight)),
                                    bi0,
                                );
                                if scorer.better(
                                    candidate,
                                    sx[child1_state.index()][l_c1 * stride + r_c1],
                                ) {
                                    sx[child1_state.index()][l_c1 * stride + r_c1] = candidate;
                                }
                            }
                        }
                    } else {
                        // Higher arity: general case
                        // For each child position p, enumerate sibling widths
                        for (p_pos, &p_child_idx) in children_order.iter().enumerate() {
                            let child_p_state = match rule.children.get(p_child_idx) {
                                Some(&s) if !s.is_stuck() => s,
                                _ => continue,
                            };

                            let siblings: Vec<(usize, StateId)> = children_order
                                .iter()
                                .enumerate()
                                .filter(|&(q_pos, _)| q_pos != p_pos)
                                .map(|(_, &q_child_idx)| {
                                    let q_state = rule
                                        .children
                                        .get(q_child_idx)
                                        .copied()
                                        .unwrap_or(StateId::STUCK);
                                    (q_child_idx, q_state)
                                })
                                .collect();

                            if siblings.iter().any(|(_, s)| s.is_stuck()) {
                                continue;
                            }

                            let sib_states: Vec<StateId> =
                                siblings.iter().map(|(_, s)| *s).collect();
                            let sib_mins: Vec<usize> =
                                sib_states.iter().map(|s| minwidth[s.index()]).collect();
                            if sib_mins.iter().any(|&m| m == INF) {
                                continue;
                            }
                            let sib_min_sum: usize = sib_mins.iter().sum();

                            let mwp = minwidth[child_p_state.index()];
                            let max_sibling_total = if mwp < INF {
                                remaining_for_children.saturating_sub(mwp)
                            } else {
                                remaining_for_children
                            };

                            if sib_min_sum > max_sibling_total {
                                continue;
                            }

                            let wl_p = tmpl.words_left_of_child(p_child_idx);
                            let wr_p = tmpl.words_right_of_child(p_child_idx);
                            let left_sibs = tmpl.children_left_of(p_child_idx);
                            let right_sibs = tmpl.children_right_of(p_child_idx);

                            // Enumerate sibling width assignments
                            enumerate_sibling_splits(
                                &sib_states,
                                &sib_mins,
                                sib_min_sum,
                                max_sibling_total,
                                &bi,
                                scorer,
                                &mut |sib_widths: &[usize], sib_bi_prod: f64| {
                                    // Map sibling widths back to left/right of p
                                    let mut wl_from_sibs = 0usize;
                                    let mut wr_from_sibs = 0usize;
                                    for (qi, &(q_child_idx, _)) in siblings.iter().enumerate() {
                                        if left_sibs.contains(&q_child_idx) {
                                            wl_from_sibs += sib_widths[qi];
                                        } else if right_sibs.contains(&q_child_idx) {
                                            wr_from_sibs += sib_widths[qi];
                                        }
                                    }
                                    let l_cp = l_a + wl_p + wl_from_sibs;
                                    let r_cp = r_a + wr_p + wr_from_sibs;
                                    if l_cp + r_cp > n {
                                        return;
                                    }
                                    let candidate = scorer.times(
                                        scorer.times(parent_sx, scorer.rule_score(rule.weight)),
                                        sib_bi_prod,
                                    );
                                    if scorer.better(
                                        candidate,
                                        sx[child_p_state.index()][l_cp * stride + r_cp],
                                    ) {
                                        sx[child_p_state.index()][l_cp * stride + r_cp] = candidate;
                                    }
                                },
                            );
                        }
                    }
                }
            }
        }

        let sx_boxed: Vec<Box<[f64]>> = sx.into_iter().map(|v| v.into_boxed_slice()).collect();

        SxHeuristic {
            sx: sx_boxed,
            n,
            stride,
            zero: scorer.zero(),
        }
    }

    /// Serialize to bytes. Format: magic(8) + n(8) + stride(8) + num_states(8) +
    /// for each state: row_len(8) + f64*row_len.  All integers are little-endian.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(b"SXCACH01");
        buf.extend_from_slice(&(self.n as u64).to_le_bytes());
        buf.extend_from_slice(&(self.stride as u64).to_le_bytes());
        buf.extend_from_slice(&self.zero.to_le_bytes());
        buf.extend_from_slice(&(self.sx.len() as u64).to_le_bytes());
        for row in &self.sx {
            buf.extend_from_slice(&(row.len() as u64).to_le_bytes());
            for &v in row.iter() {
                buf.extend_from_slice(&v.to_le_bytes());
            }
        }
        buf
    }

    /// Deserialize from bytes produced by [`Self::to_bytes`]. Returns `None` on any format error.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut pos = 0;
        let read_u64 = |bytes: &[u8], pos: &mut usize| -> Option<u64> {
            let b = bytes.get(*pos..*pos + 8)?;
            *pos += 8;
            Some(u64::from_le_bytes(b.try_into().ok()?))
        };
        if bytes.get(..8) != Some(b"SXCACH01") {
            return None;
        }
        pos += 8;
        let n = read_u64(bytes, &mut pos)? as usize;
        let stride = read_u64(bytes, &mut pos)? as usize;
        let b = bytes.get(pos..pos + 8)?;
        pos += 8;
        let zero = f64::from_le_bytes(b.try_into().ok()?);
        let num_states = read_u64(bytes, &mut pos)? as usize;
        let mut sx = Vec::with_capacity(num_states);
        for _ in 0..num_states {
            let row_len = read_u64(bytes, &mut pos)? as usize;
            let mut row = Vec::with_capacity(row_len);
            for _ in 0..row_len {
                let b = bytes.get(pos..pos + 8)?;
                pos += 8;
                row.push(f64::from_le_bytes(b.try_into().ok()?));
            }
            sx.push(row.into_boxed_slice());
        }
        Some(SxHeuristic {
            sx,
            n,
            stride,
            zero,
        })
    }
}

// ---------------------------------------------------------------------------
// UniversalSxHeuristic + SentenceSxHeuristic
// ---------------------------------------------------------------------------

/// A precomputed SX heuristic table that is admissible for all sentence lengths ≤ `n_max`.
///
/// `SX(X, l, r)` depends only on the number of words to the left (`l`) and right (`r`)
/// of the span, not on the total sentence length.  A table built for `n_max` contains every
/// `(l, r)` pair that can appear for any `n ≤ n_max`, so it can be reused across sentences
/// without recomputation.  Per-sentence use requires knowing `n` to recover `r = n - span.end`
/// from a [`Span`]; supply it via [`UniversalSxHeuristic::for_sentence`].
pub struct UniversalSxHeuristic {
    inner: SxHeuristic,
}

impl UniversalSxHeuristic {
    /// Build the universal SX heuristic for all sentence lengths up to `n_max`.
    pub fn new(grammar: &Explicit, hom: &Homomorphism, concat: Symbol, n_max: usize) -> Self {
        Self {
            inner: SxHeuristic::new(grammar, hom, concat, n_max),
        }
    }

    /// Build the universal SX heuristic using `scorer`.
    pub fn new_with<S: WeightScorer>(
        grammar: &Explicit,
        hom: &Homomorphism,
        concat: Symbol,
        n_max: usize,
        scorer: &S,
    ) -> Self {
        Self {
            inner: SxHeuristic::new_with(grammar, hom, concat, n_max, scorer),
        }
    }

    /// Maximum sentence length this table covers.
    pub fn n_max(&self) -> usize {
        self.inner.n
    }

    /// Zero-cost per-sentence adapter that supplies `n` to `outside_estimate`.
    pub fn for_sentence(&self, n: usize) -> SentenceSxHeuristic<'_> {
        SentenceSxHeuristic { table: self, n }
    }

    /// Serialize to bytes (same format as [`SxHeuristic::to_bytes`]).
    pub fn to_bytes(&self) -> Vec<u8> {
        self.inner.to_bytes()
    }

    /// Deserialize from bytes produced by [`Self::to_bytes`]. Returns `None` on any format error.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        SxHeuristic::from_bytes(bytes).map(|inner| Self { inner })
    }
}

/// Zero-cost per-sentence view into a [`UniversalSxHeuristic`] with a fixed sentence length `n`.
#[derive(Clone, Copy)]
pub struct SentenceSxHeuristic<'a> {
    table: &'a UniversalSxHeuristic,
    n: usize,
}

impl IntersectionHeuristic<StringDecompositionAutomaton> for SentenceSxHeuristic<'_> {
    fn outside_estimate(&self, left: StateId, span: &Span) -> f64 {
        let l = span.start;
        let r = self.n.saturating_sub(span.end);
        self.table.inner.lookup_lr(left, l, r)
    }
}

impl IntersectionHeuristic<InvHom<'_, StringDecompositionAutomaton>> for SentenceSxHeuristic<'_> {
    fn outside_estimate(&self, left: StateId, span: &Span) -> f64 {
        <Self as IntersectionHeuristic<StringDecompositionAutomaton>>::outside_estimate(
            self, left, span,
        )
    }
}

/// Recursively enumerate all width splits for multiple children, accumulating the product of BI values.
fn enumerate_splits(
    child_states: &[StateId],
    mins: &[usize],
    remaining: usize,
    pos: usize,
    acc: f64,
    rule_weight: f64,
    bi: &[Vec<f64>],
    scorer: &impl WeightScorer,
    out: &mut impl FnMut(f64),
) {
    if pos == child_states.len() {
        if remaining == 0 {
            out(scorer.times(scorer.rule_score(rule_weight), acc));
        }
        return;
    }
    let min_w = mins[pos];
    let max_w = {
        // The remaining children after pos need at least sum(mins[pos+1..]) words
        let rest_min: usize = mins[pos + 1..].iter().sum();
        remaining.saturating_sub(rest_min)
    };
    let state = child_states[pos];
    for w in min_w..=max_w {
        let child_bi = bi[state.index()][w];
        if child_bi == scorer.zero() {
            continue;
        }
        enumerate_splits(
            child_states,
            mins,
            remaining - w,
            pos + 1,
            scorer.times(acc, child_bi),
            rule_weight,
            bi,
            scorer,
            out,
        );
    }
}

/// Enumerate all sibling width assignments for the outside computation.
fn enumerate_sibling_splits(
    sib_states: &[StateId],
    sib_mins: &[usize],
    sib_min_sum: usize,
    max_total: usize,
    bi: &[Vec<f64>],
    scorer: &impl WeightScorer,
    out: &mut impl FnMut(&[usize], f64),
) {
    let k = sib_states.len();
    let mut widths = vec![0usize; k];
    let total_range = sib_min_sum..=max_total;
    for total in total_range {
        // Enumerate splits of `total` among k siblings with minimums sib_mins[i]
        enumerate_sibling_splits_inner(
            sib_states,
            sib_mins,
            total,
            0,
            &mut widths,
            scorer.one(),
            bi,
            scorer,
            out,
        );
    }
}

fn enumerate_sibling_splits_inner(
    sib_states: &[StateId],
    sib_mins: &[usize],
    remaining: usize,
    pos: usize,
    widths: &mut Vec<usize>,
    acc: f64,
    bi: &[Vec<f64>],
    scorer: &impl WeightScorer,
    out: &mut impl FnMut(&[usize], f64),
) {
    if pos == sib_states.len() {
        if remaining == 0 {
            out(widths, acc);
        }
        return;
    }
    let min_w = sib_mins[pos];
    let rest_min: usize = sib_mins[pos + 1..].iter().sum();
    let max_w = remaining.saturating_sub(rest_min);
    let state = sib_states[pos];
    for w in min_w..=max_w {
        let child_bi = bi[state.index()][w];
        if child_bi == scorer.zero() {
            continue;
        }
        widths[pos] = w;
        enumerate_sibling_splits_inner(
            sib_states,
            sib_mins,
            remaining - w,
            pos + 1,
            widths,
            scorer.times(acc, child_bi),
            bi,
            scorer,
            out,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn span_product_sibling_finder_returns_adjacent_products_in_both_directions() {
        let left_product = StateId(10);
        let right_product = StateId(11);
        let left_state = StateId(0);
        let right_state = StateId(1);
        let left_span = Span::new(0, 1);
        let right_span = Span::new(1, 3);

        let mut finder = SpanProductSiblingFinder::default();
        assert!(finder.activate(right_product, right_state, StateId(21), right_span, 1));

        let mut products = Vec::new();
        finder.sibling_products_into(left_span, 0, right_state, &mut products);
        assert_eq!(
            products,
            vec![SpanProductSibling {
                product: right_product,
                right_state: StateId(21)
            }]
        );

        let mut finder = SpanProductSiblingFinder::default();
        assert!(finder.activate(left_product, left_state, StateId(20), left_span, 0));

        products.clear();
        finder.sibling_products_into(right_span, 1, left_state, &mut products);
        assert_eq!(
            products,
            vec![SpanProductSibling {
                product: left_product,
                right_state: StateId(20)
            }]
        );
    }

    #[test]
    fn span_product_sibling_finder_filters_by_left_state_and_activation() {
        let product = StateId(10);
        let wanted_left = StateId(0);
        let other_left = StateId(1);
        let right_state = StateId(20);

        let mut finder = SpanProductSiblingFinder::default();
        let mut products = Vec::new();
        finder.sibling_products_into(Span::new(0, 1), 0, wanted_left, &mut products);
        assert!(products.is_empty());

        assert!(finder.activate(product, other_left, right_state, Span::new(1, 3), 1));
        finder.sibling_products_into(Span::new(0, 1), 0, wanted_left, &mut products);
        assert!(products.is_empty());

        finder.sibling_products_into(Span::new(0, 1), 0, other_left, &mut products);
        assert_eq!(
            products,
            vec![SpanProductSibling {
                product,
                right_state
            }]
        );
    }

    #[test]
    fn span_product_sibling_finder_activation_is_idempotent_per_position() {
        let product = StateId(10);
        let left = StateId(0);
        let right = StateId(20);
        let span = Span::new(0, 1);

        let mut finder = SpanProductSiblingFinder::default();
        assert!(finder.activate(product, left, right, span, 0));
        assert!(!finder.activate(product, left, right, span, 0));
        assert!(finder.activate(product, left, right, span, 1));
        assert!(!finder.activate(product, left, right, span, 1));
    }

    #[test]
    fn span_product_sibling_finder_separates_products_with_same_right_span() {
        let left_a = StateId(0);
        let left_b = StateId(1);
        let product_a = StateId(10);
        let product_b = StateId(11);
        let span = Span::new(1, 2);

        let mut finder = SpanProductSiblingFinder::default();
        assert!(finder.activate(product_a, left_a, StateId(20), span, 1));
        assert!(finder.activate(product_b, left_b, StateId(21), span, 1));

        let mut products = Vec::new();
        finder.sibling_products_into(Span::new(0, 1), 0, left_a, &mut products);
        assert_eq!(
            products,
            vec![SpanProductSibling {
                product: product_a,
                right_state: StateId(20)
            }]
        );

        finder.sibling_products_into(Span::new(0, 1), 0, left_b, &mut products);
        assert_eq!(
            products,
            vec![SpanProductSibling {
                product: product_b,
                right_state: StateId(21)
            }]
        );
    }

    #[test]
    fn lexical_lookup_handles_repeated_words() {
        let mut alg = StringAlgebra::new();
        let a = alg.intern_word("a");
        let b = alg.intern_word("b");
        let decomp = alg.decompose(vec![a, b, a]);

        let mut spans = Vec::new();
        decomp.step(a, &[], &mut |q| spans.push(q));
        assert_eq!(spans, vec![Span::new(0, 1), Span::new(2, 3)]);
    }

    #[test]
    fn concat_requires_adjacency() {
        let mut alg = StringAlgebra::new();
        let a = alg.intern_word("a");
        let decomp = alg.decompose(vec![a, a, a]);
        let concat = alg.concat_symbol();

        let mut ok = Vec::new();
        decomp.step(concat, &[Span::new(0, 1), Span::new(1, 3)], &mut |q| {
            ok.push(q)
        });
        assert_eq!(ok, vec![Span::new(0, 3)]);

        let mut bad = Vec::new();
        decomp.step(concat, &[Span::new(0, 1), Span::new(2, 3)], &mut |q| {
            bad.push(q)
        });
        assert!(bad.is_empty());
    }

    #[test]
    fn universe_is_callback_enumerated() {
        let mut alg = StringAlgebra::new();
        let a = alg.intern_word("a");
        let decomp = alg.decompose(vec![a, a, a, a]);

        let mut count = 0;
        decomp.all_states(&mut |_| count += 1);
        assert_eq!(count, 10);
    }

    #[test]
    fn condensed_rule_count_matches_cky_formula() {
        let mut alg = StringAlgebra::new();
        let a = alg.intern_word("a");
        let decomp = alg.decompose(vec![a, a, a, a]);

        let mut count = 0;
        decomp.condensed_rules(&mut |_, _, _| count += 1);
        assert_eq!(count, decomp.rule_count());
    }

    #[test]
    fn indexed_condensed_rules_by_child_enumerates_adjacent_spans() {
        let mut alg = StringAlgebra::new();
        let a = alg.intern_word("a");
        let decomp = alg.decompose(vec![a, a, a]);

        let mut rules = Vec::new();
        decomp.condensed_rules_by_child(0, &Span::new(0, 1), &mut |children, symbols, result| {
            rules.push((children.to_vec(), symbols.clone(), result));
        });

        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0].0, vec![Span::new(0, 1), Span::new(1, 2)]);
        assert_eq!(rules[0].2, Span::new(0, 2));
        assert_eq!(rules[1].0, vec![Span::new(0, 1), Span::new(1, 3)]);
        assert_eq!(rules[1].2, Span::new(0, 3));
        assert!(
            rules
                .iter()
                .all(|(_, symbols, _)| { symbols.contains(decomp.concat_symbol()) })
        );
    }

    // -----------------------------------------------------------------------
    // SxHeuristic tests
    // -----------------------------------------------------------------------

    /// Build a tiny grammar and homomorphism for tests.
    ///
    /// Grammar (binarized):
    ///   S -> A B   w=0.9   (homomorphism: concat(x0, x1))
    ///   A -> "a"   w=0.8   (homomorphism: a_word)
    ///   B -> "b"   w=0.7   (homomorphism: b_word)
    ///
    /// States: s_A=0, s_B=1, s_S=2 (accepting)
    ///
    /// For sentence ["a", "b"] (n=2):
    ///   BI(s_A, 1) = 0.8 (lexical)
    ///   BI(s_B, 1) = 0.7 (lexical)
    ///   BI(s_S, 2) = 0.9 * BI(s_A, 1) * BI(s_B, 1) = 0.9 * 0.8 * 0.7 = 0.504
    ///   SX(s_S, 0, 0) = 1.0 (accepting)
    ///   SX(s_A, 0, 1) = SX(s_S, 0, 0) * 0.9 * BI(s_B, 1) = 1.0 * 0.9 * 0.7 = 0.63
    ///   SX(s_B, 1, 0) = SX(s_S, 0, 0) * 0.9 * BI(s_A, 1) = 1.0 * 0.9 * 0.8 = 0.72
    fn build_tiny_grammar_and_hom() -> (
        crate::Explicit,
        crate::Homomorphism,
        Symbol,
        crate::StateId,
        crate::StateId,
        crate::StateId,
    ) {
        use crate::ExplicitBuilder;

        let mut hom_arena = rusty_tree::tree::TreeArena::new();

        // Build word symbols and concat
        let mut sig = crate::Signature::new();
        let concat = sig.intern("*".to_owned(), 2).unwrap();
        let sym_a = sig.intern("a".to_owned(), 0).unwrap();
        let sym_b = sig.intern("b".to_owned(), 0).unwrap();
        // Grammar symbols (S, A, B) - we'll reuse the same symbol ids for simplicity
        // The grammar uses Symbol values; the homomorphism maps grammar symbols to string terms.
        // Let's define grammar symbols as:
        //   g_AB = Symbol(10), g_A = Symbol(11), g_B = Symbol(12)
        let g_ab = Symbol(10); // S -> A B
        let g_a = Symbol(11); // A -> "a"
        let g_b = Symbol(12); // B -> "b"

        // Homomorphism terms:
        // g_ab(x0, x1) -> concat(x0, x1)
        let v0 = hom_arena.add_node(HomLabel::Var(0), vec![]);
        let v1 = hom_arena.add_node(HomLabel::Var(1), vec![]);
        let concat_term = hom_arena.add_node(HomLabel::Symbol(concat), vec![v0, v1]);
        // g_a() -> a_word
        let a_word_term = hom_arena.add_node(HomLabel::Symbol(sym_a), vec![]);
        // g_b() -> b_word
        let b_word_term = hom_arena.add_node(HomLabel::Symbol(sym_b), vec![]);

        let mut hom = Homomorphism::with_arena(hom_arena);
        hom.add(g_ab, 2, concat_term).unwrap();
        hom.add(g_a, 0, a_word_term).unwrap();
        hom.add(g_b, 0, b_word_term).unwrap();

        // Grammar automaton
        let mut b = ExplicitBuilder::new();
        let s_a = b.new_state(); // index 0
        let s_b = b.new_state(); // index 1
        let s_s = b.new_state(); // index 2, accepting

        b.add_weighted_rule(g_a, vec![], s_a, 0.8);
        b.add_weighted_rule(g_b, vec![], s_b, 0.7);
        b.add_weighted_rule(g_ab, vec![s_a, s_b], s_s, 0.9);
        b.add_accepting(s_s);

        (b.build(), hom, concat, s_a, s_b, s_s)
    }

    #[test]
    fn sx_heuristic_bi_and_sx_values_match_hand_computation() {
        let (grammar, hom, concat, s_a, s_b, s_s) = build_tiny_grammar_and_hom();
        let universal = UniversalSxHeuristic::new(&grammar, &hom, concat, 2);
        let h = universal.for_sentence(2);

        // outside_estimate(s_A, span=[0,1]): l=0, r=2-1=1 -> SX(s_A, 0, 1)
        let est_a = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
            StringDecompositionAutomaton,
        >>::outside_estimate(&h, s_a, &Span::new(0, 1));
        let expected_a = 0.9 * 0.7; // SX(s_S,0,0)*w_rule*BI(s_B,1)
        assert!(
            (est_a - expected_a).abs() < 1e-9,
            "SX(s_A, 0, 1) = {est_a}, expected {expected_a}"
        );

        // outside_estimate(s_B, span=[1,2]): l=1, r=2-2=0 -> SX(s_B, 1, 0)
        let est_b = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
            StringDecompositionAutomaton,
        >>::outside_estimate(&h, s_b, &Span::new(1, 2));
        let expected_b = 0.9 * 0.8; // SX(s_S,0,0)*w_rule*BI(s_A,1)
        assert!(
            (est_b - expected_b).abs() < 1e-9,
            "SX(s_B, 1, 0) = {est_b}, expected {expected_b}"
        );

        // outside_estimate(s_S, span=[0,2]): l=0, r=0 -> SX(s_S, 0, 0) = 1.0
        let est_s = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
            StringDecompositionAutomaton,
        >>::outside_estimate(&h, s_s, &Span::new(0, 2));
        assert!(
            (est_s - 1.0).abs() < 1e-9,
            "SX(s_S, 0, 0) = {est_s}, expected 1.0"
        );
    }

    #[test]
    fn sx_heuristic_outside_returns_zero_for_impossible_spans() {
        let (grammar, hom, concat, s_a, _s_b, _s_s) = build_tiny_grammar_and_hom();
        let universal = UniversalSxHeuristic::new(&grammar, &hom, concat, 2);
        let h = universal.for_sentence(2);

        // s_A cannot appear in a span of width 0 (minwidth=1), so contexts where
        // n-l-r < 1 should give 0.
        // span=[0,0]: l=0, r=2, l+r=2=n -> parent width 0, can't fit s_A
        let est = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
            StringDecompositionAutomaton,
        >>::outside_estimate(&h, s_a, &Span::new(0, 0));
        assert_eq!(est, 0.0, "SX(s_A, 0, 2) should be 0 (no room)");
    }

    #[test]
    fn universal_sx_covers_shorter_sentences() {
        // A table built for n_max=3 must give the same estimates as one built for n=2
        // when used via for_sentence(2).
        let (grammar, hom, concat, s_a, s_b, _s_s) = build_tiny_grammar_and_hom();
        let universal = UniversalSxHeuristic::new(&grammar, &hom, concat, 3);
        let h2 = universal.for_sentence(2);
        let universal_direct = UniversalSxHeuristic::new(&grammar, &hom, concat, 2);
        let h2_direct = universal_direct.for_sentence(2);

        for (state, span) in [(s_a, Span::new(0, 1)), (s_b, Span::new(1, 2))] {
            let via_universal = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
                StringDecompositionAutomaton,
            >>::outside_estimate(&h2, state, &span);
            let direct = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
                StringDecompositionAutomaton,
            >>::outside_estimate(&h2_direct, state, &span);
            assert!(
                (via_universal - direct).abs() < 1e-12,
                "universal(n_max=3).for_sentence(2) != direct(n=2) for state {:?} span {:?}: {} vs {}",
                state,
                span,
                via_universal,
                direct
            );
        }
    }
}
