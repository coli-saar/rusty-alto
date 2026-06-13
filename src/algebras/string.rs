use super::Algebra;
use crate::{
    BottomUpTa, CondensedTa, FxHashMap, IndexedBottomUpTa, Signature, StateUniverse, Symbol,
    SymbolSet, TopDownTa,
};
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
