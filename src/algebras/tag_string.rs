//! TAG string algebra and its lazy decomposition automaton.
//!
//! The domain has two sorts: ordinary strings and pairs of strings separated
//! by a gap. Operations use the reserved names from Alto's TAG algebra.

use super::{Algebra, Span};
use crate::{
    BottomUpTa, CondensedTa, FxHashMap, IndexedBottomUpTa, Signature, StateUniverse, Symbol,
    SymbolSet, TopDownTa,
};
use std::{convert::Infallible, fmt};

/// Concatenate two ordinary strings.
pub const CONC11: &str = "*CONC11*";
/// Prefix a string to the left component of a string pair.
pub const CONC12: &str = "*CONC12*";
/// Append a string to the right component of a string pair.
pub const CONC21: &str = "*CONC21*";
/// Fill the gap of a string pair with an ordinary string.
pub const WRAP21: &str = "*WRAP21*";
/// Insert one string pair into the gap of another.
pub const WRAP22: &str = "*WRAP22*";
/// Constant denoting the empty ordinary string.
pub const TAG_E: &str = "*E*";
/// Constant denoting a pair of empty strings.
pub const TAG_EE: &str = "*EE*";

/// A TAG string-algebra value: either one contiguous string or a pair of strings.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TagStringValue<T> {
    /// One contiguous string.
    String(Vec<T>),
    /// Material to the left and right of one gap.
    Pair(Vec<T>, Vec<T>),
}

impl<T: fmt::Display> fmt::Display for TagStringValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn words<T: fmt::Display>(f: &mut fmt::Formatter<'_>, values: &[T]) -> fmt::Result {
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    f.write_str(" ")?;
                }
                write!(f, "{value}")?;
            }
            Ok(())
        }

        match self {
            Self::String(value) => words(f, value),
            Self::Pair(left, right) => {
                f.write_str("[")?;
                words(f, left)?;
                f.write_str(" / ")?;
                words(f, right)?;
                f.write_str("]")
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Operation {
    Conc11,
    Conc12,
    Conc21,
    Wrap21,
    Wrap22,
    E,
    Ee,
}

/// Alto-compatible TAG string algebra.
#[derive(Clone, Debug)]
pub struct TagStringAlgebra {
    signature: Signature,
    operations: FxHashMap<Symbol, Operation>,
}

impl TagStringAlgebra {
    /// Construct an algebra containing all reserved TAG operations.
    pub fn new() -> Self {
        Self::with_signature(Signature::new())
    }

    /// Construct an algebra over an existing target signature.
    pub fn with_signature(mut signature: Signature) -> Self {
        let mut operations = FxHashMap::default();
        for (name, arity, operation) in [
            (CONC11, 2, Operation::Conc11),
            (CONC12, 2, Operation::Conc12),
            (CONC21, 2, Operation::Conc21),
            (WRAP21, 2, Operation::Wrap21),
            (WRAP22, 2, Operation::Wrap22),
            (TAG_E, 0, Operation::E),
            (TAG_EE, 0, Operation::Ee),
        ] {
            let symbol = signature.intern(name.to_owned(), arity).unwrap();
            operations.insert(symbol, operation);
        }
        Self {
            signature,
            operations,
        }
    }

    /// Intern a nullary lexical symbol.
    pub fn intern_word(&mut self, word: impl Into<String>) -> Symbol {
        self.signature.intern(word.into(), 0).unwrap()
    }

    /// Resolve an operation or lexical symbol by name.
    pub fn operation_symbol(&self, name: &str) -> Option<Symbol> {
        self.signature.get(name)
    }

    /// Parse whitespace-separated tokens as a contiguous string.
    pub fn parse_string(&mut self, input: &str) -> TagStringValue<Symbol> {
        TagStringValue::String(
            input
                .split_whitespace()
                .map(|word| self.intern_word(word.to_owned()))
                .collect(),
        )
    }

    /// Build a lazy decomposition for a contiguous input string.
    ///
    /// Complete string-pair values are not parse inputs, matching Alto.
    pub fn decompose(
        &self,
        value: TagStringValue<Symbol>,
    ) -> Option<TagStringDecompositionAutomaton> {
        let TagStringValue::String(words) = value else {
            return None;
        };
        Some(TagStringDecompositionAutomaton::new(
            self.operations.clone(),
            words,
        ))
    }
}

impl Default for TagStringAlgebra {
    fn default() -> Self {
        Self::new()
    }
}

fn append<T: Clone>(left: &[T], right: &[T]) -> Vec<T> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    result.extend_from_slice(left);
    result.extend_from_slice(right);
    result
}

impl Algebra for TagStringAlgebra {
    type InternalValue = TagStringValue<Symbol>;
    type Value = TagStringValue<String>;
    type ParseError = Infallible;

    fn signature(&self) -> &Signature {
        &self.signature
    }

    fn evaluate(
        &self,
        symbol: Symbol,
        children: &[Self::InternalValue],
    ) -> Option<Self::InternalValue> {
        use TagStringValue::{Pair, String as One};
        match self.operations.get(&symbol).copied() {
            Some(Operation::Conc11) => match children {
                [One(left), One(right)] => Some(One(append(left, right))),
                _ => None,
            },
            Some(Operation::Conc12) => match children {
                [One(first), Pair(left, right)] => Some(Pair(append(first, left), right.clone())),
                _ => None,
            },
            Some(Operation::Conc21) => match children {
                [Pair(left, right), One(second)] => Some(Pair(left.clone(), append(right, second))),
                _ => None,
            },
            Some(Operation::Wrap21) => match children {
                [Pair(left, right), One(middle)] => Some(One(append(&append(left, middle), right))),
                _ => None,
            },
            Some(Operation::Wrap22) => match children {
                [
                    Pair(first_left, first_right),
                    Pair(second_left, second_right),
                ] => Some(Pair(
                    append(first_left, second_left),
                    append(second_right, first_right),
                )),
                _ => None,
            },
            Some(Operation::E) if children.is_empty() => Some(One(Vec::new())),
            Some(Operation::Ee) if children.is_empty() => Some(Pair(Vec::new(), Vec::new())),
            Some(_) => None,
            None if children.is_empty() => Some(One(vec![symbol])),
            None => None,
        }
    }

    fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError> {
        Ok(self.parse_string(input))
    }

    fn to_external(&self, value: &Self::InternalValue) -> Self::Value {
        let resolve = |values: &[Symbol]| {
            values
                .iter()
                .map(|&symbol| self.signature.resolve(symbol).to_owned())
                .collect()
        };
        match value {
            TagStringValue::String(words) => TagStringValue::String(resolve(words)),
            TagStringValue::Pair(left, right) => {
                TagStringValue::Pair(resolve(left), resolve(right))
            }
        }
    }
}

/// A TAG string decomposition state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TagSpan {
    /// One half-open input span.
    String(Span),
    /// Two ordered, non-overlapping half-open spans.
    Pair(Span, Span),
}

impl TagSpan {
    fn valid(self, n: usize) -> bool {
        match self {
            Self::String(span) => span.start <= span.end && span.end <= n,
            Self::Pair(left, right) => {
                left.start <= left.end
                    && left.end <= right.start
                    && right.start <= right.end
                    && right.end <= n
            }
        }
    }
}

/// Lazy decomposition automaton for a fixed TAG string value.
#[derive(Clone, Debug)]
pub struct TagStringDecompositionAutomaton {
    operations: FxHashMap<Symbol, Operation>,
    words: Vec<Symbol>,
    positions_by_word: FxHashMap<Symbol, Vec<usize>>,
}

impl TagStringDecompositionAutomaton {
    fn new(operations: FxHashMap<Symbol, Operation>, words: Vec<Symbol>) -> Self {
        let mut positions_by_word = FxHashMap::default();
        for (position, &word) in words.iter().enumerate() {
            positions_by_word
                .entry(word)
                .or_insert_with(Vec::new)
                .push(position);
        }
        Self {
            operations,
            words,
            positions_by_word,
        }
    }

    /// Return the number of tokens in the fixed input.
    pub fn len(&self) -> usize {
        self.words.len()
    }

    /// Return whether the fixed input is empty.
    pub fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    fn operation(&self, symbol: Symbol) -> Option<Operation> {
        self.operations.get(&symbol).copied()
    }

    fn symbol_for(&self, operation: Operation) -> Symbol {
        self.operations
            .iter()
            .find_map(|(&symbol, &candidate)| (candidate == operation).then_some(symbol))
            .expect("all TAG operations are registered")
    }

    fn step_operation(
        &self,
        operation: Operation,
        children: &[TagSpan],
        out: &mut dyn FnMut(TagSpan),
    ) {
        use TagSpan::{Pair, String as One};
        match (operation, children) {
            (Operation::Conc11, [One(left), One(right)]) if left.end == right.start => {
                out(One(Span::new(left.start, right.end)));
            }
            (Operation::Conc12, [One(first), Pair(left, right)]) if first.end == left.start => {
                out(Pair(Span::new(first.start, left.end), *right));
            }
            (Operation::Conc21, [Pair(left, right), One(second)]) if right.end == second.start => {
                out(Pair(*left, Span::new(right.start, second.end)));
            }
            (Operation::Wrap21, [Pair(left, right), One(middle)])
                if left.end == middle.start && middle.end == right.start =>
            {
                out(One(Span::new(left.start, right.end)));
            }
            (
                Operation::Wrap22,
                [
                    Pair(first_left, first_right),
                    Pair(second_left, second_right),
                ],
            ) if first_left.end == second_left.start && second_right.end == first_right.start => {
                out(Pair(
                    Span::new(first_left.start, second_left.end),
                    Span::new(second_right.start, first_right.end),
                ));
            }
            (Operation::E, []) => {
                for i in 0..=self.len() {
                    out(One(Span::new(i, i)));
                }
            }
            (Operation::Ee, []) => {
                for i in 0..=self.len() {
                    for j in i..=self.len() {
                        out(Pair(Span::new(i, i), Span::new(j, j)));
                    }
                }
            }
            _ => {}
        }
    }
}

impl BottomUpTa for TagStringDecompositionAutomaton {
    type State = TagSpan;

    fn step(&self, symbol: Symbol, children: &[TagSpan], out: &mut dyn FnMut(TagSpan)) {
        if let Some(operation) = self.operation(symbol) {
            self.step_operation(operation, children, &mut |state| {
                if state.valid(self.len()) {
                    out(state);
                }
            });
        } else if children.is_empty()
            && let Some(positions) = self.positions_by_word.get(&symbol)
        {
            for &position in positions {
                out(TagSpan::String(Span::new(position, position + 1)));
            }
        }
    }

    fn is_accepting(&self, state: &TagSpan) -> bool {
        *state == TagSpan::String(Span::new(0, self.len()))
    }
}

impl StateUniverse for TagStringDecompositionAutomaton {
    fn all_states(&self, out: &mut dyn FnMut(TagSpan)) {
        let n = self.len();
        for start in 0..=n {
            for end in start..=n {
                out(TagSpan::String(Span::new(start, end)));
            }
        }
        for i in 0..=n {
            for j in i..=n {
                for k in j..=n {
                    for l in k..=n {
                        out(TagSpan::Pair(Span::new(i, j), Span::new(k, l)));
                    }
                }
            }
        }
    }
}

impl TopDownTa for TagStringDecompositionAutomaton {
    fn step_topdown(&self, parent: &TagSpan, out: &mut dyn FnMut(Symbol, &[TagSpan])) {
        use TagSpan::{Pair, String as One};
        if !parent.valid(self.len()) {
            return;
        }

        match *parent {
            One(span) => {
                if span.len() == 1 {
                    out(self.words[span.start], &[]);
                }
                if span.is_empty() {
                    out(self.symbol_for(Operation::E), &[]);
                }
                for split in span.start..=span.end {
                    let children = [
                        One(Span::new(span.start, split)),
                        One(Span::new(split, span.end)),
                    ];
                    out(self.symbol_for(Operation::Conc11), &children);
                }
                for start in span.start..=span.end {
                    for end in start..=span.end {
                        let children = [
                            Pair(Span::new(span.start, start), Span::new(end, span.end)),
                            One(Span::new(start, end)),
                        ];
                        out(self.symbol_for(Operation::Wrap21), &children);
                    }
                }
            }
            Pair(left, right) => {
                if left.is_empty() && right.is_empty() {
                    out(self.symbol_for(Operation::Ee), &[]);
                }
                for split in left.start..=left.end {
                    let children = [
                        One(Span::new(left.start, split)),
                        Pair(Span::new(split, left.end), right),
                    ];
                    out(self.symbol_for(Operation::Conc12), &children);
                }
                for split in right.start..=right.end {
                    let children = [
                        Pair(left, Span::new(right.start, split)),
                        One(Span::new(split, right.end)),
                    ];
                    out(self.symbol_for(Operation::Conc21), &children);
                }
                for split_left in left.start..=left.end {
                    for split_right in right.start..=right.end {
                        let children = [
                            Pair(
                                Span::new(left.start, split_left),
                                Span::new(split_right, right.end),
                            ),
                            Pair(
                                Span::new(split_left, left.end),
                                Span::new(right.start, split_right),
                            ),
                        ];
                        out(self.symbol_for(Operation::Wrap22), &children);
                    }
                }
            }
        }
    }

    fn initial_states(&self, out: &mut dyn FnMut(TagSpan)) {
        out(TagSpan::String(Span::new(0, self.len())));
    }
}

impl CondensedTa for TagStringDecompositionAutomaton {
    fn condensed_rules(&self, out: &mut dyn FnMut(&[TagSpan], &SymbolSet, TagSpan)) {
        self.all_states(&mut |state| {
            self.step_topdown(&state, &mut |symbol, children| {
                let mut symbols = SymbolSet::new();
                symbols.insert(symbol);
                out(children, &symbols, state);
            });
        });
    }

    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, TagSpan)) {
        for (position, &word) in self.words.iter().enumerate() {
            let mut symbols = SymbolSet::new();
            symbols.insert(word);
            out(&symbols, TagSpan::String(Span::new(position, position + 1)));
        }
        let mut e = SymbolSet::new();
        e.insert(self.symbol_for(Operation::E));
        for i in 0..=self.len() {
            out(&e, TagSpan::String(Span::new(i, i)));
        }
        let mut ee = SymbolSet::new();
        ee.insert(self.symbol_for(Operation::Ee));
        for i in 0..=self.len() {
            for j in i..=self.len() {
                out(&ee, TagSpan::Pair(Span::new(i, i), Span::new(j, j)));
            }
        }
    }

    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &TagSpan,
        out: &mut dyn FnMut(&[TagSpan], &SymbolSet, TagSpan),
    ) {
        if position > 1 {
            return;
        }
        self.all_states(&mut |parent| {
            self.step_topdown(&parent, &mut |symbol, children| {
                if children.get(position) == Some(state) {
                    let mut symbols = SymbolSet::new();
                    symbols.insert(symbol);
                    out(children, &symbols, parent);
                }
            });
        });
    }
}

impl IndexedBottomUpTa for TagStringDecompositionAutomaton {
    fn step_partial(
        &self,
        symbol: Symbol,
        position: usize,
        state_at_position: &TagSpan,
        out: &mut dyn FnMut(&[TagSpan], TagSpan),
    ) {
        let Some(operation) = self.operation(symbol) else {
            return;
        };
        if !matches!(
            operation,
            Operation::Conc11
                | Operation::Conc12
                | Operation::Conc21
                | Operation::Wrap21
                | Operation::Wrap22
        ) || position > 1
        {
            return;
        }

        self.all_states(&mut |partner| {
            let children = if position == 0 {
                [*state_at_position, partner]
            } else {
                [partner, *state_at_position]
            };
            self.step_operation(operation, &children, &mut |parent| {
                if parent.valid(self.len()) {
                    out(&children, parent);
                }
            });
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluates_all_operations() {
        let mut algebra = TagStringAlgebra::new();
        let a = TagStringValue::String(vec![algebra.intern_word("a")]);
        let b = TagStringValue::String(vec![algebra.intern_word("b")]);
        let pair = TagStringValue::Pair(
            vec![algebra.intern_word("l")],
            vec![algebra.intern_word("r")],
        );

        let eval = |name, children: &[TagStringValue<Symbol>]| {
            algebra.evaluate(algebra.operation_symbol(name).unwrap(), children)
        };
        assert!(
            matches!(eval(CONC11, &[a.clone(), b.clone()]), Some(TagStringValue::String(v)) if v.len() == 2)
        );
        assert!(
            matches!(eval(CONC12, &[a.clone(), pair.clone()]), Some(TagStringValue::Pair(l, r)) if l.len() == 2 && r.len() == 1)
        );
        assert!(
            matches!(eval(CONC21, &[pair.clone(), b.clone()]), Some(TagStringValue::Pair(l, r)) if l.len() == 1 && r.len() == 2)
        );
        assert!(
            matches!(eval(WRAP21, &[pair.clone(), b.clone()]), Some(TagStringValue::String(v)) if v.len() == 3)
        );
        assert!(
            matches!(eval(WRAP22, &[pair.clone(), pair.clone()]), Some(TagStringValue::Pair(l, r)) if l.len() == 2 && r.len() == 2)
        );
    }

    #[test]
    fn decomposition_accepts_empty_and_repeated_words() {
        let mut algebra = TagStringAlgebra::new();
        let value = algebra.parse_string("a a");
        let decomp = algebra.decompose(value).unwrap();
        let a = algebra.signature().get("a").unwrap();
        let mut states = Vec::new();
        decomp.step(a, &[], &mut |state| states.push(state));
        assert_eq!(states.len(), 2);

        let empty_value = algebra.parse_string("");
        let empty = algebra.decompose(empty_value).unwrap();
        let e = algebra.operation_symbol(TAG_E).unwrap();
        let mut empty_states = Vec::new();
        empty.step(e, &[], &mut |state| empty_states.push(state));
        assert!(empty_states.iter().any(|state| empty.is_accepting(state)));
    }
}
