use crate::{Explicit, ExplicitBuilder, FxHashMap, Interner, StateId, Symbol};
use std::fmt;
use thiserror::Error;

/// Parsed Alto tree automaton.
///
/// Alto's `.auto` format writes rules top-down, for example
/// `S! -> f(A,A) [1.0]`. This reader builds the equivalent bottom-up
/// [`Explicit`] automaton, i.e. the rule above becomes `f(A,A) -> S`.
///
/// The current core automaton is unweighted, so weights are stored in
/// [`AltoAutomaton::rules`] as metadata.
#[derive(Clone, Debug)]
pub struct AltoAutomaton {
    /// Bottom-up explicit automaton built from the Alto rules.
    pub automaton: Explicit,
    /// Mapping from Alto state names to dense state IDs.
    pub states: Interner<String>,
    /// Mapping from Alto terminal symbols to symbol IDs.
    pub signature: AltoSignature,
    /// Parsed rules, including source names and weights.
    pub rules: Vec<AltoRule>,
}

/// String signature used while reading Alto files.
#[derive(Clone, Debug, Default)]
pub struct AltoSignature {
    names: Vec<String>,
    ids: FxHashMap<String, Symbol>,
    arities: FxHashMap<Symbol, usize>,
}

impl AltoSignature {
    /// Create an empty signature.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the symbol ID for a name, inserting it if needed.
    pub fn intern(&mut self, name: String, arity: usize) -> Result<Symbol, AltoParseError> {
        if let Some(&symbol) = self.ids.get(&name) {
            let old_arity = self.arities[&symbol];
            if old_arity != arity {
                return Err(AltoParseError::ArityMismatch {
                    symbol: name,
                    first: old_arity,
                    second: arity,
                });
            }
            return Ok(symbol);
        }

        let id = u32::try_from(self.names.len()).expect("too many symbols for Symbol");
        let symbol = Symbol(id);
        self.names.push(name.clone());
        self.ids.insert(name, symbol);
        self.arities.insert(symbol, arity);
        Ok(symbol)
    }

    /// Look up a symbol ID by name.
    pub fn get(&self, name: &str) -> Option<Symbol> {
        self.ids.get(name).copied()
    }

    /// Resolve a symbol ID back to its Alto name.
    pub fn resolve(&self, symbol: Symbol) -> &str {
        &self.names[symbol.0 as usize]
    }

    /// Return the arity recorded for a symbol.
    pub fn arity(&self, symbol: Symbol) -> usize {
        self.arities[&symbol]
    }

    /// Number of terminal symbols in the signature.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Return whether the signature is empty.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

/// One rule parsed from an Alto file.
#[derive(Clone, Debug, PartialEq)]
pub struct AltoRule {
    /// Parent state on the left-hand side of the Alto rule.
    pub parent: StateId,
    /// Terminal symbol on the right-hand side.
    pub symbol: Symbol,
    /// Child states inside the symbol term.
    pub children: Vec<StateId>,
    /// Rule weight, defaulting to `1.0` when omitted.
    pub weight: f64,
    /// Original Alto parent-state name.
    pub parent_name: String,
    /// Original Alto terminal-symbol name.
    pub symbol_name: String,
    /// Original Alto child-state names.
    pub child_names: Vec<String>,
}

/// Error returned when parsing Alto `.auto` input.
#[derive(Clone, Debug, Error, PartialEq)]
pub enum AltoParseError {
    /// A token was expected but not found.
    #[error("expected {expected} at byte {offset}")]
    Expected {
        /// Human-readable token description.
        expected: &'static str,
        /// Byte offset in the input.
        offset: usize,
    },
    /// An unexpected token was found.
    #[error("unexpected token {found:?} at byte {offset}; expected {expected}")]
    Unexpected {
        /// Human-readable expected token description.
        expected: &'static str,
        /// Token that was found.
        found: String,
        /// Byte offset in the input.
        offset: usize,
    },
    /// A quoted name reached end-of-file before the closing quote.
    #[error("unterminated quoted name starting at byte {offset}")]
    UnterminatedQuote {
        /// Byte offset where the quote started.
        offset: usize,
    },
    /// A block comment reached end-of-file before `*/`.
    #[error("unterminated block comment starting at byte {offset}")]
    UnterminatedComment {
        /// Byte offset where the comment started.
        offset: usize,
    },
    /// A weight could not be parsed as `f64`.
    #[error("invalid weight {text:?} at byte {offset}")]
    InvalidWeight {
        /// Weight text inside brackets.
        text: String,
        /// Byte offset where the weight started.
        offset: usize,
    },
    /// One terminal symbol was used with two arities.
    #[error("symbol {symbol:?} used with arities {first} and {second}")]
    ArityMismatch {
        /// Terminal symbol name.
        symbol: String,
        /// First observed arity.
        first: usize,
        /// Later conflicting arity.
        second: usize,
    },
}

/// Parse an Alto `.auto` file into a bottom-up explicit automaton.
///
/// Supported syntax follows Alto's `auto` codec:
///
/// - rules: `State! -> label(Child1, Child2) [0.5]`
/// - nullary rules: `State -> label`
/// - final states: `!` or `°` after any state occurrence
/// - quoted names with single or double quotes
/// - optional weights, defaulting to `1.0`
/// - `// ...` line comments and `/* ... */` block comments
pub fn parse_alto(input: &str) -> Result<AltoAutomaton, AltoParseError> {
    Parser::new(input).parse()
}

#[derive(Clone, Debug, PartialEq)]
enum TokenKind {
    Name(String),
    Arrow,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Fin,
}

#[derive(Clone, Debug, PartialEq)]
struct Token {
    kind: TokenKind,
    offset: usize,
}

struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    builder: ExplicitBuilder,
    states: Interner<String>,
    state_ids: FxHashMap<String, StateId>,
    signature: AltoSignature,
    rules: Vec<AltoRule>,
    _input: &'a str,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            tokens: Vec::new(),
            pos: 0,
            builder: ExplicitBuilder::new(),
            states: Interner::new(),
            state_ids: FxHashMap::default(),
            signature: AltoSignature::new(),
            rules: Vec::new(),
            _input: input,
        }
    }

    fn parse(mut self) -> Result<AltoAutomaton, AltoParseError> {
        self.tokens = lex(self._input)?;
        while !self.is_eof() {
            self.rule()?;
        }

        Ok(AltoAutomaton {
            automaton: self.builder.build(),
            states: self.states,
            signature: self.signature,
            rules: self.rules,
        })
    }

    fn rule(&mut self) -> Result<(), AltoParseError> {
        let (parent_name, parent, _) = self.state()?;
        self.expect_arrow()?;
        let (symbol_name, children) = self.term()?;
        let weight = if self.eat_lbracket() {
            let start = self.current_offset();
            let text = self.expect_name("weight")?;
            self.expect_rbracket()?;
            text.parse::<f64>()
                .map_err(|_| AltoParseError::InvalidWeight {
                    text,
                    offset: start,
                })?
        } else {
            1.0
        };

        let symbol = self.signature.intern(symbol_name.clone(), children.len())?;
        let child_ids: Vec<StateId> = children.iter().map(|(_, id, _)| *id).collect();
        let child_names: Vec<String> = children.iter().map(|(name, _, _)| name.clone()).collect();
        self.builder.add_rule(symbol, child_ids.clone(), parent);
        self.rules.push(AltoRule {
            parent,
            symbol,
            children: child_ids,
            weight,
            parent_name,
            symbol_name,
            child_names,
        });
        Ok(())
    }

    fn term(&mut self) -> Result<(String, Vec<(String, StateId, bool)>), AltoParseError> {
        let name = self.expect_name("terminal symbol")?;
        let children = if self.eat_lparen() {
            let mut children = Vec::new();
            if !self.eat_rparen() {
                loop {
                    children.push(self.state()?);
                    if self.eat_comma() {
                        continue;
                    }
                    self.expect_rparen()?;
                    break;
                }
            }
            children
        } else {
            Vec::new()
        };
        Ok((name, children))
    }

    fn state(&mut self) -> Result<(String, StateId, bool), AltoParseError> {
        let name = self.expect_name("state")?;
        let final_state = self.eat_fin();
        let id = self.state_id(&name);
        if final_state {
            self.builder.add_accepting(id);
        }
        Ok((name, id, final_state))
    }

    fn state_id(&mut self, name: &str) -> StateId {
        if let Some(&id) = self.state_ids.get(name) {
            return id;
        }
        let id = self.builder.new_state();
        let interned = self.states.intern(name.to_owned());
        debug_assert_eq!(id, interned);
        self.state_ids.insert(name.to_owned(), id);
        id
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn current_offset(&self) -> usize {
        self.tokens
            .get(self.pos)
            .map(|t| t.offset)
            .or_else(|| self.tokens.last().map(|t| t.offset + 1))
            .unwrap_or(0)
    }

    fn expect_name(&mut self, expected: &'static str) -> Result<String, AltoParseError> {
        match self.tokens.get(self.pos) {
            Some(Token {
                kind: TokenKind::Name(name),
                ..
            }) => {
                self.pos += 1;
                Ok(name.clone())
            }
            Some(tok) => Err(AltoParseError::Unexpected {
                expected,
                found: token_display(&tok.kind),
                offset: tok.offset,
            }),
            None => Err(AltoParseError::Expected {
                expected,
                offset: self.current_offset(),
            }),
        }
    }

    fn expect_arrow(&mut self) -> Result<(), AltoParseError> {
        self.expect_punct("->", |kind| matches!(kind, TokenKind::Arrow))
    }

    fn expect_rparen(&mut self) -> Result<(), AltoParseError> {
        self.expect_punct(")", |kind| matches!(kind, TokenKind::RParen))
    }

    fn expect_rbracket(&mut self) -> Result<(), AltoParseError> {
        self.expect_punct("]", |kind| matches!(kind, TokenKind::RBracket))
    }

    fn expect_punct(
        &mut self,
        expected: &'static str,
        pred: impl FnOnce(&TokenKind) -> bool,
    ) -> Result<(), AltoParseError> {
        match self.tokens.get(self.pos) {
            Some(tok) if pred(&tok.kind) => {
                self.pos += 1;
                Ok(())
            }
            Some(tok) => Err(AltoParseError::Unexpected {
                expected,
                found: token_display(&tok.kind),
                offset: tok.offset,
            }),
            None => Err(AltoParseError::Expected {
                expected,
                offset: self.current_offset(),
            }),
        }
    }

    fn eat_lparen(&mut self) -> bool {
        self.eat(|kind| matches!(kind, TokenKind::LParen))
    }

    fn eat_rparen(&mut self) -> bool {
        self.eat(|kind| matches!(kind, TokenKind::RParen))
    }

    fn eat_lbracket(&mut self) -> bool {
        self.eat(|kind| matches!(kind, TokenKind::LBracket))
    }

    fn eat_comma(&mut self) -> bool {
        self.eat(|kind| matches!(kind, TokenKind::Comma))
    }

    fn eat_fin(&mut self) -> bool {
        self.eat(|kind| matches!(kind, TokenKind::Fin))
    }

    fn eat(&mut self, pred: impl FnOnce(&TokenKind) -> bool) -> bool {
        if self.tokens.get(self.pos).is_some_and(|tok| pred(&tok.kind)) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
}

fn lex(input: &str) -> Result<Vec<Token>, AltoParseError> {
    let mut tokens = Vec::new();
    let mut iter = input.char_indices().peekable();

    while let Some((offset, ch)) = iter.next() {
        match ch {
            c if c.is_whitespace() => {}
            '/' if iter.peek().is_some_and(|&(_, c)| c == '/') => {
                iter.next();
                for (_, c) in iter.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '/' if iter.peek().is_some_and(|&(_, c)| c == '*') => {
                iter.next();
                let mut closed = false;
                let mut prev = '\0';
                for (_, c) in iter.by_ref() {
                    if prev == '*' && c == '/' {
                        closed = true;
                        break;
                    }
                    prev = c;
                }
                if !closed {
                    return Err(AltoParseError::UnterminatedComment { offset });
                }
            }
            '-' if iter.peek().is_some_and(|&(_, c)| c == '>') => {
                iter.next();
                tokens.push(Token {
                    kind: TokenKind::Arrow,
                    offset,
                });
            }
            '(' => tokens.push(Token {
                kind: TokenKind::LParen,
                offset,
            }),
            ')' => tokens.push(Token {
                kind: TokenKind::RParen,
                offset,
            }),
            '[' => tokens.push(Token {
                kind: TokenKind::LBracket,
                offset,
            }),
            ']' => tokens.push(Token {
                kind: TokenKind::RBracket,
                offset,
            }),
            ',' => tokens.push(Token {
                kind: TokenKind::Comma,
                offset,
            }),
            '!' | '°' => tokens.push(Token {
                kind: TokenKind::Fin,
                offset,
            }),
            '\'' | '"' => {
                let quote = ch;
                let mut value = String::new();
                let mut closed = false;
                for (_, c) in iter.by_ref() {
                    if c == quote {
                        closed = true;
                        break;
                    }
                    value.push(c);
                }
                if !closed {
                    return Err(AltoParseError::UnterminatedQuote { offset });
                }
                tokens.push(Token {
                    kind: TokenKind::Name(value),
                    offset,
                });
            }
            c if is_name_start(c) || c.is_ascii_digit() || c == '-' || c == '.' => {
                let mut value = String::new();
                value.push(c);
                while let Some(&(_, next)) = iter.peek() {
                    if is_name_continue(next) {
                        value.push(next);
                        iter.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token {
                    kind: TokenKind::Name(value),
                    offset,
                });
            }
            _ => {
                return Err(AltoParseError::Unexpected {
                    expected: "Alto token",
                    found: ch.to_string(),
                    offset,
                });
            }
        }
    }

    Ok(tokens)
}

fn is_name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || matches!(c, '_' | '*' | '$' | '@' | '+')
}

fn is_name_continue(c: char) -> bool {
    is_name_start(c)
        || c.is_ascii_digit()
        || matches!(c, '<' | '>' | '/' | '.' | '-')
        || matches!(c, 'e' | 'E')
}

fn token_display(kind: &TokenKind) -> String {
    match kind {
        TokenKind::Name(name) => format!("name {name:?}"),
        TokenKind::Arrow => "->".to_owned(),
        TokenKind::LParen => "(".to_owned(),
        TokenKind::RParen => ")".to_owned(),
        TokenKind::LBracket => "[".to_owned(),
        TokenKind::RBracket => "]".to_owned(),
        TokenKind::Comma => ",".to_owned(),
        TokenKind::Fin => "!".to_owned(),
    }
}

impl fmt::Display for AltoSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, name) in self.names.iter().enumerate() {
            if idx > 0 {
                writeln!(f)?;
            }
            let symbol = Symbol(idx as u32);
            write!(f, "{} / {}", name, self.arity(symbol))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BottomUpTa, DetBottomUpTa};

    #[test]
    fn parses_wiki_example_as_bottom_up() {
        let parsed = parse_alto(
            "
            S! -> f(A,A) [1.0]
            A -> g(A) [0.5]
            A -> a [0.5]
            ",
        )
        .unwrap();
        let s = parsed.states.get(&"S".to_owned()).unwrap();
        let a_state = parsed.states.get(&"A".to_owned()).unwrap();
        let f = parsed.signature.get("f").unwrap();
        let leaf = parsed.signature.get("a").unwrap();

        let mut out = Vec::new();
        parsed.automaton.step(leaf, &[], &mut |q| out.push(q));
        assert_eq!(out, vec![a_state]);
        assert_eq!(parsed.automaton.step_det(f, &[a_state, a_state]), Some(s));
        assert!(parsed.automaton.is_accepting(&s));
        assert_eq!(parsed.rules[1].weight, 0.5);
    }

    #[test]
    fn accepts_whitespace_separated_rules_and_comments() {
        let parsed =
            parse_alto("q1 -> a /* ignored -> text */ q2! -> f(q1, // line\n q1)").unwrap();
        let q1 = parsed.states.get(&"q1".to_owned()).unwrap();
        let q2 = parsed.states.get(&"q2".to_owned()).unwrap();
        let f = parsed.signature.get("f").unwrap();
        assert_eq!(parsed.automaton.step_det(f, &[q1, q1]), Some(q2));
    }

    #[test]
    fn parses_quoted_names_and_scientific_weights() {
        let parsed =
            parse_alto("'S,0-1'! -> r('A,0-1', \"B state\") [3.3921302578018993E-4]").unwrap();
        assert_eq!(parsed.rules[0].parent_name, "S,0-1");
        assert_eq!(parsed.rules[0].child_names, vec!["A,0-1", "B state"]);
        assert!((parsed.rules[0].weight - 3.3921302578018993E-4).abs() < 1e-12);
    }

    #[test]
    fn detects_arity_mismatch() {
        let err = parse_alto("S -> f(A) T -> f(A,A)").unwrap_err();
        assert!(matches!(err, AltoParseError::ArityMismatch { .. }));
    }
}
