//! Shared AST and lexer for Alto-format automata and IRTGs.

use thiserror::Error;

/// Complete parsed IRTG AST.
#[derive(Clone, Debug, PartialEq)]
pub struct AstIrtg {
    /// Interpretation declarations.
    pub interpretations: Vec<AstInterpretationDecl>,
    /// Feature declarations skipped by the runtime for now.
    pub features: Vec<AstFeatureDecl>,
    /// Grammar rules with optional homomorphism clauses.
    pub rules: Vec<AstRule>,
}

/// Parsed tree automaton AST.
#[derive(Clone, Debug, PartialEq)]
pub struct AstFta {
    /// Automaton rules.
    pub rules: Vec<AstAutoRule>,
}

/// Alto interpretation declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstInterpretationDecl {
    /// Interpretation name.
    pub name: String,
    /// Alto algebra class name.
    pub algebra: String,
}

/// Alto feature declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstFeatureDecl {
    /// Raw feature declaration names, preserved for diagnostics/future use.
    pub parts: Vec<String>,
    /// State list at the end of the declaration.
    pub states: Vec<AstState>,
}

/// A grammar rule plus homomorphism clauses.
#[derive(Clone, Debug, PartialEq)]
pub struct AstRule {
    /// The grammar automaton rule.
    pub auto: AstAutoRule,
    /// Homomorphism clauses following the automaton rule.
    pub homs: Vec<AstHomRule>,
}

/// A top-down Alto automaton rule.
#[derive(Clone, Debug, PartialEq)]
pub struct AstAutoRule {
    /// Parent state.
    pub parent: AstState,
    /// Grammar or automaton terminal label.
    pub symbol: String,
    /// Child states.
    pub children: Vec<AstState>,
    /// Optional rule weight.
    pub weight: Option<f64>,
}

/// A state occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstState {
    /// State name.
    pub name: String,
    /// Whether this state occurrence carries a final marker.
    pub is_final: bool,
}

/// One interpretation-specific homomorphism clause.
#[derive(Clone, Debug, PartialEq)]
pub struct AstHomRule {
    /// Interpretation name.
    pub interpretation: String,
    /// Homomorphic image term.
    pub term: AstHomTerm,
}

/// Homomorphism RHS term.
#[derive(Clone, Debug, PartialEq)]
pub enum AstHomTerm {
    /// Target algebra operation.
    Symbol(String, Vec<AstHomTerm>),
    /// Alto variable number. Alto syntax is one-based.
    Variable(usize),
}

/// Token produced by the Alto lexer.
#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    /// Name-like token, including quoted names and numeric weights.
    Name(String),
    /// Numeric token used for weights.
    Number(String),
    /// Alto variable token, e.g. `?1`.
    Variable(usize),
    /// `interpretation`
    Interpretation,
    /// `feature`
    Feature,
    /// `->`
    Arrow,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `,`
    Comma,
    /// `:`
    Colon,
    /// `!` or `°`
    Fin,
}

/// Lexer error.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum LexError {
    /// A quoted name was not closed.
    #[error("unterminated quoted name starting at byte {offset}")]
    UnterminatedQuote {
        /// Byte offset.
        offset: usize,
    },
    /// A block comment was not closed.
    #[error("unterminated block comment starting at byte {offset}")]
    UnterminatedComment {
        /// Byte offset.
        offset: usize,
    },
    /// A variable token was malformed.
    #[error("invalid variable at byte {offset}")]
    InvalidVariable {
        /// Byte offset.
        offset: usize,
    },
    /// Unexpected character.
    #[error("unexpected character {found:?} at byte {offset}")]
    Unexpected {
        /// Character.
        found: char,
        /// Byte offset.
        offset: usize,
    },
}

/// Lex Alto-format input into LALRPOP-compatible spanned tokens.
pub fn lex(input: &str) -> Result<Vec<(usize, Tok, usize)>, LexError> {
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
                let mut end = offset + 2;
                for (idx, c) in iter.by_ref() {
                    end = idx + c.len_utf8();
                    if prev == '*' && c == '/' {
                        closed = true;
                        break;
                    }
                    prev = c;
                }
                if !closed {
                    return Err(LexError::UnterminatedComment { offset });
                }
                let _ = end;
            }
            '-' if iter.peek().is_some_and(|&(_, c)| c == '>') => {
                iter.next();
                tokens.push((offset, Tok::Arrow, offset + 2));
            }
            '(' => tokens.push((offset, Tok::LParen, offset + 1)),
            ')' => tokens.push((offset, Tok::RParen, offset + 1)),
            '[' => tokens.push((offset, Tok::LBracket, offset + 1)),
            ']' => tokens.push((offset, Tok::RBracket, offset + 1)),
            ',' => tokens.push((offset, Tok::Comma, offset + 1)),
            ':' => tokens.push((offset, Tok::Colon, offset + 1)),
            '!' | '°' => tokens.push((offset, Tok::Fin, offset + ch.len_utf8())),
            '?' => {
                let mut value = String::new();
                let mut end = offset + 1;
                while let Some(&(idx, next)) = iter.peek() {
                    if next.is_ascii_digit() {
                        value.push(next);
                        end = idx + next.len_utf8();
                        iter.next();
                    } else {
                        break;
                    }
                }
                let variable = value
                    .parse::<usize>()
                    .map_err(|_| LexError::InvalidVariable { offset })?;
                tokens.push((offset, Tok::Variable(variable), end));
            }
            '\'' | '"' => {
                let quote = ch;
                let mut value = String::new();
                let mut closed = false;
                let mut end = offset + ch.len_utf8();
                for (idx, c) in iter.by_ref() {
                    end = idx + c.len_utf8();
                    if c == quote {
                        closed = true;
                        break;
                    }
                    value.push(c);
                }
                if !closed {
                    return Err(LexError::UnterminatedQuote { offset });
                }
                tokens.push((offset, Tok::Name(value), end));
            }
            c if is_name_start(c) || c.is_ascii_digit() || c == '-' || c == '.' => {
                let mut value = String::new();
                value.push(c);
                let mut end = offset + c.len_utf8();
                while let Some(&(idx, next)) = iter.peek() {
                    if is_name_continue(next) {
                        value.push(next);
                        end = idx + next.len_utf8();
                        iter.next();
                    } else {
                        break;
                    }
                }
                let token = if value.parse::<f64>().is_ok() {
                    Tok::Number(value)
                } else {
                    match value.as_str() {
                        "interpretation" => Tok::Interpretation,
                        "feature" => Tok::Feature,
                        _ => Tok::Name(value),
                    }
                };
                tokens.push((offset, token, end));
            }
            _ => return Err(LexError::Unexpected { found: ch, offset }),
        }
    }

    Ok(tokens)
}

fn is_name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || matches!(c, '_' | '*' | '$' | '@' | '+')
}

fn is_name_continue(c: char) -> bool {
    is_name_start(c) || c.is_ascii_digit() || matches!(c, '<' | '>' | '/' | '.' | '-')
}
