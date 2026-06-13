use crate::{
    Explicit, ExplicitBuilder, FxHashMap, Interner, Signature, SignatureError, StateId, Symbol,
    alto_ast::{AstAutoRule, AstFta, AstState, LexError, Tok, lex},
    alto_grammar,
};
use lalrpop_util::ParseError;
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

/// Backwards-compatible name for the shared label signature.
pub type AltoSignature = Signature;

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
    /// A variable token appeared in an automaton file or was malformed.
    #[error("invalid variable at byte {offset}")]
    InvalidVariable {
        /// Byte offset where the variable started.
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
    /// LALRPOP reported a syntax error.
    #[error("{0}")]
    Syntax(String),
}

impl From<SignatureError> for AltoParseError {
    fn from(value: SignatureError) -> Self {
        match value {
            SignatureError::ArityMismatch {
                symbol,
                first,
                second,
            } => Self::ArityMismatch {
                symbol,
                first,
                second,
            },
        }
    }
}

impl From<LexError> for AltoParseError {
    fn from(value: LexError) -> Self {
        match value {
            LexError::UnterminatedQuote { offset } => Self::UnterminatedQuote { offset },
            LexError::UnterminatedComment { offset } => Self::UnterminatedComment { offset },
            LexError::InvalidVariable { offset } => Self::InvalidVariable { offset },
            LexError::Unexpected { found, offset } => Self::Unexpected {
                expected: "Alto token",
                found: found.to_string(),
                offset,
            },
        }
    }
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
    let mut signature = Signature::new();
    parse_alto_with_signature(input, &mut signature)
}

/// Parse an Alto `.auto` file using a caller-owned shared signature.
///
/// This is useful when automata and input trees should be compiled into the
/// same raw [`Symbol`] space. The returned [`AltoAutomaton`] contains a clone of
/// the signature after parsing; the caller can keep using `signature` to parse
/// or validate trees before running the automaton.
pub fn parse_alto_with_signature(
    input: &str,
    signature: &mut Signature,
) -> Result<AltoAutomaton, AltoParseError> {
    let tokens = lex(input)?;
    let ast = alto_grammar::FtaParser::new()
        .parse(tokens.into_iter().map(Ok))
        .map_err(parse_error_to_alto)?;
    build_alto(ast, signature)
}

fn build_alto(ast: AstFta, signature: &mut Signature) -> Result<AltoAutomaton, AltoParseError> {
    let mut builder = ExplicitBuilder::new();
    let mut states = Interner::new();
    let mut state_ids = FxHashMap::default();
    let mut rules = Vec::new();

    for rule in ast.rules {
        let parent_name = rule.parent.name.clone();
        let parent = state_id(&mut builder, &mut states, &mut state_ids, &rule.parent);
        if rule.parent.is_final {
            builder.add_accepting(parent);
        }
        let child_ids: Vec<_> = rule
            .children
            .iter()
            .map(|child| {
                let id = state_id(&mut builder, &mut states, &mut state_ids, child);
                if child.is_final {
                    builder.add_accepting(id);
                }
                id
            })
            .collect();
        let child_names: Vec<_> = rule
            .children
            .iter()
            .map(|child| child.name.clone())
            .collect();
        let symbol = signature.intern(rule.symbol.clone(), child_ids.len())?;
        builder.add_rule(symbol, child_ids.clone(), parent);
        rules.push(alto_rule(
            rule,
            parent,
            symbol,
            child_ids,
            parent_name,
            child_names,
        ));
    }

    Ok(AltoAutomaton {
        automaton: builder.build(),
        states,
        signature: signature.clone(),
        rules,
    })
}

fn alto_rule(
    rule: AstAutoRule,
    parent: StateId,
    symbol: Symbol,
    children: Vec<StateId>,
    parent_name: String,
    child_names: Vec<String>,
) -> AltoRule {
    AltoRule {
        parent,
        symbol,
        children,
        weight: rule.weight.unwrap_or(1.0),
        parent_name,
        symbol_name: rule.symbol,
        child_names,
    }
}

fn state_id(
    builder: &mut ExplicitBuilder,
    states: &mut Interner<String>,
    state_ids: &mut FxHashMap<String, StateId>,
    state: &AstState,
) -> StateId {
    if let Some(&id) = state_ids.get(&state.name) {
        return id;
    }
    let id = builder.new_state();
    let interned = states.intern(state.name.clone());
    debug_assert_eq!(id, interned);
    state_ids.insert(state.name.clone(), id);
    id
}

fn parse_error_to_alto(err: ParseError<usize, Tok, String>) -> AltoParseError {
    match err {
        ParseError::InvalidToken { location } => AltoParseError::Unexpected {
            expected: "Alto token",
            found: "<invalid>".to_owned(),
            offset: location,
        },
        ParseError::UnrecognizedEof { location, expected } => AltoParseError::Expected {
            expected: leak_expected(expected),
            offset: location,
        },
        ParseError::UnrecognizedToken { token, expected } => AltoParseError::Unexpected {
            expected: leak_expected(expected),
            found: token_display(&token.1),
            offset: token.0,
        },
        ParseError::ExtraToken { token } => AltoParseError::Unexpected {
            expected: "end of input",
            found: token_display(&token.1),
            offset: token.0,
        },
        ParseError::User { error } => AltoParseError::Syntax(error),
    }
}

fn leak_expected(expected: Vec<String>) -> &'static str {
    if expected.is_empty() {
        "valid syntax"
    } else {
        Box::leak(expected.join(", ").into_boxed_str())
    }
}

fn token_display(kind: &Tok) -> String {
    match kind {
        Tok::Name(name) => format!("name {name:?}"),
        Tok::Number(number) => format!("number {number:?}"),
        Tok::Variable(variable) => format!("variable ?{variable}"),
        Tok::Interpretation => "interpretation".to_owned(),
        Tok::Feature => "feature".to_owned(),
        Tok::Arrow => "->".to_owned(),
        Tok::LParen => "(".to_owned(),
        Tok::RParen => ")".to_owned(),
        Tok::LBracket => "[".to_owned(),
        Tok::RBracket => "]".to_owned(),
        Tok::Comma => ",".to_owned(),
        Tok::Colon => ":".to_owned(),
        Tok::Fin => "!".to_owned(),
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

    #[test]
    fn can_parse_with_shared_signature() {
        let mut signature = Signature::new();
        let a = signature.intern("a".to_owned(), 0).unwrap();
        let parsed = parse_alto_with_signature("S! -> a", &mut signature).unwrap();
        assert_eq!(parsed.signature.get("a"), Some(a));
        assert_eq!(signature.get("a"), Some(a));
    }

    #[test]
    fn parses_nullary_empty_parens() {
        let parsed = parse_alto("S! -> a()").unwrap();
        assert_eq!(parsed.rules[0].child_names, Vec::<String>::new());
        assert_eq!(parsed.signature.arity(parsed.rules[0].symbol), 0);
    }

    #[test]
    fn final_marker_on_child_marks_accepting_state() {
        let parsed = parse_alto("S -> f(A!)").unwrap();
        let a = parsed.states.get(&"A".to_owned()).unwrap();
        assert!(parsed.automaton.is_accepting(&a));
    }

    #[test]
    fn rejects_variable_tokens_in_automata() {
        let err = parse_alto("S -> f(?1)").unwrap_err();
        assert!(matches!(err, AltoParseError::Unexpected { .. }));
    }

    #[test]
    fn lalrpop_rejects_trailing_junk() {
        let err = parse_alto("S -> a [oops]").unwrap_err();
        assert!(matches!(err, AltoParseError::Unexpected { .. }));
    }
}
