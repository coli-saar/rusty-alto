//! Interpreted regular tree grammars.

use crate::{
    Algebra, Explicit, ExplicitBuildError, ExplicitBuilder, FxHashMap, Homomorphism,
    HomomorphismError, IndexedCondensedIntersectionStats, Interner, InvHom, Signature,
    SignatureError, StateId, StringAlgebra, Symbol,
    alto_ast::{AstHomTerm, AstIrtg, AstState, LexError, Tok, lex},
    alto_grammar, materialize_topdown_condensed_intersection,
};
use lalrpop_util::ParseError;
use rusty_tree::tree::Tree;
use std::{any::Any, cell::RefCell, fmt, io::Read, marker::PhantomData};
use thiserror::Error;

const STRING_ALGEBRA: &str = "de.up.ling.irtg.algebra.StringAlgebra";

/// An interpreted regular tree grammar.
#[derive(Debug)]
pub struct Irtg {
    grammar: Explicit,
    states: Interner<String>,
    grammar_signature: Signature,
    interpretations: FxHashMap<String, Interpretation>,
}

impl Irtg {
    /// Return the explicit grammar automaton.
    pub fn grammar(&self) -> &Explicit {
        &self.grammar
    }

    /// Return the grammar signature.
    pub fn grammar_signature(&self) -> &Signature {
        &self.grammar_signature
    }

    /// Return the grammar state-name interner.
    pub fn states(&self) -> &Interner<String> {
        &self.states
    }

    /// Return the names of interpretations backed by [`StringAlgebra`].
    pub fn string_interpretation_names(&self) -> Vec<&str> {
        let mut names: Vec<_> = self
            .interpretations
            .values()
            .filter(|interpretation| interpretation.kind == InterpretationKind::String)
            .map(|interpretation| interpretation.name.as_str())
            .collect();
        names.sort_unstable();
        names
    }

    /// Return a typed handle for a named interpretation.
    pub fn interpretation<A>(&self, name: &str) -> Result<TypedInterpretation<'_, A>, IrtgError>
    where
        A: Algebra + 'static,
    {
        let interpretation = self
            .interpretations
            .get(name)
            .ok_or_else(|| IrtgError::UnknownInterpretation(name.to_owned()))?;
        if interpretation.algebra.borrow().as_ref().is::<A>() {
            Ok(TypedInterpretation {
                interpretation,
                _algebra: PhantomData,
            })
        } else {
            Err(IrtgError::WrongAlgebraType {
                interpretation: name.to_owned(),
                requested: std::any::type_name::<A>(),
                actual: interpretation.class_name.clone(),
            })
        }
    }

    /// Parse with one or more interpretation inputs.
    pub fn parse<'a>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
    ) -> Result<ParseChart, IrtgError> {
        let mut chart = self.grammar.clone();
        let mut stats = Vec::new();

        for input in inputs {
            let interpretation = input.interpretation;
            match interpretation.kind {
                InterpretationKind::String => {
                    let value = *input.value.downcast::<Vec<Symbol>>().map_err(|_| {
                        IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        }
                    })?;
                    let algebra = interpretation.algebra.borrow();
                    let algebra = algebra
                        .as_ref()
                        .downcast_ref::<StringAlgebra>()
                        .ok_or_else(|| IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        })?;
                    let decomp = algebra.decompose(value);
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    let (next_chart, _right_interner, stat) =
                        materialize_topdown_condensed_intersection(&chart, &invhom);
                    chart = next_chart;
                    stats.push(stat);
                }
                InterpretationKind::Unsupported => {
                    return Err(IrtgError::UnsupportedAlgebra {
                        interpretation: interpretation.name.clone(),
                        class_name: interpretation.class_name.clone(),
                    });
                }
            }
        }

        Ok(ParseChart {
            automaton: chart,
            stats,
        })
    }
}

/// A named interpretation of an IRTG.
#[derive(Debug)]
pub struct Interpretation {
    name: String,
    class_name: String,
    kind: InterpretationKind,
    algebra: RefCell<Box<dyn Any>>,
    algebra_signature: Signature,
    homomorphism: Homomorphism,
}

impl Interpretation {
    /// Return the interpretation name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the declared Alto algebra class name.
    pub fn class_name(&self) -> &str {
        &self.class_name
    }

    /// Return the algebra signature.
    pub fn algebra_signature(&self) -> &Signature {
        &self.algebra_signature
    }

    /// Return the homomorphism.
    pub fn homomorphism(&self) -> &Homomorphism {
        &self.homomorphism
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InterpretationKind {
    String,
    Unsupported,
}

/// Typed access to an interpretation.
pub struct TypedInterpretation<'i, A> {
    interpretation: &'i Interpretation,
    _algebra: PhantomData<A>,
}

impl<'i, A> TypedInterpretation<'i, A>
where
    A: Algebra + 'static,
    A::Value: 'static,
    A::ParseError: fmt::Display,
{
    /// Return the interpretation name.
    pub fn name(&self) -> &str {
        self.interpretation.name()
    }

    /// Return the interpretation's algebra signature.
    pub fn algebra_signature(&self) -> &Signature {
        self.interpretation.algebra_signature()
    }

    /// Return the interpretation's homomorphism.
    pub fn homomorphism(&self) -> &Homomorphism {
        self.interpretation.homomorphism()
    }

    /// Parse a textual object using the interpretation's algebra.
    pub fn parse_object(&self, input: &str) -> Result<A::Value, IrtgError> {
        let mut algebra = self.interpretation.algebra.borrow_mut();
        let algebra =
            algebra
                .as_mut()
                .downcast_mut::<A>()
                .ok_or_else(|| IrtgError::WrongInputType {
                    interpretation: self.interpretation.name.clone(),
                })?;
        algebra
            .parse_object(input)
            .map_err(|err| IrtgError::ObjectParse {
                interpretation: self.interpretation.name.clone(),
                message: err.to_string(),
            })
    }

    /// Package a typed algebra value as an input for [`Irtg::parse`].
    pub fn input(&self, value: A::Value) -> ParseInput<'i> {
        ParseInput {
            interpretation: self.interpretation,
            value: Box::new(value),
        }
    }
}

/// Type-erased parse input created by a typed interpretation handle.
pub struct ParseInput<'i> {
    interpretation: &'i Interpretation,
    value: Box<dyn Any>,
}

/// The parse chart returned by [`Irtg::parse`].
#[derive(Debug)]
pub struct ParseChart {
    /// Explicit grammar chart after all input constraints were applied.
    pub automaton: Explicit,
    /// Per-intersection materialization statistics.
    pub stats: Vec<IndexedCondensedIntersectionStats>,
}

/// Errors returned by IRTG parsing, construction, and parsing.
#[derive(Debug, Error)]
pub enum IrtgError {
    /// Input bytes were not valid UTF-8.
    #[error("input is not valid UTF-8: {0}")]
    Utf8(#[from] std::string::FromUtf8Error),
    /// Reading failed.
    #[error("failed to read IRTG: {0}")]
    Io(#[from] std::io::Error),
    /// Syntax error.
    #[error("{0}")]
    Syntax(String),
    /// A signature rejected a symbol.
    #[error("{0}")]
    Signature(#[from] SignatureError),
    /// A homomorphism rejected an image.
    #[error("{0}")]
    Homomorphism(#[from] HomomorphismError),
    /// The grammar automaton could not be built.
    #[error("{0}")]
    Automaton(#[from] ExplicitBuildError),
    /// A named interpretation was not found.
    #[error("unknown interpretation {0:?}")]
    UnknownInterpretation(String),
    /// A requested interpretation has a different concrete algebra type.
    #[error("interpretation {interpretation:?} has algebra {actual}, not {requested}")]
    WrongAlgebraType {
        /// Interpretation name.
        interpretation: String,
        /// Requested Rust type.
        requested: &'static str,
        /// Actual Alto class name.
        actual: String,
    },
    /// A parse input value has the wrong concrete value type.
    #[error("wrong input value type for interpretation {interpretation:?}")]
    WrongInputType {
        /// Interpretation name.
        interpretation: String,
    },
    /// The algebra could not parse an object.
    #[error("failed to parse object for interpretation {interpretation:?}: {message}")]
    ObjectParse {
        /// Interpretation name.
        interpretation: String,
        /// Parser error.
        message: String,
    },
    /// The declared algebra is not implemented yet.
    #[error("unsupported algebra {class_name} for interpretation {interpretation:?}")]
    UnsupportedAlgebra {
        /// Interpretation name.
        interpretation: String,
        /// Alto class name.
        class_name: String,
    },
}

/// Parse an Alto-format IRTG from UTF-8 bytes.
pub fn parse_irtg<R: Read>(mut reader: R) -> Result<Irtg, IrtgError> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    let input = String::from_utf8(bytes)?;
    let tokens = lex(&input).map_err(irtg_lex_error)?;
    let ast = alto_grammar::IrtgParser::new()
        .parse(tokens.into_iter().map(Ok))
        .map_err(irtg_parse_error)?;
    build_irtg(ast)
}

fn build_irtg(ast: AstIrtg) -> Result<Irtg, IrtgError> {
    let mut builder = ExplicitBuilder::new();
    let mut states = Interner::new();
    let mut state_ids = FxHashMap::default();
    let mut grammar_signature = Signature::new();
    let mut homs = FxHashMap::default();
    let mut algebra_signatures = FxHashMap::default();

    for decl in &ast.interpretations {
        homs.insert(decl.name.clone(), Homomorphism::new());
        algebra_signatures.insert(decl.name.clone(), Signature::new());
    }

    for rule in ast.rules {
        let parent = state_id(&mut builder, &mut states, &mut state_ids, &rule.auto.parent);
        if rule.auto.parent.is_final {
            builder.add_accepting(parent);
        }
        let child_ids: Vec<_> = rule
            .auto
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
        let symbol = grammar_signature.intern(rule.auto.symbol.clone(), child_ids.len())?;
        builder.add_weighted_rule(symbol, child_ids, parent, rule.auto.weight.unwrap_or(1.0));

        for hom_rule in rule.homs {
            let Some(hom) = homs.get_mut(&hom_rule.interpretation) else {
                return Err(IrtgError::UnknownInterpretation(hom_rule.interpretation));
            };
            let signature = algebra_signatures
                .get_mut(&hom_rule.interpretation)
                .expect("hom and signature maps are initialized together");
            let term = lower_hom_term(&hom_rule.term, hom, signature)?;
            hom.add(symbol, rule.auto.children.len(), term)?;
        }
    }

    let mut interpretations = FxHashMap::default();
    for decl in ast.interpretations {
        let (kind, algebra, algebra_signature): (InterpretationKind, Box<dyn Any>, Signature) =
            if decl.algebra == STRING_ALGEBRA {
                let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
                let algebra = StringAlgebra::with_signature(signature.clone());
                (InterpretationKind::String, Box::new(algebra), signature)
            } else {
                (
                    InterpretationKind::Unsupported,
                    Box::new(()),
                    Signature::new(),
                )
            };
        let homomorphism = homs.remove(&decl.name).unwrap_or_else(Homomorphism::new);
        interpretations.insert(
            decl.name.clone(),
            Interpretation {
                name: decl.name,
                class_name: decl.algebra,
                kind,
                algebra: RefCell::new(algebra),
                algebra_signature,
                homomorphism,
            },
        );
    }

    Ok(Irtg {
        grammar: builder.try_build()?,
        states,
        grammar_signature,
        interpretations,
    })
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

fn lower_hom_term(
    term: &AstHomTerm,
    hom: &mut Homomorphism,
    signature: &mut Signature,
) -> Result<Tree, IrtgError> {
    match term {
        AstHomTerm::Variable(variable) => {
            if *variable == 0 {
                return Err(IrtgError::Syntax(
                    "Alto homomorphism variables are one-based; ?0 is invalid".to_owned(),
                ));
            }
            Ok(hom.add_var(variable - 1))
        }
        AstHomTerm::Symbol(name, children) => {
            let children = children
                .iter()
                .map(|child| lower_hom_term(child, hom, signature))
                .collect::<Result<Vec<_>, _>>()?;
            let symbol = signature.intern(name.clone(), children.len())?;
            Ok(hom.add_symbol(symbol, children))
        }
    }
}

fn irtg_lex_error(err: LexError) -> IrtgError {
    IrtgError::Syntax(err.to_string())
}

fn irtg_parse_error(err: ParseError<usize, Tok, String>) -> IrtgError {
    IrtgError::Syntax(match err {
        ParseError::InvalidToken { location } => format!("invalid token at byte {location}"),
        ParseError::UnrecognizedEof { location, expected } => {
            format!(
                "unexpected EOF at byte {location}; expected {}",
                expected.join(", ")
            )
        }
        ParseError::UnrecognizedToken { token, expected } => format!(
            "unexpected token {:?} at byte {}; expected {}",
            token.1,
            token.0,
            expected.join(", ")
        ),
        ParseError::ExtraToken { token } => {
            format!("unexpected extra token {:?} at byte {}", token.1, token.0)
        }
        ParseError::User { error } => error,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_tiny_string_irtg_and_accepts_compatible_input() {
        let irtg = parse_irtg(
            br#"
            interpretation english: de.up.ling.irtg.algebra.StringAlgebra

            S! -> r(NP,VP) [1.0]
              [english] *(?1,?2)

            NP -> john_rule
              [english] john

            VP -> watches_rule
              [english] watches
            "# as &[u8],
        )
        .unwrap();

        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();
        let value = english.parse_object("john watches").unwrap();
        let chart = irtg.parse([english.input(value)]).unwrap();
        assert!(!chart.automaton.is_empty());

        let bad = english.parse_object("john sleeps").unwrap();
        let chart = irtg.parse([english.input(bad)]).unwrap();
        assert!(chart.automaton.is_empty());
    }

    #[test]
    fn parses_multi_interpretation_irtg_and_enforces_both_inputs() {
        let irtg = parse_irtg(
            br#"
            interpretation english: de.up.ling.irtg.algebra.StringAlgebra
            interpretation german: de.up.ling.irtg.algebra.StringAlgebra

            S! -> r(A,B)
              [english] *(?1,?2)
              [german] *(?1,?2)

            A -> a
              [english] john
              [german] hans

            B -> b
              [english] watches
              [german] sieht
            "# as &[u8],
        )
        .unwrap();

        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();
        let german = irtg.interpretation::<StringAlgebra>("german").unwrap();
        let english_value = english.parse_object("john watches").unwrap();
        let german_value = german.parse_object("hans sieht").unwrap();
        let chart = irtg
            .parse([english.input(english_value), german.input(german_value)])
            .unwrap();
        assert!(!chart.automaton.is_empty());

        let english_value = english.parse_object("john watches").unwrap();
        let german_value = german.parse_object("hans schaut").unwrap();
        let chart = irtg
            .parse([english.input(english_value), german.input(german_value)])
            .unwrap();
        assert!(chart.automaton.is_empty());
    }

    #[test]
    fn reads_actual_alto_format_cfg_fixture() {
        let irtg = parse_irtg(include_bytes!("../benchdata/irtg/cfg.irtg").as_slice()).unwrap();
        let interpretation = irtg.interpretation::<StringAlgebra>("i").unwrap();
        let value = interpretation
            .parse_object("john watches the woman")
            .unwrap();
        let chart = irtg.parse([interpretation.input(value)]).unwrap();
        assert!(!chart.automaton.is_empty());
        assert_eq!(irtg.grammar().rules().count(), 12);
    }

    #[test]
    fn parses_features_comments_quoted_names_and_scientific_weights() {
        let irtg = parse_irtg(
            br#"
            interpretation 'surface': de.up.ling.irtg.algebra.StringAlgebra
            feature constructor: SomeFeature(A, B)
            /* block comment */
            'S root'! -> 'r root'('A one') [3.3921302578018993E-4]
              [surface] wrap(?1) // line comment

            'A one' -> leaf()
              [surface] 'hello world'
            "# as &[u8],
        )
        .unwrap();

        assert_eq!(irtg.grammar().rules().count(), 2);
        let parent = irtg.states().get(&"S root".to_owned()).unwrap();
        let symbol = irtg.grammar_signature().get("r root").unwrap();
        let rule = irtg
            .grammar()
            .rules()
            .find(|rule| rule.symbol == symbol)
            .unwrap();
        assert_eq!(rule.result, parent);
        assert!((rule.weight - 3.3921302578018993E-4).abs() < 1e-12);
        let surface = irtg.interpretation::<StringAlgebra>("surface").unwrap();
        assert!(surface.algebra_signature().get("wrap").is_some());
        assert!(surface.algebra_signature().get("hello world").is_some());
    }

    #[test]
    fn rejects_unknown_hom_interpretation() {
        let err = parse_irtg(
            br#"
            interpretation i: de.up.ling.irtg.algebra.StringAlgebra
            S! -> r
              [missing] x
            "# as &[u8],
        )
        .unwrap_err();
        assert!(matches!(err, IrtgError::UnknownInterpretation(name) if name == "missing"));
    }

    #[test]
    fn parse_irtg_rejects_invalid_utf8_reader() {
        let err = parse_irtg(&b"\xff"[..]).unwrap_err();
        assert!(matches!(err, IrtgError::Utf8(_)));
    }

    #[test]
    fn rejects_zero_variable() {
        let err = parse_irtg(
            br#"
            interpretation i: de.up.ling.irtg.algebra.StringAlgebra
            S! -> r(A)
              [i] ?0
            "# as &[u8],
        )
        .unwrap_err();
        assert!(matches!(err, IrtgError::Syntax(message) if message.contains("?0")));
    }

    #[test]
    fn rejects_duplicate_grammar_transitions() {
        let err = parse_irtg(
            br#"
            interpretation i: de.up.ling.irtg.algebra.StringAlgebra
            S! -> r [1.0]
            S! -> r [2.0]
            "# as &[u8],
        )
        .unwrap_err();
        assert!(matches!(err, IrtgError::Automaton(_)));
    }
}
