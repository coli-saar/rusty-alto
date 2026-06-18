//! Interpreted regular tree grammars.

use crate::{
    APPEND_SYMBOL, Algebra, Binarizing, DisplayCodec, Explicit, ExplicitBuildError, ExplicitBuilder,
    FxHashMap, Homomorphism, HomomorphismError, IndexedCondensedIntersectionStats, Interner, InvHom,
    MinHeuristic, ObligatoryLeafTables, OutputCodec, OutsideHeuristic, ScoredZeroHeuristic,
    Signature, SignatureError, SpaceJoinCodec, StateId, StringAlgebra, Symbol, TreeAlgebra,
    UniversalSxHeuristic, ViterbiTree, WeightScorer, ZeroHeuristic,
    alto_ast::{AstHomTerm, AstIrtg, AstState, LexError, Tok, lex},
    alto_grammar,
    astar::{
        AstarOptions, AstarStats, astar_string_one_best_with_stats,
        materialize_astar_string_intersection_with,
    },
    materialize::{
        materialize_indexed_condensed_intersection, materialize_topdown_condensed_intersection,
    },
};
use lalrpop_util::ParseError;
use rusty_tree::tree::{Tree, TreeArena};
use std::{any::Any, cell::RefCell, fmt, io::Read, marker::PhantomData};
use thiserror::Error;

const STRING_ALGEBRA: &str = "de.up.ling.irtg.algebra.StringAlgebra";
const TREE_WITH_ARITIES_ALGEBRA: &str = "de.up.ling.irtg.algebra.TreeWithAritiesAlgebra";
const BINARIZING_TREE_WITH_ARITIES_ALGEBRA: &str =
    "de.up.ling.irtg.algebra.BinarizingTreeWithAritiesAlgebra";

// ---------------------------------------------------------------------------
// Materialization strategy
// ---------------------------------------------------------------------------

/// Which algorithm to use when materializing an intersection inside [`Irtg::parse_with`].
pub enum MaterializationStrategy<'h> {
    /// Top-down condensed intersection (default, matches [`Irtg::parse`]).
    TopDownCondensed,
    /// Indexed condensed intersection.
    IndexedCondensed,
    /// A* intersection with a configurable heuristic.
    ///
    /// **Precondition**: all grammar rule weights must be ≤ 1 (probability
    /// weights).  If any weight exceeds 1 the strategy is rejected at
    /// parse time with [`IrtgError::AstarWeightPrecondition`].
    Astar {
        /// Heuristic to guide the A* search.
        heuristic: AstarHeuristic<'h>,
        /// Options for the A* materializer.
        options: AstarOptions,
    },
}

/// Heuristic choice for [`MaterializationStrategy::Astar`].
pub enum AstarHeuristic<'h> {
    /// Uninformed heuristic (always returns 1.0).  A* degenerates to Knuth
    /// order and is exact.
    Zero,
    /// Grammar-only outside-weight heuristic.  Algebra-agnostic and
    /// sentence-independent; compute once with [`OutsideHeuristic::from_grammar`].
    Outside(&'h OutsideHeuristic),
    /// Universal SX heuristic table built for `n_max`; `n` is the length of the
    /// current sentence.  The table is admissible for any sentence with `n ≤ n_max`.
    /// Build once with [`UniversalSxHeuristic::new`] and reuse across all sentences.
    UniversalSx {
        table: &'h UniversalSxHeuristic,
        n: usize,
    },
    /// Universal SX combined with the obligatory-leaf F filter via `min`. SX
    /// bounds outside *weight*; F prunes spans whose context cannot supply an
    /// obligatory leaf. Both are admissible, so the combination stays exact.
    /// `oblig` is grammar-only (build once); the per-input terminal supply is
    /// derived from the sentence at call time.
    UniversalSxF {
        table: &'h UniversalSxHeuristic,
        oblig: &'h ObligatoryLeafTables,
        n: usize,
    },
}

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

    /// Iterate over all interpretations (in unspecified order).
    pub fn interpretations(&self) -> impl Iterator<Item = &Interpretation> {
        self.interpretations.values()
    }

    /// Return a reference to a named interpretation, or `None` if absent.
    pub fn interpretation_ref(&self, name: &str) -> Option<&Interpretation> {
        self.interpretations.get(name)
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

    /// Parse with one or more interpretation inputs using the default strategy
    /// ([`MaterializationStrategy::TopDownCondensed`]).
    pub fn parse<'a>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
    ) -> Result<ParseChart, IrtgError> {
        self.parse_with(inputs, &MaterializationStrategy::TopDownCondensed)
    }

    /// Parse with one or more interpretation inputs, selecting the
    /// materialization algorithm via `strategy`.
    ///
    /// For [`MaterializationStrategy::Astar`] the precondition is that all
    /// grammar rule weights are ≤ 1.  If that is violated the method returns
    /// [`IrtgError::AstarWeightPrecondition`] immediately.
    pub fn parse_with<'a>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
    ) -> Result<ParseChart, IrtgError> {
        // Guard: A* requires probability weights (≤ 1).
        if matches!(strategy, MaterializationStrategy::Astar { .. }) {
            self.check_astar_weight_precondition()?;
        }

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
                    let next_chart = match strategy {
                        MaterializationStrategy::TopDownCondensed => {
                            let (c, _, stat) =
                                materialize_topdown_condensed_intersection(&chart, &invhom);
                            stats.push(stat);
                            c
                        }
                        MaterializationStrategy::IndexedCondensed => {
                            let (c, _, stat) =
                                materialize_indexed_condensed_intersection(&chart, &invhom);
                            stats.push(stat);
                            c
                        }
                        MaterializationStrategy::Astar {
                            heuristic,
                            options: _,
                        } => {
                            // We need owned options — clone by rebuilding (AstarOptions is not Clone).
                            // Instead, call materialize_astar_intersection with a fresh options value.
                            // We route via a helper to avoid duplicating logic.
                            let c = self.run_astar_chart(&chart, &invhom, heuristic, strategy)?;
                            // A* produces no IndexedCondensedIntersectionStats; we push nothing.
                            c
                        }
                    };
                    chart = next_chart;
                }
                InterpretationKind::OutputOnly => {
                    return Err(IrtgError::NotInputable {
                        interpretation: interpretation.name.clone(),
                    });
                }
            }
        }

        Ok(ParseChart {
            automaton: chart,
            stats,
        })
    }

    /// Return the single best parse tree (Viterbi tree) for the given inputs
    /// and strategy.
    ///
    /// For [`MaterializationStrategy::Astar`] this calls [`astar_one_best`]
    /// directly without building a full chart.  For chart-based strategies it
    /// falls back to [`Irtg::parse_with`] and calls `.automaton.viterbi()`.
    pub fn best_with<'a>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
    ) -> Result<Option<ViterbiTree>, IrtgError> {
        self.best_with_scorer(inputs, strategy, &crate::ProbabilityScorer)
    }

    /// Return the single best parse tree using `scorer` for weight products.
    pub fn best_with_scorer<'a, S: WeightScorer>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
        scorer: &S,
    ) -> Result<Option<ViterbiTree>, IrtgError> {
        self.best_with_scorer_and_stats(inputs, strategy, scorer)
            .map(|(tree, _)| tree)
    }

    /// Return the single best parse tree using `scorer`, plus A* stats when available.
    pub fn best_with_scorer_and_stats<'a, S: WeightScorer>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
        scorer: &S,
    ) -> Result<(Option<ViterbiTree>, Option<AstarStats>), IrtgError> {
        // For A* we can short-circuit and avoid building the chart.
        if let MaterializationStrategy::Astar { heuristic, .. } = strategy {
            // Guard
            self.check_astar_weight_precondition()?;

            // We need to iterate inputs and run astar_one_best on the last
            // grammar (after intersecting all inputs in order).  For simplicity
            // we run parse_with for all-but-last inputs (if any) and then do
            // astar_one_best for the final one.  In practice IRTGs usually have
            // a single string interpretation per parse call, so this is fast.
            let inputs: Vec<_> = inputs.into_iter().collect();
            if inputs.is_empty() {
                return Ok((self.grammar.viterbi_with(scorer), None));
            }

            // Split: all-but-last via parse_with(TopDownCondensed), then last via astar_one_best.
            let (last, rest) = inputs.split_last().unwrap();
            // Build intermediate chart from all-but-last inputs (if any).
            let intermediate_chart = if rest.is_empty() {
                self.grammar.clone()
            } else {
                // Collect rest as owned inputs — but ParseInput<'a> is not Clone.
                // We cannot split a Vec<ParseInput<'_>> this way because ParseInput doesn't
                // implement Clone.  Instead we re-collect from the iterator below.
                // Since we already consumed the iterator into a Vec, we need to handle
                // the rest of the inputs with their Box<dyn Any> values.
                // The simplest approach: call parse_with on rest using TopDownCondensed.
                // We cannot re-use ParseInput because it owns value; instead we call
                // materialize_topdown_condensed_intersection directly.
                //
                // NOTE: this path is only reached when there are 2+ inputs and the
                // caller uses Astar.  The typical single-interpretation use case avoids it.
                return self.best_with_multi(inputs, heuristic, strategy, scorer);
            };

            // Run astar_one_best for the last (only) input.
            let interpretation = last.interpretation;
            match interpretation.kind {
                InterpretationKind::String => {
                    let value = last
                        .value
                        .downcast_ref::<Vec<Symbol>>()
                        .ok_or_else(|| IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        })?
                        .clone();
                    let algebra = interpretation.algebra.borrow();
                    let algebra = algebra
                        .as_ref()
                        .downcast_ref::<StringAlgebra>()
                        .ok_or_else(|| IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        })?;
                    let decomp = algebra.decompose(value);
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    let (tree, stats) = self.run_astar_one_best_with_scorer(
                        &intermediate_chart,
                        &invhom,
                        heuristic,
                        scorer,
                    );
                    Ok((tree, Some(stats)))
                }
                InterpretationKind::OutputOnly => Err(IrtgError::NotInputable {
                    interpretation: interpretation.name.clone(),
                }),
            }
        } else {
            // Chart strategies: build the chart and run Viterbi on it.
            let chart = self.parse_with(inputs, strategy)?;
            Ok((chart.automaton.viterbi_with(scorer), None))
        }
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    /// Check the A* weight precondition: all grammar rule weights must be ≤ 1.
    fn check_astar_weight_precondition(&self) -> Result<(), IrtgError> {
        for rule in self.grammar.rules() {
            if rule.weight > 1.0 {
                // `Signature::resolve` panics if the symbol is absent; use
                // a bounds check first since all interned rules should be present.
                let symbol = if (rule.symbol.0 as usize) < self.grammar_signature.len() {
                    self.grammar_signature.resolve(rule.symbol).to_owned()
                } else {
                    format!("{:?}", rule.symbol)
                };
                return Err(IrtgError::AstarWeightPrecondition {
                    weight: rule.weight,
                    symbol,
                });
            }
        }
        Ok(())
    }

    /// Run A* chart materializer for a single `InvHom<StringDecompositionAutomaton>`.
    fn run_astar_chart(
        &self,
        chart: &Explicit,
        invhom: &InvHom<'_, crate::algebras::StringDecompositionAutomaton>,
        heuristic: &AstarHeuristic<'_>,
        strategy: &MaterializationStrategy<'_>,
    ) -> Result<Explicit, IrtgError> {
        let options = match strategy {
            MaterializationStrategy::Astar { options, .. } => AstarOptions {
                stop_at_first_goal: options.stop_at_first_goal,
                beam: options.beam,
            },
            _ => unreachable!(),
        };
        let (new_chart, _, _) = match heuristic {
            AstarHeuristic::Zero => {
                let h = ZeroHeuristic;
                materialize_astar_string_intersection_with(
                    chart,
                    invhom,
                    &h,
                    options,
                    &crate::ProbabilityScorer,
                )
            }
            AstarHeuristic::Outside(h) => materialize_astar_string_intersection_with(
                chart,
                invhom,
                *h,
                options,
                &crate::ProbabilityScorer,
            ),
            AstarHeuristic::UniversalSx { table, n } => {
                let h = table.for_sentence(*n);
                materialize_astar_string_intersection_with(
                    chart,
                    invhom,
                    &h,
                    options,
                    &crate::ProbabilityScorer,
                )
            }
            AstarHeuristic::UniversalSxF { table, oblig, n } => {
                let sx = table.for_sentence(*n);
                let f = oblig.for_sentence(invhom.inner().sentence(), &crate::ProbabilityScorer);
                let h = MinHeuristic::new(sx, f);
                materialize_astar_string_intersection_with(
                    chart,
                    invhom,
                    &h,
                    options,
                    &crate::ProbabilityScorer,
                )
            }
        };
        Ok(new_chart)
    }

    /// Run `astar_one_best` for a single `InvHom<StringDecompositionAutomaton>`.
    fn run_astar_one_best_with_scorer<S: WeightScorer>(
        &self,
        chart: &Explicit,
        invhom: &InvHom<'_, crate::algebras::StringDecompositionAutomaton>,
        heuristic: &AstarHeuristic<'_>,
        scorer: &S,
    ) -> (Option<ViterbiTree>, AstarStats) {
        match heuristic {
            AstarHeuristic::Zero => {
                let h = ScoredZeroHeuristic::new(scorer);
                astar_string_one_best_with_stats(chart, invhom, &h, scorer)
            }
            AstarHeuristic::Outside(h) => {
                astar_string_one_best_with_stats(chart, invhom, *h, scorer)
            }
            AstarHeuristic::UniversalSx { table, n } => {
                let h = table.for_sentence(*n);
                astar_string_one_best_with_stats(chart, invhom, &h, scorer)
            }
            AstarHeuristic::UniversalSxF { table, oblig, n } => {
                let sx = table.for_sentence(*n);
                let f = oblig.for_sentence(invhom.inner().sentence(), scorer);
                let h = MinHeuristic::new(sx, f);
                astar_string_one_best_with_stats(chart, invhom, &h, scorer)
            }
        }
    }

    /// Fallback for `best_with` when there are 2+ inputs with A* strategy.
    /// Runs all inputs using TopDownCondensed, then A* on the last one.
    fn best_with_multi<'a, S: WeightScorer>(
        &self,
        inputs: Vec<ParseInput<'a>>,
        heuristic: &AstarHeuristic<'_>,
        _strategy: &MaterializationStrategy<'_>,
        scorer: &S,
    ) -> Result<(Option<ViterbiTree>, Option<AstarStats>), IrtgError> {
        // We can't clone ParseInput, so we process them one by one.
        let n = inputs.len();
        let mut chart = self.grammar.clone();

        for (i, input) in inputs.into_iter().enumerate() {
            let interpretation = input.interpretation;
            let is_last = i == n - 1;
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
                    if is_last {
                        let (tree, stats) =
                            self.run_astar_one_best_with_scorer(&chart, &invhom, heuristic, scorer);
                        return Ok((tree, Some(stats)));
                    } else {
                        let (next, _, _) =
                            materialize_topdown_condensed_intersection(&chart, &invhom);
                        chart = next;
                    }
                }
                InterpretationKind::OutputOnly => {
                    return Err(IrtgError::NotInputable {
                        interpretation: interpretation.name.clone(),
                    });
                }
            }
        }

        Ok((chart.viterbi_with(scorer), None))
    }
}

/// Object-safe bridge that interprets a derivation tree through an interpretation's
/// homomorphism and algebra, then renders the resulting value with a fixed output codec.
///
/// One concrete `Box<dyn DerivationRenderer>` is bound per algebra when the IRTG is built,
/// so [`Interpretation`] can render values without the caller knowing concrete algebra types.
trait DerivationRenderer: fmt::Debug {
    fn render(
        &self,
        algebra: &dyn Any,
        homomorphism: &Homomorphism,
        arena: &TreeArena<Symbol>,
        root: Tree,
        name: &str,
    ) -> Result<String, IrtgError>;
}

/// [`DerivationRenderer`] for a concrete algebra `A` paired with codec `C`.
struct TypedDerivationCodec<A, C> {
    codec: C,
    _algebra: PhantomData<fn() -> A>,
}

impl<A, C> TypedDerivationCodec<A, C> {
    fn new(codec: C) -> Self {
        Self {
            codec,
            _algebra: PhantomData,
        }
    }
}

// Manual `Debug` so the bound is only on `C` (the derive would also require `A: Debug`).
impl<A, C: fmt::Debug> fmt::Debug for TypedDerivationCodec<A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TypedDerivationCodec")
            .field("codec", &self.codec)
            .finish()
    }
}

impl<A, C> DerivationRenderer for TypedDerivationCodec<A, C>
where
    A: Algebra + 'static,
    C: OutputCodec<A::Value> + fmt::Debug,
{
    fn render(
        &self,
        algebra: &dyn Any,
        homomorphism: &Homomorphism,
        arena: &TreeArena<Symbol>,
        root: Tree,
        name: &str,
    ) -> Result<String, IrtgError> {
        let algebra = algebra
            .downcast_ref::<A>()
            .ok_or_else(|| IrtgError::WrongInputType {
                interpretation: name.to_owned(),
            })?;
        // Map the derivation tree through the homomorphism, then evaluate in the algebra.
        let mut image = TreeArena::new();
        let image_root = homomorphism.apply(arena, root, &mut image)?;
        let value =
            algebra
                .evaluate_term(&image, image_root)
                .ok_or_else(|| IrtgError::ObjectParse {
                    interpretation: name.to_owned(),
                    message: "derivation tree did not evaluate in the algebra".to_owned(),
                })?;
        Ok(self.codec.encode(&value))
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
    renderer: Box<dyn DerivationRenderer>,
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

    /// Return whether this interpretation can serve as a parse input (its algebra is decomposable).
    /// Output-only interpretations (e.g. tree algebras) return `false`.
    pub fn is_inputable(&self) -> bool {
        matches!(self.kind, InterpretationKind::String)
    }

    /// Parse a textual object with this interpretation's algebra, returning a type-erased
    /// value suitable for [`input_erased`](Self::input_erased).
    pub fn parse_object_erased(&self, input: &str) -> Result<Box<dyn Any>, IrtgError> {
        match self.kind {
            InterpretationKind::String => {
                let mut algebra = self.algebra.borrow_mut();
                let algebra = algebra
                    .as_mut()
                    .downcast_mut::<StringAlgebra>()
                    .ok_or_else(|| IrtgError::WrongInputType {
                        interpretation: self.name.clone(),
                    })?;
                let value =
                    algebra
                        .parse_object(input)
                        .map_err(|err| IrtgError::ObjectParse {
                            interpretation: self.name.clone(),
                            message: err.to_string(),
                        })?;
                Ok(Box::new(value))
            }
            InterpretationKind::OutputOnly => Err(IrtgError::ObjectParse {
                interpretation: self.name.clone(),
                message: "interpretation is output-only and cannot be parsed as a parse input"
                    .to_owned(),
            }),
        }
    }

    /// Package a type-erased value (from [`parse_object_erased`](Self::parse_object_erased))
    /// as a [`ParseInput`] for [`Irtg::parse`].
    pub fn input_erased(&self, value: Box<dyn Any>) -> ParseInput<'_> {
        ParseInput {
            interpretation: self,
            value,
        }
    }

    /// Interpret a derivation tree (over grammar symbols) through this interpretation and
    /// render the resulting algebra value as text using the interpretation's output codec.
    pub fn interpret_to_string(
        &self,
        arena: &TreeArena<Symbol>,
        root: Tree,
    ) -> Result<String, IrtgError> {
        let algebra = self.algebra.borrow();
        self.renderer
            .render(&**algebra, &self.homomorphism, arena, root, &self.name)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InterpretationKind {
    /// A [`StringAlgebra`] interpretation: can be a parse input (decomposable).
    String,
    /// An output-only interpretation (e.g. a tree algebra): values can be produced from a
    /// derivation tree, but the algebra cannot be decomposed for use as a parse input.
    OutputOnly,
}

/// Typed access to an interpretation.
pub struct TypedInterpretation<'i, A> {
    interpretation: &'i Interpretation,
    _algebra: PhantomData<A>,
}

impl<'i, A> TypedInterpretation<'i, A>
where
    A: Algebra + 'static,
    A::InternalValue: 'static,
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

    /// Parse a textual object using the interpretation's algebra (to its internal value).
    pub fn parse_object(&self, input: &str) -> Result<A::InternalValue, IrtgError> {
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

    /// Package a typed internal value as an input for [`Irtg::parse`].
    pub fn input(&self, value: A::InternalValue) -> ParseInput<'i> {
        ParseInput {
            interpretation: self.interpretation,
            value: Box::new(value),
        }
    }

    /// Interpret a derivation tree and return the typed external algebra value.
    pub fn interpret_derivation(
        &self,
        arena: &TreeArena<Symbol>,
        root: Tree,
    ) -> Result<A::Value, IrtgError> {
        let algebra = self.interpretation.algebra.borrow();
        let algebra =
            algebra
                .as_ref()
                .downcast_ref::<A>()
                .ok_or_else(|| IrtgError::WrongInputType {
                    interpretation: self.interpretation.name.clone(),
                })?;
        let mut image = TreeArena::new();
        let image_root = self
            .interpretation
            .homomorphism
            .apply(arena, root, &mut image)?;
        algebra
            .evaluate_term(&image, image_root)
            .ok_or_else(|| IrtgError::ObjectParse {
                interpretation: self.interpretation.name.clone(),
                message: "derivation tree did not evaluate in the algebra".to_owned(),
            })
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
    /// An output-only interpretation was used as a parse input.
    #[error("interpretation {interpretation:?} is output-only and cannot be a parse input")]
    NotInputable {
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
    /// A* strategy requires all grammar rule weights ≤ 1 (probability weights).
    #[error(
        "A* requires all grammar rule weights ≤ 1, but found weight {weight} for rule {symbol:?}"
    )]
    AstarWeightPrecondition {
        /// The offending weight.
        weight: f64,
        /// The grammar symbol name of the offending rule.
        symbol: String,
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
        let (kind, algebra, algebra_signature, renderer): (
            InterpretationKind,
            Box<dyn Any>,
            Signature,
            Box<dyn DerivationRenderer>,
        ) = if decl.algebra == STRING_ALGEBRA {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let algebra = StringAlgebra::with_signature(signature.clone());
            let renderer = Box::new(TypedDerivationCodec::<StringAlgebra, SpaceJoinCodec>::new(
                SpaceJoinCodec,
            ));
            (
                InterpretationKind::String,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else if decl.algebra == TREE_WITH_ARITIES_ALGEBRA {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let algebra = TreeAlgebra::with_arities(signature.clone());
            let renderer =
                Box::new(TypedDerivationCodec::<TreeAlgebra, DisplayCodec>::new(DisplayCodec));
            (
                InterpretationKind::OutputOnly,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else if decl.algebra == BINARIZING_TREE_WITH_ARITIES_ALGEBRA {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let append = signature.get(APPEND_SYMBOL);
            let algebra = Binarizing::new(TreeAlgebra::with_arities(signature.clone()), append);
            let renderer = Box::new(TypedDerivationCodec::<
                Binarizing<TreeAlgebra>,
                DisplayCodec,
            >::new(DisplayCodec));
            (
                InterpretationKind::OutputOnly,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else {
            return Err(IrtgError::UnsupportedAlgebra {
                interpretation: decl.name.clone(),
                class_name: decl.algebra.clone(),
            });
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
                renderer,
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
    fn typed_interpretation_returns_tree_value_without_rendering() {
        let irtg = parse_irtg(
            br#"
            interpretation string: de.up.ling.irtg.algebra.StringAlgebra
            interpretation tree: de.up.ling.irtg.algebra.TreeWithAritiesAlgebra

            S! -> r(A,B)
              [string] *(?1,?2)
              [tree] S_2(?1,?2)

            A -> a
              [string] a
              [tree] NN_1(a_0)

            B -> b
              [string] b
              [tree] VB_1(b_0)
            "# as &[u8],
        )
        .unwrap();

        let string = irtg.interpretation::<StringAlgebra>("string").unwrap();
        let input = string.parse_object("a b").unwrap();
        let best = irtg
            .best_with(
                [string.input(input)],
                &MaterializationStrategy::TopDownCondensed,
            )
            .unwrap()
            .unwrap();
        let tree = irtg.interpretation::<TreeAlgebra>("tree").unwrap();
        let value = tree
            .interpret_derivation(best.arena(), best.root())
            .unwrap();
        assert_eq!(value.to_string(), "S(NN(a), VB(b))");
        assert_eq!(value.arena().get_label(value.root()), "S");
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

    // -----------------------------------------------------------------------
    // Phase E: MaterializationStrategy tests
    // -----------------------------------------------------------------------

    fn tiny_irtg_bytes() -> &'static [u8] {
        br#"
        interpretation english: de.up.ling.irtg.algebra.StringAlgebra

        S! -> r(NP,VP) [1.0]
          [english] *(?1,?2)

        NP -> john_rule [1.0]
          [english] john

        VP -> watches_rule [1.0]
          [english] watches
        "#
    }

    #[test]
    fn parse_with_top_down_condensed_matches_parse() {
        let irtg = parse_irtg(tiny_irtg_bytes()).unwrap();
        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();

        let value = english.parse_object("john watches").unwrap();
        let chart_default = irtg.parse([english.input(value.clone())]).unwrap();

        let chart_explicit = irtg
            .parse_with(
                [english.input(value)],
                &MaterializationStrategy::TopDownCondensed,
            )
            .unwrap();

        // Both strategies should agree on emptiness.
        assert_eq!(
            chart_default.automaton.is_empty(),
            chart_explicit.automaton.is_empty()
        );
        assert!(!chart_explicit.automaton.is_empty());
    }

    #[test]
    fn parse_with_indexed_condensed_works() {
        let irtg = parse_irtg(tiny_irtg_bytes()).unwrap();
        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();

        let value = english.parse_object("john watches").unwrap();
        let chart = irtg
            .parse_with(
                [english.input(value)],
                &MaterializationStrategy::IndexedCondensed,
            )
            .unwrap();

        assert!(!chart.automaton.is_empty());

        // Rejection case.
        let bad = english.parse_object("john sleeps").unwrap();
        let chart = irtg
            .parse_with(
                [english.input(bad)],
                &MaterializationStrategy::IndexedCondensed,
            )
            .unwrap();
        assert!(chart.automaton.is_empty());
    }

    #[test]
    fn parse_with_astar_zero_returns_non_empty_chart_for_known_sentence() {
        let irtg = parse_irtg(tiny_irtg_bytes()).unwrap();
        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();

        let value = english.parse_object("john watches").unwrap();
        let chart = irtg
            .parse_with(
                [english.input(value)],
                &MaterializationStrategy::Astar {
                    heuristic: AstarHeuristic::Zero,
                    options: AstarOptions {
                        stop_at_first_goal: true,
                        beam: None,
                    },
                },
            )
            .unwrap();

        assert!(!chart.automaton.is_empty());
    }

    #[test]
    fn astar_strategy_rejects_grammar_with_weight_greater_than_one() {
        let irtg = parse_irtg(
            br#"
            interpretation i: de.up.ling.irtg.algebra.StringAlgebra

            S! -> r [5.0]
              [i] hello

            "# as &[u8],
        )
        .unwrap();

        let interp = irtg.interpretation::<StringAlgebra>("i").unwrap();
        let value = interp.parse_object("hello").unwrap();

        let err = irtg
            .parse_with(
                [interp.input(value)],
                &MaterializationStrategy::Astar {
                    heuristic: AstarHeuristic::Zero,
                    options: AstarOptions {
                        stop_at_first_goal: true,
                        beam: None,
                    },
                },
            )
            .unwrap_err();

        assert!(
            matches!(err, IrtgError::AstarWeightPrecondition { weight, .. } if weight > 1.0),
            "expected AstarWeightPrecondition, got {:?}",
            err
        );
    }

    #[test]
    fn astar_weight_precondition_error_contains_weight_and_symbol() {
        let irtg = parse_irtg(
            br#"
            interpretation i: de.up.ling.irtg.algebra.StringAlgebra

            S! -> my_rule [3.5]
              [i] hello
            "# as &[u8],
        )
        .unwrap();

        let interp = irtg.interpretation::<StringAlgebra>("i").unwrap();
        let value = interp.parse_object("hello").unwrap();

        let err = irtg
            .parse_with(
                [interp.input(value)],
                &MaterializationStrategy::Astar {
                    heuristic: AstarHeuristic::Zero,
                    options: AstarOptions {
                        stop_at_first_goal: true,
                        beam: None,
                    },
                },
            )
            .unwrap_err();

        if let IrtgError::AstarWeightPrecondition { weight, symbol } = &err {
            assert!((weight - 3.5).abs() < 1e-10);
            assert!(symbol.contains("my_rule"), "symbol = {symbol}");
        } else {
            panic!("expected AstarWeightPrecondition, got {:?}", err);
        }

        // Check error message.
        let msg = err.to_string();
        assert!(msg.contains("3.5") || msg.contains("A*"), "message = {msg}");
    }

    #[test]
    fn best_with_astar_returns_some_for_known_sentence() {
        let irtg = parse_irtg(tiny_irtg_bytes()).unwrap();
        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();

        let value = english.parse_object("john watches").unwrap();
        let result = irtg
            .best_with(
                [english.input(value)],
                &MaterializationStrategy::Astar {
                    heuristic: AstarHeuristic::Zero,
                    options: AstarOptions {
                        stop_at_first_goal: true,
                        beam: None,
                    },
                },
            )
            .unwrap();

        assert!(result.is_some(), "expected a best tree for 'john watches'");
    }

    #[test]
    fn best_with_chart_strategy_returns_some_for_known_sentence() {
        let irtg = parse_irtg(tiny_irtg_bytes()).unwrap();
        let english = irtg.interpretation::<StringAlgebra>("english").unwrap();

        let value = english.parse_object("john watches").unwrap();
        let result = irtg
            .best_with(
                [english.input(value)],
                &MaterializationStrategy::TopDownCondensed,
            )
            .unwrap();

        assert!(result.is_some(), "expected a best tree for 'john watches'");
    }
}
