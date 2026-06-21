//! Interpreted regular tree grammars.

use crate::{
    APPEND_SYMBOL, Algebra, BinarizedTagTreeDecompositionAutomaton, Binarizing, BottomUpTa,
    CodecMetadata, CondensedTa, DisplayCodec, Explicit, ExplicitBuildError, ExplicitBuilder,
    FeatureStructure, FeatureStructureAlgebra, FxHashMap, FxHashSet, Homomorphism,
    HomomorphismError, IndexedCondensedIntersectionStats, Interner, InvHom, MinHeuristic,
    ObligatoryLeafTables, OutputCodec, OutputCodecError, OutputCodecRegistry, OutsideHeuristic,
    ParseControl, ScoredZeroHeuristic, Signature, SignatureError, SpaceJoinCodec, StateId,
    StateUniverse, StringAlgebra, Symbol, TagStringAlgebra, TagStringDecompositionAutomaton,
    TagStringValue, TagTreeAlgebra, TagTreeDecompositionAutomaton, TopDownTa, TreeAlgebra,
    UniversalSxHeuristic, VisualRepresentation, ViterbiTree, WeightScorer, ZeroHeuristic,
    alto_ast::{AstHomTerm, AstIrtg, AstState, LexError, Tok, lex},
    alto_grammar,
    astar::{
        AstarOptions, AstarStats, PreparedAstarGrammar, astar_one_best_with_stats,
        astar_string_one_best_with_stats, astar_string_one_best_with_stats_prepared,
        materialize_astar_intersection_with_pairs_controlled,
        materialize_astar_string_intersection_with_controlled,
    },
    materialize::{
        materialize_indexed_condensed_intersection_with_pairs_controlled,
        materialize_topdown_condensed_intersection,
        materialize_topdown_condensed_intersection_with_pairs_controlled,
    },
};
use lalrpop_util::ParseError;
use packed_term_arena::tree::{Tree, TreeArena};
use std::{
    any::Any,
    fmt,
    hash::Hash,
    io::Read,
    marker::PhantomData,
    sync::{Arc, Mutex},
};
use thiserror::Error;

fn product_state_names<S: Clone + Eq + Hash + fmt::Display>(
    left_names: &[String],
    right_states: &Interner<S>,
    pairs: &[(StateId, StateId)],
) -> Vec<String> {
    pairs
        .iter()
        .map(|&(left, right)| {
            let left = left_names
                .get(left.index())
                .cloned()
                .unwrap_or_else(|| format!("q{}", left.0));
            format!("{left} × {}", right_states.resolve(right))
        })
        .collect()
}

fn filter_feature_chart(
    chart: &Explicit,
    algebra: &FeatureStructureAlgebra,
    homomorphism: &Homomorphism,
    control: &ParseControl,
) -> Result<NonNullFilteredChart, IrtgError> {
    control.check().map_err(|_| IrtgError::Cancelled)?;
    let filter = InvHom::new(algebra.filter(), homomorphism);
    let rules: Vec<_> = chart
        .rules()
        .map(|rule| {
            (
                rule.symbol,
                rule.children.to_vec(),
                rule.result,
                rule.weight,
            )
        })
        .collect();
    let mut builder = ExplicitBuilder::new();
    let mut pair_ids = FxHashMap::<(StateId, FeatureStructure), StateId>::default();
    let mut value_ids = FxHashMap::<FeatureStructure, usize>::default();
    let mut state_origins = Vec::<(StateId, usize)>::new();
    let mut variants = vec![Vec::<(FeatureStructure, StateId)>::new(); chart.num_states() as usize];
    let mut emitted = FxHashSet::<(Symbol, Vec<StateId>, StateId)>::default();

    let intern = |left: StateId,
                  value: FeatureStructure,
                  builder: &mut ExplicitBuilder,
                  pair_ids: &mut FxHashMap<(StateId, FeatureStructure), StateId>,
                  value_ids: &mut FxHashMap<FeatureStructure, usize>,
                  state_origins: &mut Vec<(StateId, usize)>,
                  variants: &mut [Vec<(FeatureStructure, StateId)>]| {
        if let Some(&id) = pair_ids.get(&(left, value.clone())) {
            return (id, false);
        }
        let next_value_id = value_ids.len();
        let value_id = *value_ids.entry(value.clone()).or_insert(next_value_id);
        let id = builder.new_state();
        if chart.is_accepting(&left) {
            builder.add_accepting(id);
        }
        pair_ids.insert((left, value.clone()), id);
        state_origins.push((left, value_id));
        variants[left.index()].push((value, id));
        (id, true)
    };

    let mut changed = true;
    while changed {
        control.check().map_err(|_| IrtgError::Cancelled)?;
        changed = false;
        for (symbol, children, result, weight) in &rules {
            control.check().map_err(|_| IrtgError::Cancelled)?;
            if children.is_empty() {
                filter.step(*symbol, &[], &mut |value| {
                    if control.is_cancelled() {
                        return;
                    }
                    let (parent, is_new) = intern(
                        *result,
                        value,
                        &mut builder,
                        &mut pair_ids,
                        &mut value_ids,
                        &mut state_origins,
                        &mut variants,
                    );
                    changed |= is_new;
                    if emitted.insert((*symbol, Vec::new(), parent)) {
                        builder.add_weighted_rule(*symbol, Vec::new(), parent, *weight);
                    }
                });
                continue;
            }
            if children
                .iter()
                .any(|child| variants[child.index()].is_empty())
            {
                continue;
            }
            let pool_storage: Vec<_> = children
                .iter()
                .map(|child| variants[child.index()].clone())
                .collect();
            let pools: Vec<_> = pool_storage.iter().map(Vec::as_slice).collect();
            crate::run::cartesian_product(&pools, |combination| {
                if control.is_cancelled() {
                    return;
                }
                let child_values: Vec<_> =
                    combination.iter().map(|(value, _)| value.clone()).collect();
                let child_ids: Vec<_> = combination.iter().map(|(_, id)| *id).collect();
                filter.step(*symbol, &child_values, &mut |value| {
                    if control.is_cancelled() {
                        return;
                    }
                    let (parent, is_new) = intern(
                        *result,
                        value,
                        &mut builder,
                        &mut pair_ids,
                        &mut value_ids,
                        &mut state_origins,
                        &mut variants,
                    );
                    changed |= is_new;
                    if emitted.insert((*symbol, child_ids.clone(), parent)) {
                        builder.add_weighted_rule(*symbol, child_ids.clone(), parent, *weight);
                    }
                });
            });
            control.check().map_err(|_| IrtgError::Cancelled)?;
        }
    }
    Ok(NonNullFilteredChart {
        automaton: builder.build(),
        state_origins,
    })
}

/// A chart filtered to terms whose interpretation evaluates successfully.
#[derive(Debug)]
pub struct NonNullFilteredChart {
    /// Filtered automaton.
    pub automaton: Explicit,
    /// For each filtered state, its source-chart state and dense filter-state ID.
    pub state_origins: Vec<(StateId, usize)>,
}

const STRING_ALGEBRA: &str = "de.up.ling.irtg.algebra.StringAlgebra";
const TAG_STRING_ALGEBRA: &str = "de.up.ling.irtg.algebra.TagStringAlgebra";
const TAG_TREE_ALGEBRA: &str = "de.up.ling.irtg.algebra.TagTreeAlgebra";
const TAG_TREE_WITH_ARITIES_ALGEBRA: &str = "de.up.ling.irtg.algebra.TagTreeWithAritiesAlgebra";
const BINARIZING_TAG_TREE_ALGEBRA: &str = "de.up.ling.irtg.algebra.BinarizingTagTreeAlgebra";
const BINARIZING_TAG_TREE_WITH_ARITIES_ALGEBRA: &str =
    "de.up.ling.irtg.algebra.BinarizingTagTreeWithAritiesAlgebra";
const FEATURE_STRUCTURE_ALGEBRA: &str = "de.up.ling.irtg.algebra.FeatureStructureAlgebra";
const TREE_WITH_ARITIES_ALGEBRA: &str = "de.up.ling.irtg.algebra.TreeWithAritiesAlgebra";
const BINARIZING_TREE_WITH_ARITIES_ALGEBRA: &str =
    "de.up.ling.irtg.algebra.BinarizingTreeWithAritiesAlgebra";

// ---------------------------------------------------------------------------
// Materialization strategy
// ---------------------------------------------------------------------------

/// Which algorithm to use when materializing an intersection.
///
/// The strategies recognize the same derivations but explore the product
/// automaton differently:
///
/// - [`TopDownCondensed`](Self::TopDownCondensed) is the recommended default
///   when a complete chart is needed.
/// - [`IndexedCondensed`](Self::IndexedCondensed) is primarily useful for
///   algorithm comparison, statistics, or workloads where benchmarking shows
///   it is advantageous. It can generate very large candidate sets for some
///   ambiguous or discontinuous decompositions.
/// - [`Astar`](Self::Astar) is intended for weight-directed search and can stop
///   early when only the best derivation is needed.
///
/// Strategy choice depends on the resulting IRTG, its decomposition automata,
/// and representative inputs—not on the grammar's source filename or codec.
/// See the
/// [parsing-algorithm guide](https://github.com/coli-saar/rusty-alto/wiki/Parsing-Algorithms)
/// for a user-facing comparison.
pub enum MaterializationStrategy<'h> {
    /// Top-down condensed intersection.
    ///
    /// This is the default used by [`Irtg::parse`]. It starts from accepting
    /// product states and follows compatible condensed rules downward,
    /// producing a complete explicit parse chart.
    ///
    /// Prefer this as the general chart-building default unless measurements
    /// on the intended workload support another choice.
    TopDownCondensed,
    /// Bottom-up indexed condensed intersection.
    ///
    /// This grows reachable product states through partial-child indexes and
    /// returns detailed intersection statistics. It also produces a complete
    /// chart; it is not an early-exit one-best parser.
    ///
    /// Candidate generation can become substantially more expensive than the
    /// top-down strategy for some workloads, including some TAG-derived IRTGs.
    /// This is a property of the automata and inputs, not of a `.tag` filename.
    IndexedCondensed,
    /// A* intersection with a configurable heuristic.
    ///
    /// **Precondition**: all grammar rule weights must be ≤ 1 (probability
    /// weights).  If any weight exceeds 1 the strategy is rejected at
    /// parse time with [`IrtgError::AstarWeightPrecondition`].
    ///
    /// Use this when weight-directed search or early one-best termination is
    /// more important than constructing the complete parse chart. Heuristic
    /// compatibility depends on the input algebra; SX-family heuristics are
    /// specific to compatible string interpretations.
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
        /// Precomputed universal SX table.
        table: &'h UniversalSxHeuristic,
        /// Current sentence length.
        n: usize,
    },
    /// Universal SX combined with the obligatory-leaf F filter via `min`. SX
    /// bounds outside *weight*; F prunes spans whose context cannot supply an
    /// obligatory leaf. Both are admissible, so the combination stays exact.
    /// `oblig` is grammar-only (build once); the per-input terminal supply is
    /// derived from the sentence at call time.
    UniversalSxF {
        /// Precomputed universal SX table.
        table: &'h UniversalSxHeuristic,
        /// Grammar-level obligatory-leaf tables.
        oblig: &'h ObligatoryLeafTables,
        /// Current sentence length.
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

    /// Return the names of all interpretations that can be used as parse inputs.
    pub fn input_interpretation_names(&self) -> Vec<&str> {
        let mut names: Vec<_> = self
            .interpretations
            .values()
            .filter(|interpretation| interpretation.is_inputable())
            .map(|interpretation| interpretation.name.as_str())
            .collect();
        names.sort_unstable();
        names
    }

    /// Filter a parse chart to derivations whose feature-structure interpretation
    /// evaluates successfully.
    pub fn filter_non_null(
        &self,
        chart: &Explicit,
        interpretation_name: &str,
    ) -> Result<Explicit, IrtgError> {
        Ok(self
            .filter_non_null_with_state_origins(chart, interpretation_name)?
            .automaton)
    }

    /// Filter a chart while retaining source-state provenance for display.
    pub fn filter_non_null_with_state_origins(
        &self,
        chart: &Explicit,
        interpretation_name: &str,
    ) -> Result<NonNullFilteredChart, IrtgError> {
        self.filter_non_null_with_state_origins_controlled(
            chart,
            interpretation_name,
            &ParseControl::new(),
        )
    }

    /// Filter a chart while allowing another thread to request cancellation.
    ///
    /// This is the cancellable counterpart of
    /// [`Self::filter_non_null_with_state_origins`]. Clones of `control` may be
    /// held by another thread. If cancellation is observed, the method returns
    /// [`IrtgError::Cancelled`] and discards the partial filtered chart.
    ///
    /// Cancellation is cooperative and is checked at safe points during the
    /// feature-structure fixpoint computation.
    pub fn filter_non_null_with_state_origins_controlled(
        &self,
        chart: &Explicit,
        interpretation_name: &str,
        control: &ParseControl,
    ) -> Result<NonNullFilteredChart, IrtgError> {
        let interpretation = self
            .interpretations
            .get(interpretation_name)
            .ok_or_else(|| IrtgError::UnknownInterpretation(interpretation_name.to_owned()))?;
        if !interpretation.supports_non_null_filter() {
            return Err(IrtgError::NonNullFilterUnsupported {
                interpretation: interpretation_name.to_owned(),
                class_name: interpretation.class_name.clone(),
            });
        }
        let algebra = interpretation.algebra.lock().unwrap();
        let algebra = algebra
            .as_ref()
            .downcast_ref::<FeatureStructureAlgebra>()
            .expect("non-null filter capability must match its algebra");
        filter_feature_chart(chart, algebra, &interpretation.homomorphism, control)
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
        if interpretation.algebra.lock().unwrap().as_ref().is::<A>() {
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
        self.parse_with_control(inputs, strategy, &ParseControl::new())
    }

    /// Parse with a strategy and a cooperative cancellation control.
    ///
    /// The control may be cloned and canceled from another thread. On
    /// cancellation this method returns [`IrtgError::Cancelled`] and discards
    /// any partial chart. Cancellation is checked at safe points and therefore
    /// does not forcibly terminate the parsing thread.
    ///
    /// Use [`Self::parse`] or [`Self::parse_with`] when cancellation is not
    /// needed.
    pub fn parse_with_control<'a>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
        control: &ParseControl,
    ) -> Result<ParseChart, IrtgError> {
        control.check().map_err(|_| IrtgError::Cancelled)?;
        // Guard: A* requires probability weights (≤ 1).
        if matches!(strategy, MaterializationStrategy::Astar { .. }) {
            self.check_astar_weight_precondition()?;
        }

        let mut chart = self.grammar.clone();
        let mut state_names = (0..chart.num_states())
            .map(|state| self.states.resolve(StateId(state)).clone())
            .collect::<Vec<_>>();
        let mut stats = Vec::new();

        for input in inputs {
            control.check().map_err(|_| IrtgError::Cancelled)?;
            let interpretation = input.interpretation;
            match interpretation.kind {
                InterpretationKind::String => {
                    let value = *input.value.downcast::<Vec<Symbol>>().map_err(|_| {
                        IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        }
                    })?;
                    let decomp = interpretation.decompose_string(value)?;
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    let next_chart = match strategy {
                        MaterializationStrategy::TopDownCondensed => {
                            let (c, right_states, pairs, stat) =
                                materialize_topdown_condensed_intersection_with_pairs_controlled(
                                    &chart, &invhom, control,
                                )
                                .map_err(|_| IrtgError::Cancelled)?;
                            state_names = pairs
                                .into_iter()
                                .map(|(left, right)| {
                                    let span = right_states.resolve(right);
                                    format!(
                                        "{}[{},{}]",
                                        state_names[left.index()],
                                        span.start,
                                        span.end
                                    )
                                })
                                .collect();
                            stats.push(stat);
                            c
                        }
                        MaterializationStrategy::IndexedCondensed => {
                            let (c, right_states, pairs, stat) =
                                materialize_indexed_condensed_intersection_with_pairs_controlled(
                                    &chart, &invhom, control,
                                )
                                .map_err(|_| IrtgError::Cancelled)?;
                            state_names = pairs
                                .into_iter()
                                .map(|(left, right)| {
                                    let span = right_states.resolve(right);
                                    format!(
                                        "{}[{},{}]",
                                        state_names[left.index()],
                                        span.start,
                                        span.end
                                    )
                                })
                                .collect();
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
                            let c = self
                                .run_astar_chart(&chart, &invhom, heuristic, strategy, control)?;
                            state_names = (0..c.num_states())
                                .map(|state| format!("q{state}"))
                                .collect();
                            // A* produces no IndexedCondensedIntersectionStats; we push nothing.
                            c
                        }
                    };
                    chart = next_chart;
                }
                InterpretationKind::TagString => {
                    let value =
                        *input
                            .value
                            .downcast::<TagStringValue<Symbol>>()
                            .map_err(|_| IrtgError::WrongInputType {
                                interpretation: interpretation.name.clone(),
                            })?;
                    let decomp = interpretation.decompose_tag_string(value)?;
                    let (next_chart, next_names, stat) = self.run_generic_chart(
                        &chart,
                        &state_names,
                        decomp,
                        &interpretation.homomorphism,
                        strategy,
                        &interpretation.name,
                        control,
                    )?;
                    if let Some(stat) = stat {
                        stats.push(stat);
                    }
                    chart = next_chart;
                    state_names = next_names;
                }
                InterpretationKind::TagTree => {
                    let value =
                        *input
                            .value
                            .downcast::<Tree>()
                            .map_err(|_| IrtgError::WrongInputType {
                                interpretation: interpretation.name.clone(),
                            })?;
                    let decomp = interpretation.decompose_tag_tree(value)?;
                    let (next_chart, next_names, stat) = self.run_generic_chart(
                        &chart,
                        &state_names,
                        decomp,
                        &interpretation.homomorphism,
                        strategy,
                        &interpretation.name,
                        control,
                    )?;
                    if let Some(stat) = stat {
                        stats.push(stat);
                    }
                    chart = next_chart;
                    state_names = next_names;
                }
                InterpretationKind::BinarizedTagTree => {
                    let value =
                        *input
                            .value
                            .downcast::<Tree>()
                            .map_err(|_| IrtgError::WrongInputType {
                                interpretation: interpretation.name.clone(),
                            })?;
                    let decomp = interpretation.decompose_binarized_tag_tree(value)?;
                    let (next_chart, next_names, stat) = self.run_generic_chart(
                        &chart,
                        &state_names,
                        decomp,
                        &interpretation.homomorphism,
                        strategy,
                        &interpretation.name,
                        control,
                    )?;
                    if let Some(stat) = stat {
                        stats.push(stat);
                    }
                    chart = next_chart;
                    state_names = next_names;
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
            state_names,
            stats,
        })
    }

    /// Return the single best parse tree (Viterbi tree) for the given inputs
    /// and strategy.
    ///
    /// For [`MaterializationStrategy::Astar`] this calls [`crate::astar_one_best`]
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
        self.best_with_scorer_and_stats_impl(inputs, strategy, scorer, None)
    }

    /// Like [`Self::best_with_scorer_and_stats`], reusing grammar-only A*
    /// indexes for the common single-string-interpretation path.
    pub fn best_with_scorer_and_stats_prepared<'a, S: WeightScorer>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
        scorer: &S,
        prepared: &PreparedAstarGrammar,
    ) -> Result<(Option<ViterbiTree>, Option<AstarStats>), IrtgError> {
        self.best_with_scorer_and_stats_impl(inputs, strategy, scorer, Some(prepared))
    }

    fn best_with_scorer_and_stats_impl<'a, S: WeightScorer>(
        &self,
        inputs: impl IntoIterator<Item = ParseInput<'a>>,
        strategy: &MaterializationStrategy<'_>,
        scorer: &S,
        prepared: Option<&PreparedAstarGrammar>,
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
            if !rest.is_empty() {
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
            }

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
                    let decomp = interpretation.decompose_string(value)?;
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    let (tree, stats) = self.run_astar_one_best_with_scorer(
                        &self.grammar,
                        &invhom,
                        heuristic,
                        scorer,
                        prepared,
                    );
                    Ok((tree, Some(stats)))
                }
                InterpretationKind::TagString => {
                    let value = last
                        .value
                        .downcast_ref::<TagStringValue<Symbol>>()
                        .ok_or_else(|| IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        })?
                        .clone();
                    let decomp = interpretation.decompose_tag_string(value)?;
                    let (tree, stats) = self.run_generic_one_best(
                        &self.grammar,
                        decomp,
                        &interpretation.homomorphism,
                        heuristic,
                        scorer,
                        &interpretation.name,
                    )?;
                    Ok((tree, Some(stats)))
                }
                InterpretationKind::TagTree => {
                    let value = *last.value.downcast_ref::<Tree>().ok_or_else(|| {
                        IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        }
                    })?;
                    let decomp = interpretation.decompose_tag_tree(value)?;
                    let (tree, stats) = self.run_generic_one_best(
                        &self.grammar,
                        decomp,
                        &interpretation.homomorphism,
                        heuristic,
                        scorer,
                        &interpretation.name,
                    )?;
                    Ok((tree, Some(stats)))
                }
                InterpretationKind::BinarizedTagTree => {
                    let value = *last.value.downcast_ref::<Tree>().ok_or_else(|| {
                        IrtgError::WrongInputType {
                            interpretation: interpretation.name.clone(),
                        }
                    })?;
                    let decomp = interpretation.decompose_binarized_tag_tree(value)?;
                    let (tree, stats) = self.run_generic_one_best(
                        &self.grammar,
                        decomp,
                        &interpretation.homomorphism,
                        heuristic,
                        scorer,
                        &interpretation.name,
                    )?;
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

    #[allow(clippy::too_many_arguments)]
    fn run_generic_chart<R>(
        &self,
        chart: &Explicit,
        left_state_names: &[String],
        decomp: R,
        homomorphism: &Homomorphism,
        strategy: &MaterializationStrategy<'_>,
        interpretation: &str,
        control: &ParseControl,
    ) -> Result<
        (
            Explicit,
            Vec<String>,
            Option<IndexedCondensedIntersectionStats>,
        ),
        IrtgError,
    >
    where
        R: CondensedTa + StateUniverse + TopDownTa,
        R::State: Clone + Eq + Hash + fmt::Display,
    {
        let invhom = InvHom::new(decomp, homomorphism);
        match strategy {
            MaterializationStrategy::TopDownCondensed => {
                let (chart, right_states, pairs, stats) =
                    materialize_topdown_condensed_intersection_with_pairs_controlled(
                        chart, &invhom, control,
                    )
                    .map_err(|_| IrtgError::Cancelled)?;
                let names = product_state_names(left_state_names, &right_states, &pairs);
                Ok((chart, names, Some(stats)))
            }
            MaterializationStrategy::IndexedCondensed => {
                let (chart, right_states, pairs, stats) =
                    materialize_indexed_condensed_intersection_with_pairs_controlled(
                        chart, &invhom, control,
                    )
                    .map_err(|_| IrtgError::Cancelled)?;
                let names = product_state_names(left_state_names, &right_states, &pairs);
                Ok((chart, names, Some(stats)))
            }
            MaterializationStrategy::Astar { heuristic, options } => {
                let options = AstarOptions {
                    stop_at_first_goal: options.stop_at_first_goal,
                    beam: options.beam,
                };
                let (chart, right_states, pairs) = match heuristic {
                    AstarHeuristic::Zero => {
                        let heuristic = ZeroHeuristic;
                        let (chart, states, pairs, _) =
                            materialize_astar_intersection_with_pairs_controlled(
                                chart,
                                &invhom,
                                &heuristic,
                                options,
                                &crate::ProbabilityScorer,
                                control,
                            );
                        control.check().map_err(|_| IrtgError::Cancelled)?;
                        (chart, states, pairs)
                    }
                    AstarHeuristic::Outside(heuristic) => {
                        let (chart, states, pairs, _) =
                            materialize_astar_intersection_with_pairs_controlled(
                                chart,
                                &invhom,
                                *heuristic,
                                options,
                                &crate::ProbabilityScorer,
                                control,
                            );
                        control.check().map_err(|_| IrtgError::Cancelled)?;
                        (chart, states, pairs)
                    }
                    AstarHeuristic::UniversalSx { .. } | AstarHeuristic::UniversalSxF { .. } => {
                        return Err(IrtgError::IncompatibleHeuristic {
                            interpretation: interpretation.to_owned(),
                            message: "SX and SXF heuristics require a StringAlgebra interpretation"
                                .to_owned(),
                        });
                    }
                };
                let names = product_state_names(left_state_names, &right_states, &pairs);
                Ok((chart, names, None))
            }
        }
    }

    fn run_generic_one_best<R, S>(
        &self,
        chart: &Explicit,
        decomp: R,
        homomorphism: &Homomorphism,
        heuristic: &AstarHeuristic<'_>,
        scorer: &S,
        interpretation: &str,
    ) -> Result<(Option<ViterbiTree>, AstarStats), IrtgError>
    where
        R: CondensedTa + StateUniverse,
        R::State: Clone + Eq + Hash,
        S: WeightScorer,
    {
        let invhom = InvHom::new(decomp, homomorphism);
        match heuristic {
            AstarHeuristic::Zero => {
                let heuristic = ScoredZeroHeuristic::new(scorer);
                Ok(astar_one_best_with_stats(
                    chart, &invhom, &heuristic, scorer,
                ))
            }
            AstarHeuristic::Outside(heuristic) => Ok(astar_one_best_with_stats(
                chart, &invhom, *heuristic, scorer,
            )),
            AstarHeuristic::UniversalSx { .. } | AstarHeuristic::UniversalSxF { .. } => {
                Err(IrtgError::IncompatibleHeuristic {
                    interpretation: interpretation.to_owned(),
                    message: "SX and SXF heuristics require a StringAlgebra interpretation"
                        .to_owned(),
                })
            }
        }
    }

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
        control: &ParseControl,
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
                materialize_astar_string_intersection_with_controlled(
                    chart,
                    invhom,
                    &h,
                    options,
                    &crate::ProbabilityScorer,
                    control,
                )
            }
            AstarHeuristic::Outside(h) => materialize_astar_string_intersection_with_controlled(
                chart,
                invhom,
                *h,
                options,
                &crate::ProbabilityScorer,
                control,
            ),
            AstarHeuristic::UniversalSx { table, n } => {
                let h = table.for_sentence(*n);
                materialize_astar_string_intersection_with_controlled(
                    chart,
                    invhom,
                    &h,
                    options,
                    &crate::ProbabilityScorer,
                    control,
                )
            }
            AstarHeuristic::UniversalSxF { table, oblig, n } => {
                let sx = table.for_sentence(*n);
                let f = oblig.for_sentence(invhom.inner().sentence(), &crate::ProbabilityScorer);
                let h = MinHeuristic::new(sx, f);
                materialize_astar_string_intersection_with_controlled(
                    chart,
                    invhom,
                    &h,
                    options,
                    &crate::ProbabilityScorer,
                    control,
                )
            }
        };
        control.check().map_err(|_| IrtgError::Cancelled)?;
        Ok(new_chart)
    }

    /// Run `astar_one_best` for a single `InvHom<StringDecompositionAutomaton>`.
    fn run_astar_one_best_with_scorer<S: WeightScorer>(
        &self,
        chart: &Explicit,
        invhom: &InvHom<'_, crate::algebras::StringDecompositionAutomaton>,
        heuristic: &AstarHeuristic<'_>,
        scorer: &S,
        prepared: Option<&PreparedAstarGrammar>,
    ) -> (Option<ViterbiTree>, AstarStats) {
        macro_rules! run {
            ($h:expr) => {
                if let Some(prepared) = prepared {
                    astar_string_one_best_with_stats_prepared(chart, prepared, invhom, $h, scorer)
                } else {
                    astar_string_one_best_with_stats(chart, invhom, $h, scorer)
                }
            };
        }
        match heuristic {
            AstarHeuristic::Zero => {
                let h = ScoredZeroHeuristic::new(scorer);
                run!(&h)
            }
            AstarHeuristic::Outside(h) => run!(*h),
            AstarHeuristic::UniversalSx { table, n } => {
                let h = table.for_sentence(*n);
                run!(&h)
            }
            AstarHeuristic::UniversalSxF { table, oblig, n } => {
                let sx = table.for_sentence(*n);
                let f = oblig.for_sentence(invhom.inner().sentence(), scorer);
                let h = MinHeuristic::new(sx, f);
                run!(&h)
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
                    let decomp = interpretation.decompose_string(value)?;
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    if is_last {
                        let (tree, stats) = self.run_astar_one_best_with_scorer(
                            &chart, &invhom, heuristic, scorer, None,
                        );
                        return Ok((tree, Some(stats)));
                    } else {
                        let (next, _, _) =
                            materialize_topdown_condensed_intersection(&chart, &invhom);
                        chart = next;
                    }
                }
                InterpretationKind::TagString => {
                    let value =
                        *input
                            .value
                            .downcast::<TagStringValue<Symbol>>()
                            .map_err(|_| IrtgError::WrongInputType {
                                interpretation: interpretation.name.clone(),
                            })?;
                    let decomp = interpretation.decompose_tag_string(value)?;
                    if is_last {
                        let (tree, stats) = self.run_generic_one_best(
                            &chart,
                            decomp,
                            &interpretation.homomorphism,
                            heuristic,
                            scorer,
                            &interpretation.name,
                        )?;
                        return Ok((tree, Some(stats)));
                    }
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    chart = materialize_topdown_condensed_intersection(&chart, &invhom).0;
                }
                InterpretationKind::TagTree => {
                    let value =
                        *input
                            .value
                            .downcast::<Tree>()
                            .map_err(|_| IrtgError::WrongInputType {
                                interpretation: interpretation.name.clone(),
                            })?;
                    let decomp = interpretation.decompose_tag_tree(value)?;
                    if is_last {
                        let (tree, stats) = self.run_generic_one_best(
                            &chart,
                            decomp,
                            &interpretation.homomorphism,
                            heuristic,
                            scorer,
                            &interpretation.name,
                        )?;
                        return Ok((tree, Some(stats)));
                    }
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    chart = materialize_topdown_condensed_intersection(&chart, &invhom).0;
                }
                InterpretationKind::BinarizedTagTree => {
                    let value =
                        *input
                            .value
                            .downcast::<Tree>()
                            .map_err(|_| IrtgError::WrongInputType {
                                interpretation: interpretation.name.clone(),
                            })?;
                    let decomp = interpretation.decompose_binarized_tag_tree(value)?;
                    if is_last {
                        let (tree, stats) = self.run_generic_one_best(
                            &chart,
                            decomp,
                            &interpretation.homomorphism,
                            heuristic,
                            scorer,
                            &interpretation.name,
                        )?;
                        return Ok((tree, Some(stats)));
                    }
                    let invhom = InvHom::new(decomp, &interpretation.homomorphism);
                    chart = materialize_topdown_condensed_intersection(&chart, &invhom).0;
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
trait DerivationRenderer: fmt::Debug + Send + Sync {
    fn render(
        &self,
        algebra: &dyn Any,
        homomorphism: &Homomorphism,
        arena: &TreeArena<Symbol>,
        root: Tree,
        name: &str,
    ) -> Result<String, IrtgError>;

    fn evaluate(
        &self,
        algebra: &dyn Any,
        homomorphism: &Homomorphism,
        arena: &TreeArena<Symbol>,
        root: Tree,
        name: &str,
    ) -> Result<EvaluatedAlgebraValue, IrtgError>;
}

/// [`DerivationRenderer`] for a concrete algebra `A` paired with codec `C`.
struct TypedDerivationCodec<A, C> {
    codec: C,
    output_codecs: Arc<OutputCodecRegistry>,
    _algebra: PhantomData<fn() -> A>,
}

impl<A, C> TypedDerivationCodec<A, C> {
    fn new(codec: C) -> Self {
        Self {
            codec,
            output_codecs: Arc::new(OutputCodecRegistry::standard()),
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
    A: Send,
    A::Value: Send + Sync + 'static,
    C: OutputCodec<A::Value, Output = String> + fmt::Debug + Send + Sync,
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

    fn evaluate(
        &self,
        algebra: &dyn Any,
        homomorphism: &Homomorphism,
        arena: &TreeArena<Symbol>,
        root: Tree,
        name: &str,
    ) -> Result<EvaluatedAlgebraValue, IrtgError> {
        let algebra = algebra
            .downcast_ref::<A>()
            .ok_or_else(|| IrtgError::WrongInputType {
                interpretation: name.to_owned(),
            })?;
        let mut image = TreeArena::new();
        let image_root = homomorphism.apply(arena, root, &mut image)?;
        let value =
            algebra
                .evaluate_term(&image, image_root)
                .ok_or_else(|| IrtgError::ObjectParse {
                    interpretation: name.to_owned(),
                    message: "derivation tree did not evaluate in the algebra".to_owned(),
                })?;
        let visual = algebra.visualize(&value);
        Ok(EvaluatedAlgebraValue {
            inner: Box::new(TypedEvaluatedAlgebraValue {
                value,
                visual,
                output_codecs: self.output_codecs.clone(),
            }),
        })
    }
}

trait ErasedEvaluatedAlgebraValue: fmt::Debug + Send + Sync {
    fn visual(&self) -> &VisualRepresentation;
    fn codecs(&self) -> Vec<CodecMetadata>;
    fn encode(&self, codec_name: &str) -> Result<String, OutputCodecError>;
}

struct TypedEvaluatedAlgebraValue<V> {
    value: V,
    visual: VisualRepresentation,
    output_codecs: Arc<OutputCodecRegistry>,
}

impl<V> fmt::Debug for TypedEvaluatedAlgebraValue<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TypedEvaluatedAlgebraValue")
            .field("visual", &self.visual)
            .finish_non_exhaustive()
    }
}

impl<V: Send + Sync + 'static> ErasedEvaluatedAlgebraValue for TypedEvaluatedAlgebraValue<V> {
    fn visual(&self) -> &VisualRepresentation {
        &self.visual
    }

    fn codecs(&self) -> Vec<CodecMetadata> {
        self.output_codecs
            .codecs_for::<V>()
            .iter()
            .map(|codec| *codec.metadata())
            .collect()
    }

    fn encode(&self, codec_name: &str) -> Result<String, OutputCodecError> {
        Ok(self
            .output_codecs
            .codec_for_name::<V>(codec_name)?
            .encode(&self.value))
    }
}

/// An evaluated algebra value whose concrete Rust type remains available to codec dispatch.
#[derive(Debug)]
pub struct EvaluatedAlgebraValue {
    inner: Box<dyn ErasedEvaluatedAlgebraValue>,
}

impl EvaluatedAlgebraValue {
    /// Return the algebra's preferred GUI-neutral visualization.
    pub fn visual(&self) -> &VisualRepresentation {
        self.inner.visual()
    }

    /// List textual codecs registered for this value's exact public type.
    pub fn codecs(&self) -> Vec<CodecMetadata> {
        self.inner.codecs()
    }

    /// Encode the value with a registered textual codec.
    pub fn encode(&self, codec_name: &str) -> Result<String, OutputCodecError> {
        self.inner.encode(codec_name)
    }
}

/// A named interpretation of an IRTG.
#[derive(Debug)]
pub struct Interpretation {
    name: String,
    class_name: String,
    kind: InterpretationKind,
    algebra: Mutex<Box<dyn Any + Send>>,
    algebra_signature: Signature,
    homomorphism: Homomorphism,
    renderer: Box<dyn DerivationRenderer>,
}

impl Interpretation {
    fn decompose_string(
        &self,
        value: Vec<Symbol>,
    ) -> Result<crate::StringDecompositionAutomaton, IrtgError> {
        let algebra = self.algebra.lock().unwrap();
        let algebra = algebra
            .as_ref()
            .downcast_ref::<StringAlgebra>()
            .ok_or_else(|| IrtgError::WrongInputType {
                interpretation: self.name.clone(),
            })?;
        Ok(algebra.decompose(value))
    }

    fn decompose_tag_string(
        &self,
        value: TagStringValue<Symbol>,
    ) -> Result<TagStringDecompositionAutomaton, IrtgError> {
        let algebra = self.algebra.lock().unwrap();
        let algebra = algebra
            .as_ref()
            .downcast_ref::<TagStringAlgebra>()
            .ok_or_else(|| IrtgError::WrongInputType {
                interpretation: self.name.clone(),
            })?;
        algebra
            .decompose(value)
            .ok_or_else(|| IrtgError::ObjectParse {
                interpretation: self.name.clone(),
                message: "TAG decomposition inputs must be contiguous strings".to_owned(),
            })
    }

    fn decompose_tag_tree(&self, value: Tree) -> Result<TagTreeDecompositionAutomaton, IrtgError> {
        let algebra = self.algebra.lock().unwrap();
        let algebra = algebra
            .as_ref()
            .downcast_ref::<TagTreeAlgebra>()
            .ok_or_else(|| IrtgError::WrongInputType {
                interpretation: self.name.clone(),
            })?;
        Ok(algebra.decompose(value))
    }

    fn decompose_binarized_tag_tree(
        &self,
        value: Tree,
    ) -> Result<BinarizedTagTreeDecompositionAutomaton, IrtgError> {
        let algebra = self.algebra.lock().unwrap();
        let algebra = algebra
            .as_ref()
            .downcast_ref::<Binarizing<TagTreeAlgebra>>()
            .ok_or_else(|| IrtgError::WrongInputType {
                interpretation: self.name.clone(),
            })?;
        let append = algebra
            .append_symbol()
            .ok_or_else(|| IrtgError::ObjectParse {
                interpretation: self.name.clone(),
                message: "binarizing TAG tree algebra has no append symbol".to_owned(),
            })?;
        Ok(BinarizedTagTreeDecompositionAutomaton::new(
            algebra.inner().decompose_binarized(value),
            append,
        ))
    }

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
        !matches!(self.kind, InterpretationKind::OutputOnly)
    }

    /// Return whether this interpretation can constrain parsing to defined values.
    pub fn supports_non_null_filter(&self) -> bool {
        self.algebra
            .lock()
            .unwrap()
            .as_ref()
            .is::<FeatureStructureAlgebra>()
    }

    /// Return whether interpreted values use the tree textual representation.
    pub fn is_tree_valued(&self) -> bool {
        matches!(
            self.kind,
            InterpretationKind::TagTree | InterpretationKind::BinarizedTagTree
        ) || (self.kind == InterpretationKind::OutputOnly
            && self.class_name != FEATURE_STRUCTURE_ALGEBRA)
    }

    /// Parse a textual object with this interpretation's algebra, returning a type-erased
    /// value suitable for [`input_erased`](Self::input_erased).
    pub fn parse_object_erased(&self, input: &str) -> Result<Box<dyn Any + Send>, IrtgError> {
        match self.kind {
            InterpretationKind::String => {
                let mut algebra = self.algebra.lock().unwrap();
                let algebra = algebra
                    .as_mut()
                    .downcast_mut::<StringAlgebra>()
                    .ok_or_else(|| IrtgError::WrongInputType {
                        interpretation: self.name.clone(),
                    })?;
                let value = algebra
                    .parse_object(input)
                    .map_err(|err| IrtgError::ObjectParse {
                        interpretation: self.name.clone(),
                        message: err.to_string(),
                    })?;
                Ok(Box::new(value))
            }
            InterpretationKind::TagString => {
                let mut algebra = self.algebra.lock().unwrap();
                let algebra = algebra
                    .as_mut()
                    .downcast_mut::<TagStringAlgebra>()
                    .ok_or_else(|| IrtgError::WrongInputType {
                        interpretation: self.name.clone(),
                    })?;
                let value = algebra
                    .parse_object(input)
                    .map_err(|err| IrtgError::ObjectParse {
                        interpretation: self.name.clone(),
                        message: err.to_string(),
                    })?;
                Ok(Box::new(value))
            }
            InterpretationKind::TagTree => {
                let mut algebra = self.algebra.lock().unwrap();
                let algebra = algebra
                    .as_mut()
                    .downcast_mut::<TagTreeAlgebra>()
                    .ok_or_else(|| IrtgError::WrongInputType {
                        interpretation: self.name.clone(),
                    })?;
                let value = algebra
                    .parse_object(input)
                    .map_err(|err| IrtgError::ObjectParse {
                        interpretation: self.name.clone(),
                        message: err.to_string(),
                    })?;
                Ok(Box::new(value))
            }
            InterpretationKind::BinarizedTagTree => {
                let mut algebra = self.algebra.lock().unwrap();
                let algebra = algebra
                    .as_mut()
                    .downcast_mut::<Binarizing<TagTreeAlgebra>>()
                    .ok_or_else(|| IrtgError::WrongInputType {
                        interpretation: self.name.clone(),
                    })?;
                let value = algebra
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
    pub fn input_erased(&self, value: Box<dyn Any + Send>) -> ParseInput<'_> {
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
        let algebra = self.algebra.lock().unwrap();
        self.renderer
            .render(&**algebra, &self.homomorphism, arena, root, &self.name)
    }

    /// Evaluate a derivation while retaining its typed value for visualization and codecs.
    pub fn evaluate_derivation(
        &self,
        arena: &TreeArena<Symbol>,
        root: Tree,
    ) -> Result<EvaluatedAlgebraValue, IrtgError> {
        let algebra = self.algebra.lock().unwrap();
        self.renderer
            .evaluate(&**algebra, &self.homomorphism, arena, root, &self.name)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InterpretationKind {
    /// A [`StringAlgebra`] interpretation: can be a parse input (decomposable).
    String,
    /// A decomposable TAG string interpretation.
    TagString,
    /// A decomposable TAG derived-tree interpretation.
    TagTree,
    /// A decomposable binarized TAG derived-tree interpretation.
    BinarizedTagTree,
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
    A::InternalValue: Send + 'static,
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
        let mut algebra = self.interpretation.algebra.lock().unwrap();
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
        let algebra = self.interpretation.algebra.lock().unwrap();
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
    value: Box<dyn Any + Send>,
}

/// The parse chart returned by [`Irtg::parse`].
#[derive(Debug)]
pub struct ParseChart {
    /// Explicit grammar chart after all input constraints were applied.
    pub automaton: Explicit,
    /// Human-readable state labels in dense state-ID order.
    pub state_names: Vec<String>,
    /// Per-intersection materialization statistics.
    pub stats: Vec<IndexedCondensedIntersectionStats>,
}

/// Errors returned by IRTG parsing, construction, and parsing.
#[derive(Debug, Error)]
pub enum IrtgError {
    /// The caller requested cooperative cancellation.
    ///
    /// No partial parse chart or filtered chart is returned. Because
    /// cancellation is cooperative, the operation may finish its current
    /// indivisible automaton or algebra callback before returning this error.
    #[error("parsing cancelled")]
    Cancelled,
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
    /// An interpretation's algebra does not provide an all-defined-values filter.
    #[error(
        "interpretation {interpretation:?} with algebra {class_name} does not support non-null filtering"
    )]
    NonNullFilterUnsupported {
        /// Interpretation name.
        interpretation: String,
        /// Alto algebra class name.
        class_name: String,
    },
    /// A parse strategy selected a heuristic that is not defined for this algebra.
    #[error("heuristic is incompatible with interpretation {interpretation:?}: {message}")]
    IncompatibleHeuristic {
        /// Interpretation name.
        interpretation: String,
        /// Human-readable incompatibility.
        message: String,
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

pub(crate) fn build_irtg(ast: AstIrtg) -> Result<Irtg, IrtgError> {
    let mut builder = ExplicitBuilder::new();
    let mut states = Interner::new();
    let mut state_ids = FxHashMap::default();
    let mut grammar_signature = Signature::new();
    let mut homs = FxHashMap::default();
    let mut algebra_signatures = FxHashMap::default();
    let interpretation_algebras = ast
        .interpretations
        .iter()
        .map(|decl| (decl.name.clone(), decl.algebra.clone()))
        .collect::<FxHashMap<_, _>>();

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
            let normalized;
            let term = if interpretation_algebras
                .get(&hom_rule.interpretation)
                .map(String::as_str)
                == Some(FEATURE_STRUCTURE_ALGEBRA)
            {
                normalized = normalize_legacy_feature_term(&hom_rule.term);
                &normalized
            } else {
                &hom_rule.term
            };
            let term = lower_hom_term(term, hom, signature)?;
            hom.add(symbol, rule.auto.children.len(), term)?;
        }
    }

    let mut interpretations = FxHashMap::default();
    for decl in ast.interpretations {
        let (kind, algebra, algebra_signature, renderer): (
            InterpretationKind,
            Box<dyn Any + Send>,
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
        } else if decl.algebra == TAG_STRING_ALGEBRA {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let algebra = TagStringAlgebra::with_signature(signature.clone());
            let renderer = Box::new(TypedDerivationCodec::<TagStringAlgebra, DisplayCodec>::new(
                DisplayCodec,
            ));
            (
                InterpretationKind::TagString,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else if decl.algebra == TAG_TREE_ALGEBRA || decl.algebra == TAG_TREE_WITH_ARITIES_ALGEBRA
        {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let algebra = if decl.algebra == TAG_TREE_WITH_ARITIES_ALGEBRA {
                TagTreeAlgebra::with_arities(signature.clone())
            } else {
                TagTreeAlgebra::tree(signature.clone())
            };
            let renderer = Box::new(TypedDerivationCodec::<TagTreeAlgebra, DisplayCodec>::new(
                DisplayCodec,
            ));
            (
                InterpretationKind::TagTree,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else if decl.algebra == BINARIZING_TAG_TREE_ALGEBRA
            || decl.algebra == BINARIZING_TAG_TREE_WITH_ARITIES_ALGEBRA
        {
            let mut signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let append = Some(signature.intern(APPEND_SYMBOL.to_owned(), 2)?);
            let inner = if decl.algebra == BINARIZING_TAG_TREE_WITH_ARITIES_ALGEBRA {
                TagTreeAlgebra::with_arities(signature.clone())
            } else {
                TagTreeAlgebra::tree(signature.clone())
            };
            let algebra = Binarizing::new(inner, append);
            let renderer = Box::new(TypedDerivationCodec::<
                Binarizing<TagTreeAlgebra>,
                DisplayCodec,
            >::new(DisplayCodec));
            (
                InterpretationKind::BinarizedTagTree,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else if decl.algebra == FEATURE_STRUCTURE_ALGEBRA {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let algebra = FeatureStructureAlgebra::with_signature(signature.clone());
            let renderer = Box::new(
                TypedDerivationCodec::<FeatureStructureAlgebra, DisplayCodec>::new(DisplayCodec),
            );
            (
                InterpretationKind::OutputOnly,
                Box::new(algebra),
                signature,
                renderer,
            )
        } else if decl.algebra == TREE_WITH_ARITIES_ALGEBRA {
            let signature = algebra_signatures.remove(&decl.name).unwrap_or_default();
            let algebra = TreeAlgebra::with_arities(signature.clone());
            let renderer = Box::new(TypedDerivationCodec::<TreeAlgebra, DisplayCodec>::new(
                DisplayCodec,
            ));
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
            let renderer = Box::new(
                TypedDerivationCodec::<Binarizing<TreeAlgebra>, DisplayCodec>::new(DisplayCodec),
            );
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
                algebra: Mutex::new(algebra),
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

fn normalize_legacy_feature_term(term: &AstHomTerm) -> AstHomTerm {
    match term {
        AstHomTerm::Variable(variable) => AstHomTerm::Variable(*variable),
        AstHomTerm::Symbol(label, children) => {
            let children = children.iter().map(normalize_legacy_feature_term).collect();
            if let Some(specification) = label.strip_prefix("emba_") {
                let mut attributes = specification.split('_');
                if let (Some(top), Some(bottom)) = (attributes.next(), attributes.next()) {
                    return AstHomTerm::Symbol(format!("remap_root={top},foot={bottom}"), children);
                }
            }
            AstHomTerm::Symbol(label.clone(), children)
        }
    }
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

    fn tiny_tag_irtg() -> &'static [u8] {
        br#"
        interpretation string: de.up.ling.irtg.algebra.TagStringAlgebra
        interpretation tree: de.up.ling.irtg.algebra.TagTreeAlgebra

        S! -> r
          [string] *WRAP21*(*CONC12*(a, *EE*), b)
          [tree] @(*, f(a))
        "#
    }

    #[test]
    fn tag_string_and_tree_are_both_parse_inputs() {
        let irtg = parse_irtg(tiny_tag_irtg()).unwrap();
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();
        let tree = irtg.interpretation::<TagTreeAlgebra>("tree").unwrap();
        let string_value = string.parse_object("a b").unwrap();
        let tree_value = tree.parse_object("f(a)").unwrap();

        let chart = irtg
            .parse([string.input(string_value), tree.input(tree_value)])
            .unwrap();
        assert!(chart.automaton.viterbi().is_some());
    }

    #[test]
    fn tag_inputs_support_generic_zero_astar() {
        let irtg = parse_irtg(tiny_tag_irtg()).unwrap();
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();
        let value = string.parse_object("a b").unwrap();
        let result = irtg
            .best_with(
                [string.input(value)],
                &MaterializationStrategy::Astar {
                    heuristic: AstarHeuristic::Zero,
                    options: AstarOptions {
                        stop_at_first_goal: true,
                        beam: None,
                    },
                },
            )
            .unwrap();
        assert!(result.is_some());
    }

    #[test]
    fn binarized_tag_tree_is_inputable() {
        let irtg = parse_irtg(
            br#"
            interpretation tree: de.up.ling.irtg.algebra.BinarizingTagTreeAlgebra

            S! -> r
              [tree] f(_@_(a, _@_(b, c)))
            "# as &[u8],
        )
        .unwrap();
        let tree = irtg
            .interpretation::<Binarizing<TagTreeAlgebra>>("tree")
            .unwrap();
        let value = tree.parse_object("f(a, b, c)").unwrap();
        let chart = irtg.parse([tree.input(value)]).unwrap();
        assert!(chart.automaton.viterbi().is_some());
    }

    #[test]
    fn legacy_alto_aux_embedding_is_normalized_outside_the_algebra() {
        let irtg = parse_irtg(
            br#"
            interpretation ft: de.up.ling.irtg.algebra.FeatureStructureAlgebra

            S! -> combine(A)
              [ft] emba_top_bottom(?1)

            A -> value
              [ft] "[root: #x [], foot: #x]"
            "# as &[u8],
        )
        .unwrap();
        let ft = irtg
            .interpretation::<FeatureStructureAlgebra>("ft")
            .unwrap();
        assert!(ft.algebra_signature().get("emba_top_bottom").is_none());
        assert!(
            ft.algebra_signature()
                .get("remap_root=top,foot=bottom")
                .is_some()
        );
    }
}
