//! A small, fast library for bottom-up tree automata.
//!
//! A tree automaton reads a tree from the leaves upward. Each leaf receives a
//! state, then each parent receives a state based on its symbol and the states
//! assigned to its children. If the root reaches an accepting state, the tree
//! is accepted.
//!
//! The main trait is [`BottomUpTa`]. It treats an automaton as an oracle: given
//! a symbol and child states, it reports the possible parent states. This works
//! for both explicit automata, whose rules are stored in tables, and implicit
//! automata, whose rules are computed on demand.
//!
//! Use [`ExplicitBuilder`] when all rules are known ahead of time. Use
//! [`Memo`] when an implicit automaton has its own state type, such as strings,
//! tuples, or syntax objects, but a runner needs dense [`StateId`] values. Use
//! [`materialize()`] when a finite implicit automaton should be explored and
//! frozen into an [`Explicit`] automaton.
//!
//! Deterministic runners use [`StateId::STUCK`] as a sentinel for rejected
//! subtrees. A node assigned `STUCK` did not match any transition rule, or one
//! of its children was already stuck.
//!
//! # Grammars, algebras, and codecs
//!
//! [`Irtg`] combines a weighted grammar automaton with named homomorphisms and
//! algebras. Built-in algebras cover strings, trees, TAG strings, TAG derived
//! trees, and feature structures.
//!
//! [`InputCodecRegistry`] discovers file readers by their exact result type:
//! both `.irtg` and Tulipac `.tag` codecs produce [`Irtg`], while `.auto`
//! produces [`ExplicitWithSignature`]. [`OutputCodecRegistry`] discovers
//! textual encodings by an algebra's public value type. An algebra's preferred
//! GUI-neutral display is available through [`Algebra::visualize`].
//!
//! Codec metadata lookup is lazy: listing available formats does not read,
//! evaluate, or encode anything.
//!
//! ```
//! use rusty_alto::*;
//! use packed_term_arena::tree::TreeArena;
//!
//! let a = Symbol(0);
//! let f = Symbol(1);
//! let mut builder = ExplicitBuilder::new();
//! let leaf = builder.new_state();
//! let root = builder.new_state();
//! builder.add_rule(a, vec![], leaf);
//! builder.add_rule(f, vec![leaf, leaf], root);
//! builder.add_accepting(root);
//! let automaton = builder.build();
//!
//! let mut tree = TreeArena::new();
//! let left = tree.add_node(a, vec![]);
//! let right = tree.add_node(a, vec![]);
//! let root_node = tree.add_node(f, vec![left, right]);
//! let run = run_det(&automaton, &tree, root_node);
//! assert!(automaton.is_accepting(&run.root_state));
//! ```

pub mod algebras;
pub mod alto;
pub mod alto_ast;
pub mod application;
pub mod astar;
lalrpop_util::lalrpop_mod!(
    #[allow(clippy::all)]
    alto_grammar
);
pub mod codec;
pub mod codecs;
pub mod combinators;
pub mod corpus;
pub mod explicit;
pub mod heuristic;
pub mod homomorphism;
pub mod ids;
pub mod interner;
pub mod irtg;
pub mod materialize;
pub mod memo;
pub mod obligatory_leaf;
pub mod parseval;
pub mod run;
pub mod score;
pub mod set_trie;
pub mod signature;
pub mod sorted_language;
pub mod traits;
pub mod viterbi;

pub use algebras::{
    APPEND_SYMBOL, Algebra, BinarizedTagTreeDecompositionAutomaton, BinarizedTagTreeState,
    Binarizing, CONC11, CONC12, CONC21, EvaluatingDecompositionAutomaton, FS_EMBED_PREFIX,
    FS_PROJECT_PREFIX, FS_REMAP_PREFIX, FS_UNIFY, FeatureStructure, FeatureStructureAlgebra,
    FeatureStructureAttribute, FeatureStructureFilter, FeatureStructureNode,
    FeatureStructureNodeId, FeatureStructureParseError, SentenceSxHeuristic, Span,
    StringAlgebra, StringDecompositionAutomaton, TAG_E, TAG_EE, TAG_HOLE, TAG_SUBSTITUTE,
    TagSpan, TagStringAlgebra, TagStringDecompositionAutomaton, TagStringValue, TagTreeAlgebra,
    TagTreeContext, TagTreeDecompositionAutomaton, TreeAlgebra, TreeValue,
    UniversalSxHeuristic, WRAP21, WRAP22,
};
#[allow(deprecated)]
pub use alto::{
    AltoParseError, ExplicitWithSignature, ParsedTreeAutomaton, parse_alto,
    parse_alto_with_signature,
};
pub use application::{
    AutomatonSummary, EvaluatedInterpretation, InterpretationInfo, LanguageCardinality,
    ParseStrategy, RenderedInterpretation, RenderedValue, ResolvedRule,
};
pub use astar::{
    AstarOptions, AstarStats, PreparedAstarGrammar, astar_one_best, astar_one_best_with,
    astar_one_best_with_stats, astar_string_one_best_lazy_benchmark_with_stats_prepared,
    astar_string_one_best_with_stats_prepared, materialize_astar_intersection,
    materialize_astar_intersection_with, materialize_astar_string_intersection_with_prepared,
    materialize_astar_viterbi_forest, materialize_astar_viterbi_forest_with,
};
pub use codec::{
    AltoTreeAutomatonInputCodec, CodecMetadata, DisplayCodec, FeatureStructureVisualizationCodec,
    InputCodec, InputCodecError, InputCodecRegistry, InputCodecRegistryError, IrtgInputCodec,
    OutputCodec, OutputCodecError, OutputCodecRegistry, RegisteredInputCodec, SpaceJoinCodec,
    TextOutputCodec, TextVisualizationCodec, TreeVisualizationCodec, VisualRepresentation,
};
pub use codecs::{TulipacError, TulipacInputCodec};
pub use combinators::{Determinized, InvHom, Mapped, Product};
pub use corpus::{Corpus, CorpusError, CorpusWriter, Instance, read_corpus};
pub use explicit::{Explicit, ExplicitBuildError, ExplicitBuilder, Rule};
pub use heuristic::{
    IntersectionHeuristic, MinHeuristic, OutsideHeuristic, ScoredZeroHeuristic, ZeroHeuristic,
};
pub use homomorphism::{HomLabel, HomTerm, Homomorphism, HomomorphismError};
pub use ids::{Arity, StateId, Symbol};
pub use interner::Interner;
pub use irtg::{
    AstarHeuristic, EvaluatedAlgebraValue, Interpretation, Irtg, IrtgError,
    MaterializationStrategy, NonNullFilteredChart, ParseChart, ParseInput, TypedInterpretation,
    parse_irtg,
};
pub use materialize::{
    IndexedCondensedIntersectionStats, materialize, materialize_indexed_condensed_intersection,
    materialize_indexed_condensed_intersection_with_pairs,
    materialize_topdown_condensed_intersection,
    materialize_topdown_condensed_intersection_with_pairs,
};
pub use memo::{Memo, MemoStats};
pub use obligatory_leaf::{ObligatoryLeafHeuristic, ObligatoryLeafTables};
pub use parseval::{
    EvalbParamError, EvalbParams, ParsevalCounts, ParsevalSkip, compare_trees, count_gold,
};
pub use run::{DetRun, NonDetRun, StateSet, run_det, run_nondet};
pub use score::{LogProbabilityScorer, ProbabilityScorer, WeightScorer};
pub use set_trie::{KeySet, SetTrie};
pub use signature::{Signature, SignatureError};
pub use sorted_language::{SortedLanguageIterator, WeightedTree};
pub use traits::{
    BottomUpTa, CondensedTa, CondensedTopDownTa, DetBottomUpTa, IndexedBottomUpTa, StateUniverse,
    SymbolSet, TopDownTa,
};
pub use viterbi::ViterbiTree;

pub(crate) type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;
pub(crate) type FxHashSet<T> = hashbrown::HashSet<T, rustc_hash::FxBuildHasher>;
