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
//! ```
//! use rusty_alto::*;
//! use rusty_tree::tree::TreeArena;
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
pub mod astar;
lalrpop_util::lalrpop_mod!(
    #[allow(clippy::all)]
    alto_grammar
);
pub mod combinators;
pub mod explicit;
pub mod heuristic;
pub mod homomorphism;
pub mod ids;
pub mod interner;
pub mod irtg;
pub mod materialize;
pub mod memo;
pub mod run;
pub mod score;
pub mod set_trie;
pub mod signature;
pub mod sorted_language;
pub mod traits;
pub mod viterbi;

pub use algebras::{
    Algebra, EvaluatingDecompositionAutomaton, SentenceSxHeuristic, Span, StringAlgebra,
    StringDecompositionAutomaton, UniversalSxHeuristic,
};
pub use alto::{AltoParseError, ParsedTreeAutomaton, parse_alto, parse_alto_with_signature};
pub use astar::{
    AstarOptions, AstarStats, PreparedAstarGrammar, astar_one_best, astar_one_best_with,
    astar_one_best_with_stats, astar_string_one_best_with_stats_prepared,
    materialize_astar_intersection, materialize_astar_intersection_with,
    materialize_astar_string_intersection_with_prepared,
};
pub use combinators::{Determinized, InvHom, Mapped, Product};
pub use explicit::{Explicit, ExplicitBuildError, ExplicitBuilder, Rule};
pub use heuristic::{IntersectionHeuristic, OutsideHeuristic, ScoredZeroHeuristic, ZeroHeuristic};
pub use homomorphism::{HomLabel, HomTerm, Homomorphism, HomomorphismError};
pub use ids::{Arity, StateId, Symbol};
pub use interner::Interner;
pub use irtg::{
    AstarHeuristic, Interpretation, Irtg, IrtgError, MaterializationStrategy, ParseChart,
    ParseInput, TypedInterpretation, parse_irtg,
};
pub use materialize::{
    IndexedCondensedIntersectionStats, materialize, materialize_indexed_condensed_intersection,
    materialize_topdown_condensed_intersection,
};
pub use memo::{Memo, MemoStats};
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
