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
//! let mut tree = TestArena::new();
//! let left = tree.add_node(a, vec![]);
//! let right = tree.add_node(a, vec![]);
//! let root_node = tree.add_node(f, vec![left, right]);
//! let run = run_det(&automaton, &tree, root_node);
//! assert!(automaton.is_accepting(&run.root_state));
//! ```

pub mod alto;
pub mod arena;
pub mod combinators;
pub mod explicit;
pub mod ids;
pub mod interner;
pub mod materialize;
pub mod memo;
pub mod run;
pub mod traits;

pub use alto::{AltoAutomaton, AltoParseError, AltoRule, AltoSignature, parse_alto};
pub use arena::{Arena, NodeId, TestArena, TestNode};
pub use combinators::{Determinized, Product};
pub use explicit::{Explicit, ExplicitBuilder, Rule};
pub use ids::{Arity, StateId, Symbol};
pub use interner::Interner;
pub use materialize::materialize;
pub use memo::{Memo, MemoStats};
pub use run::{DetRun, NonDetRun, StateSet, run_det, run_nondet};
pub use traits::{BottomUpTa, DetBottomUpTa};

pub(crate) type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;
pub(crate) type FxHashSet<T> = hashbrown::HashSet<T, rustc_hash::FxBuildHasher>;
