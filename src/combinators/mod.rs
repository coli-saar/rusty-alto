//! Automaton combinators.
//!
//! Combinators build new automata from existing ones without eagerly copying
//! all rules. In Phase 1 these are simple, correctness-oriented versions. They
//! are useful as building blocks and as a reference point for faster indexed
//! versions later.

mod determinized;
mod mapped;
mod product;

pub use determinized::Determinized;
pub use mapped::Mapped;
pub use product::Product;
