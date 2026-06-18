//! Tree algebras, ported from Alto's `TreeAlgebra` / `TreeWithAritiesAlgebra`, plus a generic
//! [`Binarizing`] adapter (Alto's `BinarizingAlgebra<E>`).
//!
//! Java uses inheritance; Rust replaces it with composition:
//! - [`TreeAlgebra`] is the low-level algebra that builds a tree, optionally stripping arity
//!   suffixes (`f_2` -> `f`).
//! - [`Binarizing`] is an **adapter around any algebra** that collapses a binary append symbol
//!   (`_@_`) before delegating evaluation to the wrapped algebra. It is not tree-specific.
//!
//! The **internal value** is a [`Tree`] handle into a scratch [`TreeArena`] the algebra owns, so
//! per-node [`evaluate`](Algebra::evaluate) just appends a node (O(arity), no copying). The
//! **public value** ([`TreeValue`]) is produced once by [`to_external`](Algebra::to_external),
//! which copies the finished tree out into its own arena and resets the scratch.
//!
//! These algebras are **output-only**: they evaluate a derivation tree into a value, but do not
//! provide decomposition, so an interpretation backed by them cannot be a parse input.

use crate::{Algebra, Signature, Symbol};
use rusty_tree::parser::{TreeParseError, parse_tree};
use rusty_tree::tree::{Tree, TreeArena};
use std::cell::RefCell;
use std::fmt;

/// The default binary append (concatenation) symbol of a binarizing algebra.
pub const APPEND_SYMBOL: &str = "_@_";

/// A standalone public tree value, owning a [`TreeArena`] with `String` labels.
#[derive(Debug)]
pub struct TreeValue {
    arena: TreeArena<String>,
    root: Tree,
}

impl TreeValue {
    /// Wrap an arena and its root.
    pub fn new(arena: TreeArena<String>, root: Tree) -> Self {
        Self { arena, root }
    }
}

/// Copy the subtree rooted at `node` in `src` into `dst`, returning its new root.
fn copy_subtree(src: &TreeArena<String>, node: Tree, dst: &mut TreeArena<String>) -> Tree {
    let children: Vec<Tree> = src
        .get_children(node)
        .iter()
        .map(|&child| copy_subtree(src, child, dst))
        .collect();
    dst.add_node(src.get_label(node).clone(), children)
}

impl fmt::Display for TreeValue {
    /// Render as a term `label(c1, c2, ...)`, quoting labels that are not bare identifiers so the
    /// output round-trips through [`parse_tree`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_subtree(f, &self.arena, self.root)
    }
}

fn write_subtree(f: &mut fmt::Formatter<'_>, arena: &TreeArena<String>, node: Tree) -> fmt::Result {
    write_label(f, arena.get_label(node))?;
    let children = arena.get_children(node);
    if !children.is_empty() {
        write!(f, "(")?;
        for (i, &child) in children.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write_subtree(f, arena, child)?;
        }
        write!(f, ")")?;
    }
    Ok(())
}

fn is_bare(label: &str) -> bool {
    !label.is_empty()
        && label
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

fn write_label(f: &mut fmt::Formatter<'_>, label: &str) -> fmt::Result {
    if is_bare(label) {
        return f.write_str(label);
    }
    f.write_str("'")?;
    for c in label.chars() {
        match c {
            '\\' => f.write_str("\\\\")?,
            '\'' => f.write_str("\\'")?,
            '\n' => f.write_str("\\n")?,
            '\r' => f.write_str("\\r")?,
            '\t' => f.write_str("\\t")?,
            _ => write!(f, "{c}")?,
        }
    }
    f.write_str("'")
}

/// Strip a trailing `_<digits>` arity suffix from a label (`S_2` -> `S`, `woman_0` -> `woman`),
/// leaving labels without such a suffix unchanged. Mirrors Alto's `stripArities` (permissive).
fn strip_arity(label: &str) -> &str {
    if let Some(idx) = label.rfind('_')
        && idx > 0
        && idx + 1 < label.len()
        && label[idx + 1..].bytes().all(|b| b.is_ascii_digit())
    {
        return &label[..idx];
    }
    label
}

/// The low-level tree algebra: operation symbols build tree nodes. With `with_arities`, the
/// arity suffix on each symbol (`f_2`) is stripped when producing the node label.
///
/// `scratch` is the arena that internal values ([`Tree`] handles) point into; it is reset by
/// [`to_external`](Algebra::to_external) after each term is harvested.
#[derive(Debug)]
pub struct TreeAlgebra {
    signature: Signature,
    with_arities: bool,
    scratch: RefCell<TreeArena<String>>,
}

impl TreeAlgebra {
    /// Plain tree algebra (`TreeAlgebra`).
    pub fn tree(signature: Signature) -> Self {
        Self {
            signature,
            with_arities: false,
            scratch: RefCell::new(TreeArena::new()),
        }
    }

    /// Arity-annotated tree algebra (`TreeWithAritiesAlgebra`).
    pub fn with_arities(signature: Signature) -> Self {
        Self {
            signature,
            with_arities: true,
            scratch: RefCell::new(TreeArena::new()),
        }
    }

    /// Resolve an operation symbol to its node label, stripping the arity suffix if configured.
    fn node_label(&self, symbol: Symbol) -> String {
        let name = self.signature.resolve(symbol);
        if self.with_arities {
            strip_arity(name).to_owned()
        } else {
            name.to_owned()
        }
    }
}

impl Algebra for TreeAlgebra {
    type InternalValue = Tree; // a handle into `self.scratch`
    type Value = TreeValue;
    type ParseError = TreeParseError;

    fn signature(&self) -> &Signature {
        &self.signature
    }

    fn evaluate(
        &self,
        symbol: Symbol,
        children: &[Self::InternalValue],
    ) -> Option<Self::InternalValue> {
        let label = self.node_label(symbol);
        Some(self.scratch.borrow_mut().add_node(label, children.to_vec()))
    }

    fn to_external(&self, value: &Self::InternalValue) -> Self::Value {
        let mut out = TreeArena::new();
        let root = copy_subtree(&self.scratch.borrow(), *value, &mut out);
        // The internal value has been harvested into its own arena; reset the scratch.
        *self.scratch.borrow_mut() = TreeArena::new();
        TreeValue::new(out, root)
    }

    fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError> {
        // Tree algebras are output-only; this is provided for completeness and parses the surface
        // tree into the scratch arena, returning its root handle.
        parse_tree(&mut self.scratch.borrow_mut(), input)
    }
}

/// A binarizing adapter around an arbitrary algebra (Alto's `BinarizingAlgebra<E>`).
///
/// Before delegating evaluation to `inner`, it collapses the binary append symbol: an `_@_(a, b)`
/// node splices its children's forests together, so a right-branching binary spine becomes a flat
/// child list of the surrounding node. The unbinarization is purely structural and independent of
/// what `inner` does with the resulting term.
#[derive(Debug)]
pub struct Binarizing<A> {
    inner: A,
    append: Option<Symbol>,
}

impl<A> Binarizing<A> {
    /// Wrap `inner`, collapsing `append` (typically [`APPEND_SYMBOL`]). If `append` is `None`,
    /// evaluation is delegated unchanged.
    pub fn new(inner: A, append: Option<Symbol>) -> Self {
        Self { inner, append }
    }

    /// Unbinarize the subtree at `node`, building the result into `dst`; returns the resulting
    /// forest (a single tree, except where an append node spliced several together).
    fn unbinarize(
        &self,
        src: &TreeArena<Symbol>,
        node: Tree,
        dst: &mut TreeArena<Symbol>,
    ) -> Vec<Tree> {
        let label = *src.get_label(node);
        let children = src.get_children(node);
        if self.append == Some(label) {
            let mut forest = Vec::new();
            for &child in children {
                forest.extend(self.unbinarize(src, child, dst));
            }
            forest
        } else {
            let mut flattened = Vec::new();
            for &child in children {
                flattened.extend(self.unbinarize(src, child, dst));
            }
            vec![dst.add_node(label, flattened)]
        }
    }
}

impl<A: Algebra> Algebra for Binarizing<A> {
    type InternalValue = A::InternalValue;
    type Value = A::Value;
    type ParseError = A::ParseError;

    fn signature(&self) -> &Signature {
        self.inner.signature()
    }

    fn evaluate(
        &self,
        _symbol: Symbol,
        _children: &[Self::InternalValue],
    ) -> Option<Self::InternalValue> {
        // A per-node combinator is undefined for binarization (intermediate values are forests);
        // `evaluate_term` is overridden instead. Mirrors Alto's `UnsupportedOperationException`.
        None
    }

    fn to_external(&self, value: &Self::InternalValue) -> Self::Value {
        self.inner.to_external(value)
    }

    fn evaluate_term(&self, arena: &TreeArena<Symbol>, root: Tree) -> Option<Self::Value> {
        let mut unbinarized = TreeArena::new();
        let forest = self.unbinarize(arena, root, &mut unbinarized);
        if forest.len() != 1 {
            return None;
        }
        self.inner.evaluate_term(&unbinarized, forest[0])
    }

    fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError> {
        self.inner.parse_object(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sig(symbols: &[(&str, usize)]) -> Signature {
        let mut signature = Signature::new();
        for &(name, arity) in symbols {
            signature.intern(name.to_owned(), arity).unwrap();
        }
        signature
    }

    /// Build a `TreeArena<Symbol>` term from a rusty_tree-parsed repr (symbols must be in `sig`).
    fn term(signature: &Signature, repr: &str) -> (TreeArena<Symbol>, Tree) {
        let mut str_arena = TreeArena::new();
        let root = parse_tree(&mut str_arena, repr).unwrap();
        fn map(
            sig: &Signature,
            src: &TreeArena<String>,
            node: Tree,
            dst: &mut TreeArena<Symbol>,
        ) -> Tree {
            let symbol = sig.get(src.get_label(node)).expect("symbol in signature");
            let children: Vec<Tree> = src
                .get_children(node)
                .iter()
                .map(|&c| map(sig, src, c, dst))
                .collect();
            dst.add_node(symbol, children)
        }
        let mut arena = TreeArena::new();
        let new_root = map(signature, &str_arena, root, &mut arena);
        (arena, new_root)
    }

    #[test]
    fn display_quotes_special_labels() {
        let mut arena = TreeArena::new();
        let comma = arena.add_node(",".to_owned(), vec![]);
        let np = arena.add_node("NP-SBJ".to_owned(), vec![]);
        let root = arena.add_node("S".to_owned(), vec![comma, np]);
        assert_eq!(TreeValue::new(arena, root).to_string(), "S(',', NP-SBJ)");
    }

    #[test]
    fn with_arities_strips_suffixes() {
        let signature = sig(&[("S_2", 2), ("NP_0", 0), ("VP_0", 0)]);
        let algebra = TreeAlgebra::with_arities(signature.clone());
        let (arena, root) = term(&signature, "S_2(NP_0, VP_0)");
        assert_eq!(
            algebra.evaluate_term(&arena, root).unwrap().to_string(),
            "S(NP, VP)"
        );
    }

    #[test]
    fn binarizing_unbinarizes_then_strips() {
        // S_3('_@_'(NP_0, '_@_'(V_0, NP_0))) -> S(NP, V, NP). `_@_` is quoted only because this
        // test parses via rusty_tree; real hom images are built by `Homomorphism::apply`.
        let signature = sig(&[("S_3", 3), ("NP_0", 0), ("V_0", 0), (APPEND_SYMBOL, 2)]);
        let inner = TreeAlgebra::with_arities(signature.clone());
        let algebra = Binarizing::new(inner, signature.get(APPEND_SYMBOL));
        let (arena, root) = term(&signature, "S_3('_@_'(NP_0, '_@_'(V_0, NP_0)))");
        assert_eq!(
            algebra.evaluate_term(&arena, root).unwrap().to_string(),
            "S(NP, V, NP)"
        );
    }

    #[test]
    fn binarizing_without_append_is_identity() {
        let signature = sig(&[("S_1", 1), ("NP_0", 0)]);
        let inner = TreeAlgebra::with_arities(signature.clone());
        let algebra = Binarizing::new(inner, None);
        let (arena, root) = term(&signature, "S_1(NP_0)");
        assert_eq!(
            algebra.evaluate_term(&arena, root).unwrap().to_string(),
            "S(NP)"
        );
    }

    #[test]
    fn parse_object_round_trips() {
        let mut algebra = TreeAlgebra::with_arities(Signature::new());
        let internal = algebra.parse_object("S(NP, VP(V, NP))").unwrap();
        assert_eq!(algebra.to_external(&internal).to_string(), "S(NP, VP(V, NP))");
    }
}
