//! Sibling-indexed bottom-up intersection for interpreted grammars.
//!
//! The algorithm fuses inverse homomorphism with automaton intersection. A
//! reachable product state `(p, q)` activates occurrences of the corresponding
//! homomorphism variable. Decomposition states then propagate upward through a
//! compiled homomorphism term. At a binary term node, an algebra-specific
//! [`BinarySiblingIndex`] finds the items that can form a decomposition
//! transition with the new item. A completed root item is the condensed
//! inverse-homomorphism transition described in `sibling-finder.typ`; it is
//! subsequently joined with every compatible source rule.
//!
//! This module defines the algebra-facing interface and compiles homomorphism
//! terms. The private execution engine owns the term charts, product-state
//! agenda, and final join.

use crate::{
    BottomUpTa, Explicit, FxHashMap, HomLabel, Homomorphism, Interner, ParseControl, StateId,
    Symbol, control::ParseCancelled,
};
use packed_term_arena::tree::{Tree, TreeArena};
use smallvec::SmallVec;
use std::hash::Hash;
use thiserror::Error;

/// Algebra-specific partner index for one occurrence of a binary operation.
///
/// The term chart creates a separate index for every binary node of every term
/// program. Items are added at child position `0` or `1`. When an item arrives,
/// [`partners`](Self::partners) returns item IDs already stored at the opposite
/// position that can be combined with it.
///
/// Unlike the equality-key interface in earlier versions of the design, this
/// interface does not expose keys to the generic algorithm. An implementation
/// may use a boundary array, a multidimensional array, or another representation.
/// It must return all and only compatible partners. The engine still calls the
/// decomposition automaton to construct the parent state and debug-checks that
/// an indexed pair has at least one result.
///
/// Returned slices borrow the index and need not be sorted. The engine relies on
/// append-only item IDs remaining valid for the lifetime of the term chart.
pub trait BinarySiblingIndex<State> {
    /// Record `item` and its decomposition `state` at child `position`.
    ///
    /// The engine adds each term-chart item once at each binary occurrence that
    /// consumes it. `position` is therefore always `0` or `1`.
    fn add(&mut self, position: usize, state: &State, item: usize);

    /// Borrow the compatible item IDs stored at the other child position.
    ///
    /// Only items added before this call may be returned. The result must be
    /// complete and contain no incompatible item, but its order is unspecified.
    fn partners(&self, position: usize, state: &State) -> &[usize];
}

/// Creates the sibling index chosen by a decomposition automaton's algebra.
///
/// The factory is separate from the decomposition automaton so sibling finding
/// remains an optional parsing strategy rather than part of [`BottomUpTa`]. The
/// engine is generic over both `D` and this factory, so calls to [`add`](BinarySiblingIndex::add)
/// and [`partners`](BinarySiblingIndex::partners) are statically dispatched and
/// can compile to direct array access.
///
/// A factory is normally a zero-sized value. It receives the actual
/// decomposition automaton when constructing an index because input-dependent
/// dimensions, such as the number of string boundaries, belong to that
/// automaton.
pub trait SiblingIndexFactory<D: BottomUpTa> {
    /// Concrete index type, statically dispatched by the materializer.
    type Index: BinarySiblingIndex<D::State>;

    /// Create an empty index for one binary occurrence of `symbol`.
    ///
    /// Return `None` if sibling finding does not support that operation. The
    /// materialization then fails with
    /// [`SiblingIntersectionError::SiblingIndexUnavailable`].
    fn new_index(&self, decomp: &D, symbol: Symbol) -> Option<Self::Index>;
}

/// Failure while constructing a sibling-finder intersection.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SiblingIntersectionError {
    /// Parsing was cancelled through the supplied control.
    #[error("parsing was cancelled")]
    Cancelled,
    /// No sibling index is available for the requested decomposition operation.
    #[error("no sibling index is available for a binary target operation")]
    SiblingIndexUnavailable,
    /// A homomorphic image contains a target operation above binary rank.
    #[error("sibling intersection supports target rank at most 2, but {symbol:?} has rank {arity}")]
    UnsupportedTargetArity {
        /// Target operation in the homomorphic term.
        symbol: Symbol,
        /// Number of children at that occurrence.
        arity: usize,
    },
}

impl From<ParseCancelled> for SiblingIntersectionError {
    fn from(_: ParseCancelled) -> Self {
        Self::Cancelled
    }
}

/// Counters from one sibling-finder intersection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SiblingIntersectionStats {
    /// Product states in the resulting chart.
    pub output_states: usize,
    /// Rules in the resulting chart.
    pub output_rules: usize,
    /// Product states removed from the bottom-up agenda.
    pub agenda_pops: usize,
    /// New facts inserted into homomorphism-term charts.
    pub term_items: usize,
    /// Compatible sibling candidates considered.
    pub partner_candidates: usize,
    /// Calls to the decomposition automaton's transition oracle.
    pub right_step_calls: usize,
    /// Completed homomorphism-root items.
    pub root_items: usize,
}

/// Location of a term-program node in its parent's child list.
#[derive(Clone, Copy)]
struct ParentLink {
    node: usize,
    position: usize,
}

/// Compiled data needed to evaluate one algebra operation.
struct CompiledOperation {
    symbol: Symbol,
    children: SmallVec<[usize; 2]>,
}

/// One node of a compiled homomorphism term.
///
/// Variables are activation points for product states. Operations are evaluated
/// after their child items become available. Keeping the cases explicit avoids
/// representing a variable as an operation that happens to be absent.
enum CompiledNode {
    Variable {
        parent: Option<ParentLink>,
    },
    Operation {
        parent: Option<ParentLink>,
        operation: CompiledOperation,
        assignment_width: usize,
    },
}

impl CompiledNode {
    fn parent(&self) -> Option<ParentLink> {
        match self {
            Self::Variable { parent } | Self::Operation { parent, .. } => *parent,
        }
    }

    fn operation(&self) -> Option<&CompiledOperation> {
        match self {
            Self::Variable { .. } => None,
            Self::Operation { operation, .. } => Some(operation),
        }
    }

    fn assignment_width(&self) -> usize {
        match self {
            Self::Variable { .. } => 1,
            Self::Operation {
                assignment_width, ..
            } => *assignment_width,
        }
    }
}

/// Input-independent program for one homomorphism right-hand side.
///
/// The program is shared by every source rule whose label has this image. It
/// contains no decomposition states; those live in a per-input running program.
struct CompiledTerm {
    /// Term nodes in preorder; the root therefore has ID [`ROOT_NODE`].
    nodes: Vec<CompiledNode>,
    /// Node activated by each source-rule child position.
    variable_nodes: Vec<usize>,
    /// Root assignment offsets in source-child order; empty means identity.
    root_permutation: SmallVec<[usize; 4]>,
}

impl CompiledTerm {
    /// Number of children of every source rule represented by this program.
    fn arity(&self) -> usize {
        self.variable_nodes.len()
    }
}

const ROOT_NODE: usize = 0;

/// Compile a homomorphism term into the parent/child links used for propagation.
///
/// `arity` is the arity of the source rule, not the rank of the target root.
/// The homomorphism is nondeleting, so every source position must occur once in
/// `variable_nodes`. Target operations above binary rank are rejected here,
/// before any input-sized chart is allocated.
fn compile_term(
    arena: &TreeArena<HomLabel>,
    root: Tree,
    arity: usize,
) -> Result<CompiledTerm, SiblingIntersectionError> {
    // Reserve a preorder ID before visiting the children so every child can
    // record its parent without a second tree traversal. The temporary `None`
    // is consumed before the compiled term escapes this function.
    fn visit(
        arena: &TreeArena<HomLabel>,
        term: Tree,
        parent: Option<ParentLink>,
        nodes: &mut Vec<Option<CompiledNode>>,
        variables: &mut [usize],
    ) -> Result<(usize, SmallVec<[usize; 4]>), SiblingIntersectionError> {
        let id = nodes.len();
        nodes.push(None);

        let node_variables = match *arena.get_label(term) {
            HomLabel::Var(position) => {
                variables[position] = id;
                nodes[id] = Some(CompiledNode::Variable { parent });
                smallvec::smallvec![position]
            }
            HomLabel::Symbol(symbol) => {
                let term_children = arena.get_children(term);
                if term_children.len() > 2 {
                    return Err(SiblingIntersectionError::UnsupportedTargetArity {
                        symbol,
                        arity: term_children.len(),
                    });
                }
                let mut children = SmallVec::new();
                let mut node_variables = SmallVec::new();
                for (position, &child) in term_children.iter().enumerate() {
                    let (child, child_variables) = visit(
                        arena,
                        child,
                        Some(ParentLink { node: id, position }),
                        nodes,
                        variables,
                    )?;
                    children.push(child);
                    node_variables.extend_from_slice(&child_variables);
                }
                nodes[id] = Some(CompiledNode::Operation {
                    parent,
                    operation: CompiledOperation { symbol, children },
                    assignment_width: node_variables.len(),
                });
                node_variables
            }
        };
        Ok((id, node_variables))
    }

    let mut nodes = Vec::new();
    let mut variable_nodes = vec![usize::MAX; arity];
    let (root, root_variables) = visit(arena, root, None, &mut nodes, &mut variable_nodes)?;
    debug_assert_eq!(root, ROOT_NODE);
    debug_assert!(variable_nodes.iter().all(|&node| node != usize::MAX));
    let mut root_permutation = smallvec::smallvec![0; arity];
    for (offset, &variable) in root_variables.iter().enumerate() {
        root_permutation[variable] = offset;
    }
    if root_permutation
        .iter()
        .enumerate()
        .all(|(source, &offset)| source == offset)
    {
        root_permutation.clear();
    }
    let nodes = nodes
        .into_iter()
        .map(|node| node.expect("every compiled node is initialized"))
        .collect();
    Ok(CompiledTerm {
        nodes,
        variable_nodes,
        root_permutation,
    })
}

/// Materialize the complete bottom-up intersection of `left` with the inverse
/// homomorphic image of `decomp`, using `sibling_indexes` for binary joins.
///
/// Equal homomorphism right-hand sides share one term program and one term
/// chart. The returned automaton is the complete packed parse chart, not a
/// one-best or goal-directed result. Its state IDs index both the returned
/// `pairs` vector and the states of the returned `Explicit` automaton.
///
/// Target operations inside a homomorphic image may have rank at most two, but
/// source rules may have any arity. Unsupported binary target operations and
/// higher-rank target operations are reported as errors.
#[allow(clippy::type_complexity)]
pub fn materialize_sibling_intersection<D, F>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
    sibling_indexes: &F,
) -> Result<
    (
        Explicit,
        Interner<D::State>,
        Vec<(StateId, StateId)>,
        SiblingIntersectionStats,
    ),
    SiblingIntersectionError,
>
where
    D: BottomUpTa,
    D::State: Clone + Eq + Hash,
    F: SiblingIndexFactory<D>,
{
    let compiled = CompiledSiblingGrammar::new(left, hom)?;
    engine::materialize_compiled(decomp, &compiled, sibling_indexes, &ParseControl::new())
}

mod engine;
pub(crate) use engine::{CompiledSiblingGrammar, materialize_compiled};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ExplicitBuilder, FxHashSet, StringAlgebra, StringSiblingIndexFactory,
        materialize_indexed_condensed_intersection_with_pairs,
    };

    fn normalized_chart(
        chart: &Explicit,
        right_states: &Interner<crate::algebras::Span>,
        pairs: &[(StateId, StateId)],
    ) -> (FxHashSet<String>, FxHashSet<String>) {
        let state = |id: StateId| {
            let (left, right) = pairs[id.index()];
            format!("{}:{:?}", left.index(), right_states.resolve(right))
        };
        let rules = chart
            .rules()
            .map(|rule| {
                format!(
                    "{:?}({:?})->{}@{:016x}",
                    rule.symbol,
                    rule.children
                        .iter()
                        .map(|&child| state(child))
                        .collect::<Vec<_>>(),
                    state(rule.result),
                    rule.weight.to_bits()
                )
            })
            .collect();
        let accepting = pairs
            .iter()
            .enumerate()
            .filter_map(|(id, _)| {
                let id = StateId(id as u32);
                chart.is_accepting(&id).then(|| state(id))
            })
            .collect();
        (rules, accepting)
    }

    #[test]
    fn nested_permuted_rhs_matches_indexed_chart_exactly() {
        let mut algebra = StringAlgebra::new();
        let sentence = algebra.parse_string("a b c d");
        let [a, b, c, d] = sentence.as_slice() else {
            unreachable!()
        };
        let decomp = algebra.decompose(sentence.clone());
        let concat = algebra.concat_symbol();

        let leaf_a = Symbol(100);
        let leaf_b = Symbol(101);
        let leaf_c = Symbol(102);
        let ternary = Symbol(103);
        let unary = Symbol(104);
        let mut hom = Homomorphism::new();
        for (source, target) in [(leaf_a, *a), (leaf_b, *b), (leaf_c, *c)] {
            let rhs = hom.add_symbol(target, Vec::new());
            hom.add(source, 0, rhs).unwrap();
        }
        let v0 = hom.add_var(0);
        let v1 = hom.add_var(1);
        let v2 = hom.add_var(2);
        let tail = hom.add_symbol(concat, vec![v0, v1]);
        let permuted = hom.add_symbol(concat, vec![v2, tail]);
        hom.add(ternary, 3, permuted).unwrap();
        let v0 = hom.add_var(0);
        let d = hom.add_symbol(*d, Vec::new());
        let with_ground_tail = hom.add_symbol(concat, vec![v0, d]);
        hom.add(unary, 1, with_ground_tail).unwrap();

        let mut builder = ExplicitBuilder::new();
        let qa = builder.new_state();
        let qb = builder.new_state();
        let qc = builder.new_state();
        let phrase = builder.new_state();
        let root = builder.new_state();
        builder.add_weighted_rule(leaf_a, Vec::new(), qa, 0.9);
        builder.add_weighted_rule(leaf_b, Vec::new(), qb, 0.8);
        builder.add_weighted_rule(leaf_c, Vec::new(), qc, 0.7);
        builder.add_weighted_rule(ternary, vec![qb, qc, qa], phrase, 0.6);
        builder.add_weighted_rule(unary, vec![phrase], root, 0.5);
        builder.add_accepting(root);
        let left = builder.build();

        let invhom = crate::InvHom::new(decomp.clone(), &hom);
        let sibling_indexes = StringSiblingIndexFactory;
        let (indexed, indexed_states, indexed_pairs, _) =
            materialize_indexed_condensed_intersection_with_pairs(&left, &invhom);
        let (sibling, sibling_states, sibling_pairs, sibling_stats) =
            materialize_sibling_intersection(&left, &decomp, &hom, &sibling_indexes).unwrap();

        assert_eq!(sibling.rules().count(), indexed.rules().count());
        assert_eq!(sibling_stats.output_rules, sibling.rules().count());
        assert_eq!(
            normalized_chart(&sibling, &sibling_states, &sibling_pairs),
            normalized_chart(&indexed, &indexed_states, &indexed_pairs)
        );
    }
}
