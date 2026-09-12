//! Equality-indexed sibling-finder intersection.
//!
//! This module combines inverse homomorphism and automaton intersection in one
//! bottom-up chart construction.  Decomposition automata only provide an
//! equality key for each side of a binary operation.  The generic algorithm
//! lifts those local chart indexes through homomorphism terms.

use crate::{
    BottomUpTa, Explicit, FxHashMap, HomLabel, Homomorphism, Interner, ParseControl, StateId,
    Symbol, control::ParseCancelled,
};
use packed_term_arena::tree::{Tree, TreeArena};
use smallvec::SmallVec;
use std::hash::Hash;
use thiserror::Error;

/// A decomposition automaton whose binary transitions admit equality-indexed
/// partner lookup.
///
/// If `f(left, right)` is a valid transition, both calls to `sibling_key` must
/// return equal keys. Returning equal keys for an invalid pair is allowed: the
/// sibling materializer validates candidates with [`BottomUpTa::step`].
pub trait SiblingKeyedTa: BottomUpTa {
    /// Equality key stored in the local chart indexes.
    type Key: Clone + Eq + Hash;

    /// Return the partner-lookup key for `state` in child `position` of `f`.
    /// `None` means that the state cannot occur in that position.
    fn sibling_key(&self, f: Symbol, position: usize, state: &Self::State) -> Option<Self::Key>;
}

/// Failure while constructing a sibling-finder intersection.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SiblingIntersectionError {
    /// Parsing was cancelled through the supplied control.
    #[error("parsing was cancelled")]
    Cancelled,
    /// The selected decomposition algebra does not provide sibling keys.
    #[error("the decomposition algebra does not provide sibling keys")]
    UnsupportedDecomposition,
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
    /// Equal-key partner candidates considered.
    pub partner_candidates: usize,
    /// Calls to the decomposition automaton's transition oracle.
    pub right_step_calls: usize,
    /// Completed homomorphism-root items.
    pub root_items: usize,
}

#[derive(Clone, Copy)]
struct ParentLink {
    node: usize,
    position: usize,
}

struct CompiledOperation {
    symbol: Symbol,
    children: SmallVec<[usize; 2]>,
}

struct NodePlan {
    parent: Option<ParentLink>,
    operation: Option<CompiledOperation>,
    assignment_width: usize,
}

struct CompiledTerm {
    nodes: Vec<NodePlan>,
    variable_nodes: Vec<usize>,
    /// Root assignment offsets in source-child order; empty means identity.
    root_permutation: SmallVec<[usize; 4]>,
}

impl CompiledTerm {
    fn arity(&self) -> usize {
        self.variable_nodes.len()
    }
}

const ROOT_NODE: usize = 0;

fn compile_term(
    arena: &TreeArena<HomLabel>,
    root: Tree,
    arity: usize,
) -> Result<CompiledTerm, SiblingIntersectionError> {
    fn visit(
        arena: &TreeArena<HomLabel>,
        term: Tree,
        parent: Option<ParentLink>,
        nodes: &mut Vec<NodePlan>,
        variables: &mut [usize],
    ) -> Result<(usize, SmallVec<[usize; 4]>), SiblingIntersectionError> {
        let id = nodes.len();
        nodes.push(NodePlan {
            parent,
            operation: None,
            assignment_width: 0,
        });

        let (kind, node_variables) = match *arena.get_label(term) {
            HomLabel::Var(position) => {
                variables[position] = id;
                (None, smallvec::smallvec![position])
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
                (Some(CompiledOperation { symbol, children }), node_variables)
            }
        };
        nodes[id].operation = kind;
        nodes[id].assignment_width = node_variables.len();
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
    Ok(CompiledTerm {
        nodes,
        variable_nodes,
        root_permutation,
    })
}

struct BinaryIndex<K> {
    positions: [FxHashMap<K, Vec<usize>>; 2],
}

impl<K> Default for BinaryIndex<K> {
    fn default() -> Self {
        Self {
            positions: std::array::from_fn(|_| FxHashMap::default()),
        }
    }
}

/// Materialize the complete bottom-up intersection of `left` with the inverse
/// homomorphic image of `decomp`, using equality-indexed sibling lookup.
#[allow(clippy::type_complexity)]
pub fn materialize_sibling_intersection<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
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
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    materialize_sibling_intersection_controlled(left, decomp, hom, &ParseControl::new())
}

/// Cancellable counterpart of [`materialize_sibling_intersection`].
#[allow(clippy::type_complexity)]
pub(crate) fn materialize_sibling_intersection_controlled<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
    control: &ParseControl,
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
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    condensed::materialize(left, decomp, hom, control)
}

mod condensed;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ExplicitBuilder, FxHashSet, StringAlgebra,
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
        let (indexed, indexed_states, indexed_pairs, _) =
            materialize_indexed_condensed_intersection_with_pairs(&left, &invhom);
        let (sibling, sibling_states, sibling_pairs, _) =
            materialize_sibling_intersection(&left, &decomp, &hom).unwrap();

        assert_eq!(
            normalized_chart(&sibling, &sibling_states, &sibling_pairs),
            normalized_chart(&indexed, &indexed_states, &indexed_pairs)
        );
    }
}
