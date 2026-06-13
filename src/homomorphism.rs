use crate::{FxHashMap, Symbol};
use rusty_tree::tree::{MutAlgebra, Tree, TreeArena};
use smallvec::SmallVec;
use thiserror::Error;

/// Label used in a homomorphism right-hand side tree.
///
/// `Symbol(g)` is an output-signature symbol. `Var(i)` is a placeholder for
/// the homomorphic image of the `i`-th child of the source node. Variables are
/// intentionally separate from output symbols, so homomorphisms can share the
/// same symbol IDs as automata, algebras, and parsed trees.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum HomLabel {
    /// A real output-signature symbol.
    Symbol(Symbol),
    /// Variable `?i`, referring to source child `i`.
    Var(usize),
}

/// Root handle of a homomorphism right-hand side term.
///
/// The nodes live in an externally owned [`TreeArena<HomLabel>`]. This lets
/// callers synchronize symbol IDs and share tree storage with surrounding data
/// structures instead of copying recursive term objects into the homomorphism.
pub type HomTerm = Tree;

/// Error returned when constructing or applying a homomorphism.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum HomomorphismError {
    /// The same source symbol was registered twice with different source arity.
    #[error("source symbol {symbol:?} was registered with arity {first}, then {second}")]
    ArityMismatch {
        /// Source symbol whose arity conflicts.
        symbol: Symbol,
        /// Previously registered arity.
        first: usize,
        /// Newly requested arity.
        second: usize,
    },
    /// The same source symbol was registered twice with different image terms.
    #[error("source symbol {symbol:?} was registered with a different image term")]
    ConflictingSourceTerm {
        /// Source symbol whose image term conflicts.
        symbol: Symbol,
    },
    /// A required variable does not occur in the image term.
    #[error("source symbol {symbol:?} image is missing variable ?{variable}")]
    MissingVariable {
        /// Source symbol being registered.
        symbol: Symbol,
        /// Missing source-child variable.
        variable: usize,
    },
    /// A variable occurs more than once in the image term.
    #[error("source symbol {symbol:?} image uses variable ?{variable} more than once")]
    DuplicateVariable {
        /// Source symbol being registered.
        symbol: Symbol,
        /// Duplicated source-child variable.
        variable: usize,
    },
    /// The image term mentions a variable outside the source arity.
    #[error("source symbol {symbol:?} image uses variable ?{variable}, but arity is {arity}")]
    OutOfRangeVariable {
        /// Source symbol being registered.
        symbol: Symbol,
        /// Variable index found in the image.
        variable: usize,
        /// Source arity of the symbol.
        arity: usize,
    },
    /// A source tree contains a symbol for which no image term was registered.
    #[error("source symbol {symbol:?} has no homomorphic image")]
    UnmappedSymbol {
        /// Unmapped source symbol.
        symbol: Symbol,
    },
    /// Applying a homomorphism found a variable that has no corresponding child.
    #[error("image variable ?{variable} cannot be substituted for source arity {arity}")]
    ApplyVariableOutOfRange {
        /// Variable index in the image term.
        variable: usize,
        /// Number of mapped source children available.
        arity: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TermKey {
    Var(usize),
    Symbol(Symbol, Vec<TermKey>),
}

/// A nondeleting tree homomorphism from source symbols to output terms.
///
/// Each source symbol `f` of arity `k` maps to a tree over [`HomLabel`] whose
/// variables are exactly `?0 .. ?{k-1}`, each occurring once. Construction
/// enforces this nondeleting invariant because inverse-homomorphism algorithms
/// rely on every source child being represented by exactly one target state.
///
/// Structurally identical image terms are stored once as a *term id*. All
/// source symbols sharing that image are kept in the same label set, which is
/// the basis for condensed inverse-homomorphism rules.
#[derive(Clone, Debug)]
pub struct Homomorphism<'a> {
    arena: &'a TreeArena<HomLabel>,
    terms: Vec<HomTerm>,
    labels: Vec<SmallVec<[Symbol; 2]>>,
    symbol_to_term: FxHashMap<Symbol, usize>,
    arities: FxHashMap<Symbol, usize>,
    term_dedup: FxHashMap<TermKey, usize>,
    root_index: FxHashMap<Symbol, Vec<usize>>,
}

impl<'a> Homomorphism<'a> {
    /// Create an empty homomorphism whose right-hand sides live in `arena`.
    pub fn new(arena: &'a TreeArena<HomLabel>) -> Self {
        Self {
            arena,
            terms: Vec::new(),
            labels: Vec::new(),
            symbol_to_term: FxHashMap::default(),
            arities: FxHashMap::default(),
            term_dedup: FxHashMap::default(),
            root_index: FxHashMap::default(),
        }
    }

    /// Return the arena that owns all registered image terms.
    pub fn arena(&self) -> &'a TreeArena<HomLabel> {
        self.arena
    }

    /// Register `src` with source arity `src_arity` and image term `rhs`.
    ///
    /// The image must be nondeleting: variables `?0` through `?{src_arity-1}`
    /// occur exactly once each, with no duplicates and no out-of-range
    /// variables. Re-registering the same source symbol is accepted only when
    /// both the arity and image term are structurally identical.
    pub fn add(
        &mut self,
        src: Symbol,
        src_arity: usize,
        rhs: HomTerm,
    ) -> Result<(), HomomorphismError> {
        if let Some(&old) = self.arities.get(&src) {
            if old != src_arity {
                return Err(HomomorphismError::ArityMismatch {
                    symbol: src,
                    first: old,
                    second: src_arity,
                });
            }
        }

        self.validate_nondeleting(src, src_arity, rhs)?;
        let key = self.term_key(rhs);

        if let Some(&old_term_id) = self.symbol_to_term.get(&src) {
            let old_key = self.term_key(self.terms[old_term_id]);
            if old_key != key {
                return Err(HomomorphismError::ConflictingSourceTerm { symbol: src });
            }
            return Ok(());
        }

        let term_id = if let Some(&tid) = self.term_dedup.get(&key) {
            tid
        } else {
            let tid = self.terms.len();
            if let HomLabel::Symbol(symbol) = *self.arena.get_label(rhs) {
                self.root_index.entry(symbol).or_default().push(tid);
            }
            self.term_dedup.insert(key, tid);
            self.terms.push(rhs);
            self.labels.push(SmallVec::new());
            tid
        };

        self.arities.insert(src, src_arity);
        self.symbol_to_term.insert(src, term_id);
        self.labels[term_id].push(src);
        Ok(())
    }

    /// Return the image term root for `src`, or `None` if `src` is unmapped.
    pub fn get(&self, src: Symbol) -> Option<HomTerm> {
        let &tid = self.symbol_to_term.get(&src)?;
        Some(self.terms[tid])
    }

    /// Return the term id for `src`, or `None` if `src` is unmapped.
    pub fn term_id(&self, src: Symbol) -> Option<usize> {
        self.symbol_to_term.get(&src).copied()
    }

    /// Return all source symbols whose image has the given term id.
    pub fn label_set(&self, term_id: usize) -> &[Symbol] {
        &self.labels[term_id]
    }

    /// Return the source arity of `src`, or `None` if `src` is unmapped.
    pub fn source_arity(&self, src: Symbol) -> Option<usize> {
        self.arities.get(&src).copied()
    }

    /// Iterate over all distinct image terms and their source-symbol label sets.
    pub fn term_sets(&self) -> impl Iterator<Item = (usize, &[Symbol], HomTerm)> + '_ {
        self.terms
            .iter()
            .copied()
            .enumerate()
            .map(|(tid, term)| (tid, self.labels[tid].as_slice(), term))
    }

    /// Return the number of structurally distinct image terms.
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Return the image term root for a term id.
    pub fn term_by_id(&self, term_id: usize) -> HomTerm {
        self.terms[term_id]
    }

    /// Return term ids whose image has `sym` as root output symbol.
    pub fn terms_with_root(&self, sym: Symbol) -> &[usize] {
        self.root_index
            .get(&sym)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// Apply the homomorphism to an input tree.
    ///
    /// The input tree uses source symbols. The resulting tree is appended to
    /// `output_arena` and uses output symbols only; variables are substituted by
    /// the already-mapped child result trees. Source symbols without a
    /// registered image return [`HomomorphismError::UnmappedSymbol`].
    pub fn apply(
        &self,
        input_arena: &TreeArena<Symbol>,
        input_root: Tree,
        output_arena: &mut TreeArena<Symbol>,
    ) -> Result<Tree, HomomorphismError> {
        let mut alg = ApplyAlg {
            hom: self,
            output_arena,
        };
        input_arena.map(input_root, |symbol| *symbol, &mut alg)
    }

    fn validate_nondeleting(
        &self,
        src: Symbol,
        src_arity: usize,
        rhs: HomTerm,
    ) -> Result<(), HomomorphismError> {
        let mut seen = vec![false; src_arity];
        let mut vars = Vec::new();
        self.collect_vars(rhs, &mut vars);
        for variable in vars {
            if variable >= src_arity {
                return Err(HomomorphismError::OutOfRangeVariable {
                    symbol: src,
                    variable,
                    arity: src_arity,
                });
            }
            if seen[variable] {
                return Err(HomomorphismError::DuplicateVariable {
                    symbol: src,
                    variable,
                });
            }
            seen[variable] = true;
        }
        for (variable, was_seen) in seen.into_iter().enumerate() {
            if !was_seen {
                return Err(HomomorphismError::MissingVariable {
                    symbol: src,
                    variable,
                });
            }
        }
        Ok(())
    }

    fn collect_vars(&self, term: HomTerm, out: &mut Vec<usize>) {
        match *self.arena.get_label(term) {
            HomLabel::Var(variable) => out.push(variable),
            HomLabel::Symbol(_) => {
                for &child in self.arena.get_children(term) {
                    self.collect_vars(child, out);
                }
            }
        }
    }

    fn term_key(&self, term: HomTerm) -> TermKey {
        match *self.arena.get_label(term) {
            HomLabel::Var(variable) => TermKey::Var(variable),
            HomLabel::Symbol(symbol) => TermKey::Symbol(
                symbol,
                self.arena
                    .get_children(term)
                    .iter()
                    .map(|&child| self.term_key(child))
                    .collect(),
            ),
        }
    }

    fn instantiate(
        &self,
        rhs: HomTerm,
        mapped_children: &[Tree],
        output_arena: &mut TreeArena<Symbol>,
    ) -> Result<Tree, HomomorphismError> {
        match *self.arena.get_label(rhs) {
            HomLabel::Var(variable) => mapped_children.get(variable).copied().ok_or(
                HomomorphismError::ApplyVariableOutOfRange {
                    variable,
                    arity: mapped_children.len(),
                },
            ),
            HomLabel::Symbol(symbol) => {
                let children = self
                    .arena
                    .get_children(rhs)
                    .iter()
                    .map(|&child| self.instantiate(child, mapped_children, output_arena))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(output_arena.add_node(symbol, children))
            }
        }
    }
}

struct ApplyAlg<'h, 'out, 'arena> {
    hom: &'h Homomorphism<'arena>,
    output_arena: &'out mut TreeArena<Symbol>,
}

impl MutAlgebra<Symbol, Result<Tree, HomomorphismError>> for ApplyAlg<'_, '_, '_> {
    fn apply(
        &mut self,
        src: Symbol,
        children: Vec<Result<Tree, HomomorphismError>>,
    ) -> Result<Tree, HomomorphismError> {
        let mapped_children = children.into_iter().collect::<Result<Vec<_>, _>>()?;
        let rhs = self
            .hom
            .get(src)
            .ok_or(HomomorphismError::UnmappedSymbol { symbol: src })?;
        self.hom
            .instantiate(rhs, &mapped_children, self.output_arena)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(i: u32) -> Symbol {
        Symbol(i)
    }

    fn var(arena: &mut TreeArena<HomLabel>, i: usize) -> Tree {
        arena.add_node(HomLabel::Var(i), vec![])
    }

    fn node(arena: &mut TreeArena<HomLabel>, symbol: Symbol, children: Vec<Tree>) -> Tree {
        arena.add_node(HomLabel::Symbol(symbol), children)
    }

    #[test]
    fn deduplicates_identical_terms() {
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let term = node(&mut arena, sym(10), vec![v0, v1]);
        let same_v0 = var(&mut arena, 0);
        let same_v1 = var(&mut arena, 1);
        let same = node(&mut arena, sym(10), vec![same_v0, same_v1]);

        let mut h = Homomorphism::new(&arena);
        h.add(sym(0), 2, term).unwrap();
        h.add(sym(1), 2, same).unwrap();

        assert_eq!(h.term_id(sym(0)), h.term_id(sym(1)));
        let labels = h.label_set(h.term_id(sym(0)).unwrap());
        assert!(labels.contains(&sym(0)));
        assert!(labels.contains(&sym(1)));
        assert_eq!(h.num_terms(), 1);
    }

    #[test]
    fn rejects_invalid_nondeleting_terms() {
        let mut arena = TreeArena::new();
        let missing_v0 = var(&mut arena, 0);
        let missing = node(&mut arena, sym(10), vec![missing_v0]);
        let duplicate_v0a = var(&mut arena, 0);
        let duplicate_v0b = var(&mut arena, 0);
        let duplicate = node(&mut arena, sym(10), vec![duplicate_v0a, duplicate_v0b]);
        let out_of_range_v0 = var(&mut arena, 0);
        let out_of_range_v2 = var(&mut arena, 2);
        let out_of_range = node(&mut arena, sym(10), vec![out_of_range_v0, out_of_range_v2]);

        let mut h = Homomorphism::new(&arena);
        assert!(matches!(
            h.add(sym(0), 2, missing),
            Err(HomomorphismError::MissingVariable { variable: 1, .. })
        ));
        assert!(matches!(
            h.add(sym(1), 2, duplicate),
            Err(HomomorphismError::DuplicateVariable { variable: 0, .. })
        ));
        assert!(matches!(
            h.add(sym(2), 2, out_of_range),
            Err(HomomorphismError::OutOfRangeVariable { variable: 2, .. })
        ));
    }

    #[test]
    fn rejects_conflicting_reregistration() {
        let mut arena = TreeArena::new();
        let first_v0 = var(&mut arena, 0);
        let first = node(&mut arena, sym(10), vec![first_v0]);
        let second_v0 = var(&mut arena, 0);
        let second = node(&mut arena, sym(11), vec![second_v0]);

        let mut h = Homomorphism::new(&arena);
        h.add(sym(0), 1, first).unwrap();
        assert!(matches!(
            h.add(sym(0), 2, first),
            Err(HomomorphismError::ArityMismatch { .. })
        ));
        assert!(matches!(
            h.add(sym(0), 1, second),
            Err(HomomorphismError::ConflictingSourceTerm { .. })
        ));
    }

    #[test]
    fn apply_maps_nullary_and_nested_terms() {
        let mut hom_arena = TreeArena::new();
        let leaf_rhs = node(&mut hom_arena, sym(20), vec![]);
        let concat_v0 = var(&mut hom_arena, 0);
        let concat_v1 = var(&mut hom_arena, 1);
        let concat_rhs = node(&mut hom_arena, sym(21), vec![concat_v0, concat_v1]);
        let wrap_rhs = node(&mut hom_arena, sym(22), vec![concat_rhs]);

        let mut hom = Homomorphism::new(&hom_arena);
        hom.add(sym(0), 0, leaf_rhs).unwrap();
        hom.add(sym(1), 2, wrap_rhs).unwrap();

        let mut input = TreeArena::new();
        let l = input.add_node(sym(0), vec![]);
        let r = input.add_node(sym(0), vec![]);
        let root = input.add_node(sym(1), vec![l, r]);

        let mut output = TreeArena::new();
        let out_root = hom.apply(&input, root, &mut output).unwrap();
        assert_eq!(*output.get_label(out_root), sym(22));
        let concat = output.get_children(out_root)[0];
        assert_eq!(*output.get_label(concat), sym(21));
        let leaves = output.get_children(concat);
        assert_eq!(*output.get_label(leaves[0]), sym(20));
        assert_eq!(*output.get_label(leaves[1]), sym(20));
    }

    #[test]
    fn apply_reports_unmapped_symbols() {
        let hom_arena = TreeArena::new();
        let hom = Homomorphism::new(&hom_arena);
        let mut input = TreeArena::new();
        let root = input.add_node(sym(99), vec![]);
        let mut output = TreeArena::new();
        assert_eq!(
            hom.apply(&input, root, &mut output),
            Err(HomomorphismError::UnmappedSymbol { symbol: sym(99) })
        );
    }
}
