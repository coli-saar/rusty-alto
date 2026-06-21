//! TAG derived-tree algebra and Engelfriet-YIELD decomposition automata.
//!
//! Ordinary symbols construct ranked trees. `@` substitutes a tree into every
//! `*` hole of a host tree. Decomposition states identify either an exact
//! subtree or a context with one distinguished descendant hole.

use super::{Algebra, TreeValue};
use crate::{
    BottomUpTa, CondensedTa, FxHashMap, OutputCodec, Signature, StateUniverse, Symbol, SymbolSet,
    TopDownTa, TreeVisualizationCodec, VisualRepresentation,
};
use packed_term_arena::{
    parser::{TreeParseError, parse_tree},
    tree::{Tree, TreeArena},
};
use std::{cell::RefCell, fmt};

/// Reserved binary tree-substitution operation.
pub const TAG_SUBSTITUTE: &str = "@";
/// Reserved nullary substitution-site symbol.
pub const TAG_HOLE: &str = "*";

fn strip_arity(label: &str) -> &str {
    if let Some(index) = label.rfind('_')
        && index > 0
        && index + 1 < label.len()
        && label[index + 1..].bytes().all(|byte| byte.is_ascii_digit())
    {
        return &label[..index];
    }
    label
}

fn copy_subtree(src: &TreeArena<String>, node: Tree, dst: &mut TreeArena<String>) -> Tree {
    let children = src
        .get_children(node)
        .iter()
        .map(|&child| copy_subtree(src, child, dst))
        .collect();
    dst.add_node(src.get_label(node).clone(), children)
}

fn substitute_all(
    arena: &mut TreeArena<String>,
    host: Tree,
    replacement: Tree,
    hole_label: &str,
) -> Tree {
    if arena.get_label(host) == hole_label {
        return replacement;
    }
    let label = arena.get_label(host).clone();
    let children = arena.get_children(host).to_vec();
    let children = children
        .into_iter()
        .map(|child| substitute_all(arena, child, replacement, hole_label))
        .collect();
    arena.add_node(label, children)
}

/// Alto-compatible TAG derived-tree algebra.
#[derive(Debug)]
pub struct TagTreeAlgebra {
    signature: Signature,
    substitute: Symbol,
    hole: Symbol,
    with_arities: bool,
    scratch: RefCell<TreeArena<String>>,
    display_codec: TreeVisualizationCodec,
}

impl TagTreeAlgebra {
    /// Construct the plain TAG tree algebra.
    pub fn tree(signature: Signature) -> Self {
        Self::new(signature, false)
    }

    /// Construct the arity-annotated TAG tree algebra.
    ///
    /// Labels such as `NP_2` are stripped to `NP` in public tree values.
    pub fn with_arities(signature: Signature) -> Self {
        Self::new(signature, true)
    }

    fn new(mut signature: Signature, with_arities: bool) -> Self {
        let substitute = signature.intern(TAG_SUBSTITUTE.to_owned(), 2).unwrap();
        let hole = signature.intern(TAG_HOLE.to_owned(), 0).unwrap();
        Self {
            signature,
            substitute,
            hole,
            with_arities,
            scratch: RefCell::new(TreeArena::new()),
            display_codec: TreeVisualizationCodec,
        }
    }

    /// Return the symbol ID of the reserved `@/2` operation.
    pub fn substitute_symbol(&self) -> Symbol {
        self.substitute
    }

    /// Return the symbol ID of the reserved `*/0` hole.
    pub fn hole_symbol(&self) -> Symbol {
        self.hole
    }

    /// Build a lazy decomposition automaton for a parsed tree value.
    ///
    /// `value` must belong to this algebra's scratch arena, as values returned
    /// by [`Algebra::parse_object`] do.
    pub fn decompose(&self, value: Tree) -> TagTreeDecompositionAutomaton {
        self.decompose_with_rank_mode(value, false)
    }

    /// Build a decomposition whose ordinary labels are matched by name even when the
    /// exposed (binarized) signature gives them unary rank.
    pub fn decompose_binarized(&self, value: Tree) -> TagTreeDecompositionAutomaton {
        self.decompose_with_rank_mode(value, true)
    }

    fn decompose_with_rank_mode(
        &self,
        value: Tree,
        permissive_rank: bool,
    ) -> TagTreeDecompositionAutomaton {
        let mut arena = TreeArena::new();
        let root = copy_subtree(&self.scratch.borrow(), value, &mut arena);
        TagTreeDecompositionAutomaton::new(
            self.signature.clone(),
            self.substitute,
            self.hole,
            self.with_arities,
            permissive_rank,
            arena,
            root,
        )
    }

    fn operation_label(&self, symbol: Symbol) -> String {
        strip_arity(self.signature.resolve(symbol)).to_owned()
    }
}

impl Algebra for TagTreeAlgebra {
    type InternalValue = Tree;
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
        if symbol == self.substitute {
            let [host, replacement] = children else {
                return None;
            };
            return Some(substitute_all(
                &mut self.scratch.borrow_mut(),
                *host,
                *replacement,
                TAG_HOLE,
            ));
        }

        let label = self.operation_label(symbol);
        Some(self.scratch.borrow_mut().add_node(label, children.to_vec()))
    }

    fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError> {
        parse_tree(&mut self.scratch.borrow_mut(), input)
    }

    fn to_external(&self, value: &Self::InternalValue) -> Self::Value {
        let mut arena = TreeArena::new();
        let root = copy_subtree(&self.scratch.borrow(), *value, &mut arena);
        *self.scratch.borrow_mut() = TreeArena::new();
        TreeValue::new(arena, root)
    }

    fn visualize(&self, value: &Self::Value) -> VisualRepresentation {
        self.display_codec.encode(value)
    }
}

/// A subtree or a one-hole tree context in the fixed derived tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TagTreeContext {
    /// Root-node index in the fixed target tree.
    pub top: usize,
    /// Distinguished descendant hole, or `None` for a complete subtree.
    pub bottom: Option<usize>,
}

impl TagTreeContext {
    fn tree(top: usize) -> Self {
        Self { top, bottom: None }
    }

    fn context(top: usize, bottom: usize) -> Self {
        Self {
            top,
            bottom: Some(bottom),
        }
    }
}

#[derive(Clone, Debug)]
struct TargetNode {
    label: String,
    children: Vec<usize>,
    parent: Option<(usize, usize)>,
}

/// Lazy Engelfriet-YIELD decomposition automaton for a fixed derived tree.
#[derive(Clone, Debug)]
pub struct TagTreeDecompositionAutomaton {
    signature: Signature,
    substitute: Symbol,
    hole: Symbol,
    nodes: Vec<TargetNode>,
    root: usize,
    symbols_by_shape: FxHashMap<(String, usize), Vec<Symbol>>,
}

impl TagTreeDecompositionAutomaton {
    fn new(
        signature: Signature,
        substitute: Symbol,
        hole: Symbol,
        with_arities: bool,
        permissive_rank: bool,
        arena: TreeArena<String>,
        root: Tree,
    ) -> Self {
        fn copy(
            arena: &TreeArena<String>,
            node: Tree,
            parent: Option<(usize, usize)>,
            nodes: &mut Vec<TargetNode>,
        ) -> usize {
            let index = nodes.len();
            nodes.push(TargetNode {
                label: arena.get_label(node).clone(),
                children: Vec::new(),
                parent,
            });
            let children = arena.get_children(node).to_vec();
            for (position, child) in children.into_iter().enumerate() {
                let child_index = copy(arena, child, Some((index, position)), nodes);
                nodes[index].children.push(child_index);
            }
            index
        }

        let mut nodes = Vec::new();
        let root = copy(&arena, root, None, &mut nodes);
        let mut symbols_by_shape: FxHashMap<(String, usize), Vec<Symbol>> = FxHashMap::default();
        for raw in 0..signature.len() {
            let symbol = Symbol(raw as u32);
            if symbol == substitute || symbol == hole {
                continue;
            }
            let arity = signature.arity(symbol);
            let name = signature.resolve(symbol);
            let label = if with_arities
                || name.rsplit_once('_').is_some_and(|(_, suffix)| {
                    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                }) {
                strip_arity(name)
            } else {
                name
            };
            if permissive_rank && arity > 0 {
                for target_arity in 0..=nodes
                    .iter()
                    .map(|node| node.children.len())
                    .max()
                    .unwrap_or(0)
                {
                    symbols_by_shape
                        .entry((label.to_owned(), target_arity))
                        .or_default()
                        .push(symbol);
                }
            } else {
                symbols_by_shape
                    .entry((label.to_owned(), arity))
                    .or_default()
                    .push(symbol);
            }
        }

        Self {
            signature,
            substitute,
            hole,
            nodes,
            root,
            symbols_by_shape,
        }
    }

    /// Return the accepting context representing the complete target tree.
    pub fn root_context(&self) -> TagTreeContext {
        TagTreeContext::tree(self.root)
    }

    /// Return the target operation signature.
    pub fn signature(&self) -> &Signature {
        &self.signature
    }

    fn is_descendant(&self, ancestor: usize, mut node: usize) -> bool {
        loop {
            if node == ancestor {
                return true;
            }
            let Some((parent, _)) = self.nodes[node].parent else {
                return false;
            };
            node = parent;
        }
    }

    fn direct_child_toward(&self, ancestor: usize, mut descendant: usize) -> Option<usize> {
        if ancestor == descendant {
            return None;
        }
        loop {
            let (parent, position) = self.nodes[descendant].parent?;
            if parent == ancestor {
                return Some(position);
            }
            descendant = parent;
        }
    }

    fn symbols_for_node(&self, node: usize) -> &[Symbol] {
        let target = &self.nodes[node];
        self.symbols_by_shape
            .get(&(target.label.clone(), target.children.len()))
            .map_or(&[], Vec::as_slice)
    }
}

impl BottomUpTa for TagTreeDecompositionAutomaton {
    type State = TagTreeContext;

    fn step(
        &self,
        symbol: Symbol,
        children: &[TagTreeContext],
        out: &mut dyn FnMut(TagTreeContext),
    ) {
        if symbol == self.hole {
            if children.is_empty() {
                for node in 0..self.nodes.len() {
                    out(TagTreeContext::context(node, node));
                }
            }
            return;
        }

        if symbol == self.substitute {
            if let [host, replacement] = children
                && host.bottom == Some(replacement.top)
            {
                out(TagTreeContext {
                    top: host.top,
                    bottom: replacement.bottom,
                });
            }
            return;
        }

        if children.is_empty() {
            for node in 0..self.nodes.len() {
                if self.nodes[node].children.is_empty()
                    && self.symbols_for_node(node).contains(&symbol)
                {
                    out(TagTreeContext::tree(node));
                }
            }
            return;
        }

        let Some((parent, first_position)) = self.nodes[children[0].top].parent else {
            return;
        };
        if first_position != 0
            || self.nodes[parent].children.len() != children.len()
            || !self.symbols_for_node(parent).contains(&symbol)
        {
            return;
        }
        let mut bottom = None;
        for (position, child) in children.iter().enumerate() {
            if self.nodes[parent].children[position] != child.top {
                return;
            }
            if let Some(hole) = child.bottom {
                if bottom.replace(hole).is_some() {
                    return;
                }
            }
        }
        out(TagTreeContext {
            top: parent,
            bottom,
        });
    }

    fn is_accepting(&self, state: &TagTreeContext) -> bool {
        *state == self.root_context()
    }
}

impl StateUniverse for TagTreeDecompositionAutomaton {
    fn all_states(&self, out: &mut dyn FnMut(TagTreeContext)) {
        for top in 0..self.nodes.len() {
            out(TagTreeContext::tree(top));
            for bottom in 0..self.nodes.len() {
                if self.is_descendant(top, bottom) {
                    out(TagTreeContext::context(top, bottom));
                }
            }
        }
    }
}

impl TopDownTa for TagTreeDecompositionAutomaton {
    fn step_topdown(
        &self,
        parent: &TagTreeContext,
        out: &mut dyn FnMut(Symbol, &[TagTreeContext]),
    ) {
        if parent.top >= self.nodes.len()
            || parent
                .bottom
                .is_some_and(|bottom| !self.is_descendant(parent.top, bottom))
        {
            return;
        }

        if parent.bottom == Some(parent.top) {
            out(self.hole, &[]);
        }

        match parent.bottom {
            None => {
                for bottom in 0..self.nodes.len() {
                    if self.is_descendant(parent.top, bottom) {
                        let children = [
                            TagTreeContext::context(parent.top, bottom),
                            TagTreeContext::tree(bottom),
                        ];
                        out(self.substitute, &children);
                    }
                }
            }
            Some(bottom) => {
                let mut cut = bottom;
                loop {
                    let children = [
                        TagTreeContext::context(parent.top, cut),
                        TagTreeContext::context(cut, bottom),
                    ];
                    out(self.substitute, &children);
                    if cut == parent.top {
                        break;
                    }
                    cut = self.nodes[cut]
                        .parent
                        .expect("descendant other than root has a parent")
                        .0;
                }
            }
        }

        let node = &self.nodes[parent.top];
        let mut children: Vec<TagTreeContext> = node
            .children
            .iter()
            .copied()
            .map(TagTreeContext::tree)
            .collect();
        if let Some(bottom) = parent.bottom {
            let Some(position) = self.direct_child_toward(parent.top, bottom) else {
                return;
            };
            children[position] = TagTreeContext::context(node.children[position], bottom);
        }
        for &symbol in self.symbols_for_node(parent.top) {
            out(symbol, &children);
        }
    }

    fn initial_states(&self, out: &mut dyn FnMut(TagTreeContext)) {
        out(self.root_context());
    }
}

impl CondensedTa for TagTreeDecompositionAutomaton {
    fn condensed_rules(&self, out: &mut dyn FnMut(&[TagTreeContext], &SymbolSet, TagTreeContext)) {
        self.all_states(&mut |state| {
            self.step_topdown(&state, &mut |symbol, children| {
                let mut symbols = SymbolSet::new();
                symbols.insert(symbol);
                out(children, &symbols, state);
            });
        });
    }

    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, TagTreeContext)) {
        let mut hole = SymbolSet::new();
        hole.insert(self.hole);
        for node in 0..self.nodes.len() {
            out(&hole, TagTreeContext::context(node, node));
            if self.nodes[node].children.is_empty() {
                for &symbol in self.symbols_for_node(node) {
                    let mut symbols = SymbolSet::new();
                    symbols.insert(symbol);
                    out(&symbols, TagTreeContext::tree(node));
                }
            }
        }
    }

    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &TagTreeContext,
        out: &mut dyn FnMut(&[TagTreeContext], &SymbolSet, TagTreeContext),
    ) {
        self.all_states(&mut |parent| {
            self.step_topdown(&parent, &mut |symbol, children| {
                if children.get(position) == Some(state) {
                    let mut symbols = SymbolSet::new();
                    symbols.insert(symbol);
                    out(children, &symbols, parent);
                }
            });
        });
    }
}

impl fmt::Display for TagTreeContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.bottom {
            Some(bottom) => write!(f, "{}/{}", self.top, bottom),
            None => write!(f, "{}/-", self.top),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct BinarizedRule {
    parent: TagTreeContext,
    symbol: Symbol,
    children: Box<[TagTreeContext]>,
}

/// State of a binarized TAG-tree decomposition automaton.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinarizedTagTreeState {
    /// A state inherited from the unbinarized decomposition.
    Inner(TagTreeContext),
    /// A contiguous child interval of one higher-arity rule.
    Sequence {
        /// Index of the unbinarized rule.
        rule: usize,
        /// Inclusive first child position.
        start: usize,
        /// Exclusive final child position.
        end: usize,
    },
}

impl fmt::Display for BinarizedTagTreeState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inner(state) => write!(f, "{state}"),
            Self::Sequence { rule, start, end } => write!(f, "seq{rule}[{start},{end})"),
        }
    }
}

/// Lazy binarization of a TAG-tree decomposition automaton.
#[derive(Clone, Debug)]
pub struct BinarizedTagTreeDecompositionAutomaton {
    inner: TagTreeDecompositionAutomaton,
    append: Symbol,
    rules: Vec<BinarizedRule>,
}

impl BinarizedTagTreeDecompositionAutomaton {
    /// Binarize higher-arity rules using the binary `append` operation.
    pub fn new(inner: TagTreeDecompositionAutomaton, append: Symbol) -> Self {
        let mut rules = Vec::new();
        inner.all_states(&mut |parent| {
            inner.step_topdown(&parent, &mut |symbol, children| {
                if children.len() > 2 {
                    let rule = BinarizedRule {
                        parent,
                        symbol,
                        children: children.into(),
                    };
                    if !rules.contains(&rule) {
                        rules.push(rule);
                    }
                }
            });
        });
        Self {
            inner,
            append,
            rules,
        }
    }

    fn segment_state(&self, rule: usize, start: usize, end: usize) -> BinarizedTagTreeState {
        if end == start + 1 {
            BinarizedTagTreeState::Inner(self.rules[rule].children[start])
        } else {
            BinarizedTagTreeState::Sequence { rule, start, end }
        }
    }
}

impl BottomUpTa for BinarizedTagTreeDecompositionAutomaton {
    type State = BinarizedTagTreeState;

    fn step(&self, symbol: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        if symbol == self.append {
            let [left, right] = children else {
                return;
            };
            for (rule_index, rule) in self.rules.iter().enumerate() {
                for split in 1..rule.children.len() {
                    for start in 0..split {
                        for end in split + 1..=rule.children.len() {
                            if *left == self.segment_state(rule_index, start, split)
                                && *right == self.segment_state(rule_index, split, end)
                            {
                                out(BinarizedTagTreeState::Sequence {
                                    rule: rule_index,
                                    start,
                                    end,
                                });
                            }
                        }
                    }
                }
            }
            return;
        }

        if let [BinarizedTagTreeState::Sequence { rule, start, end }] = children {
            let rule_data = &self.rules[*rule];
            if symbol == rule_data.symbol && *start == 0 && *end == rule_data.children.len() {
                out(BinarizedTagTreeState::Inner(rule_data.parent));
            }
            return;
        }

        let Some(inner_children) = children
            .iter()
            .map(|state| match state {
                BinarizedTagTreeState::Inner(inner) => Some(*inner),
                BinarizedTagTreeState::Sequence { .. } => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            return;
        };
        self.inner.step(symbol, &inner_children, &mut |parent| {
            let is_high_rule = self.rules.iter().any(|rule| {
                rule.parent == parent
                    && rule.symbol == symbol
                    && rule.children.as_ref() == inner_children.as_slice()
            });
            if !is_high_rule {
                out(BinarizedTagTreeState::Inner(parent));
            }
        });
    }

    fn is_accepting(&self, state: &Self::State) -> bool {
        matches!(state, BinarizedTagTreeState::Inner(inner) if self.inner.is_accepting(inner))
    }
}

impl StateUniverse for BinarizedTagTreeDecompositionAutomaton {
    fn all_states(&self, out: &mut dyn FnMut(Self::State)) {
        self.inner
            .all_states(&mut |state| out(BinarizedTagTreeState::Inner(state)));
        for (rule, data) in self.rules.iter().enumerate() {
            for start in 0..data.children.len() {
                for end in start + 2..=data.children.len() {
                    out(BinarizedTagTreeState::Sequence { rule, start, end });
                }
            }
        }
    }
}

impl TopDownTa for BinarizedTagTreeDecompositionAutomaton {
    fn step_topdown(&self, parent: &Self::State, out: &mut dyn FnMut(Symbol, &[Self::State])) {
        match *parent {
            BinarizedTagTreeState::Inner(inner_parent) => {
                self.inner
                    .step_topdown(&inner_parent, &mut |symbol, children| {
                        if children.len() <= 2 {
                            let children: Vec<_> = children
                                .iter()
                                .copied()
                                .map(BinarizedTagTreeState::Inner)
                                .collect();
                            out(symbol, &children);
                        } else {
                            for (rule, data) in self.rules.iter().enumerate() {
                                if data.parent == inner_parent
                                    && data.symbol == symbol
                                    && data.children.as_ref() == children
                                {
                                    let child = [BinarizedTagTreeState::Sequence {
                                        rule,
                                        start: 0,
                                        end: children.len(),
                                    }];
                                    out(symbol, &child);
                                }
                            }
                        }
                    });
            }
            BinarizedTagTreeState::Sequence { rule, start, end } => {
                for split in start + 1..end {
                    let children = [
                        self.segment_state(rule, start, split),
                        self.segment_state(rule, split, end),
                    ];
                    out(self.append, &children);
                }
            }
        }
    }

    fn initial_states(&self, out: &mut dyn FnMut(Self::State)) {
        self.inner
            .initial_states(&mut |state| out(BinarizedTagTreeState::Inner(state)));
    }
}

impl CondensedTa for BinarizedTagTreeDecompositionAutomaton {
    fn condensed_rules(&self, out: &mut dyn FnMut(&[Self::State], &SymbolSet, Self::State)) {
        self.all_states(&mut |state| {
            self.step_topdown(&state, &mut |symbol, children| {
                let mut symbols = SymbolSet::new();
                symbols.insert(symbol);
                out(children, &symbols, state.clone());
            });
        });
    }

    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, Self::State)) {
        self.inner.condensed_nullary_rules(&mut |symbols, state| {
            out(symbols, BinarizedTagTreeState::Inner(state));
        });
    }

    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &Self::State,
        out: &mut dyn FnMut(&[Self::State], &SymbolSet, Self::State),
    ) {
        self.all_states(&mut |parent| {
            self.step_topdown(&parent, &mut |symbol, children| {
                if children.get(position) == Some(state) {
                    let mut symbols = SymbolSet::new();
                    symbols.insert(symbol);
                    out(children, &symbols, parent.clone());
                }
            });
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn signature(entries: &[(&str, usize)]) -> Signature {
        let mut signature = Signature::new();
        for &(name, arity) in entries {
            signature.intern(name.to_owned(), arity).unwrap();
        }
        signature
    }

    #[test]
    fn substitutes_every_hole() {
        let signature = signature(&[("f", 2), ("a", 0), ("b", 0)]);
        let f = signature.get("f").unwrap();
        let a = signature.get("a").unwrap();
        let b = signature.get("b").unwrap();
        let algebra = TagTreeAlgebra::tree(signature);
        let hole1 = algebra.evaluate(algebra.hole_symbol(), &[]).unwrap();
        let hole2 = algebra.evaluate(algebra.hole_symbol(), &[]).unwrap();
        let host = algebra.evaluate(f, &[hole1, hole2]).unwrap();
        let replacement = algebra.evaluate(a, &[]).unwrap();
        let result = algebra
            .evaluate(algebra.substitute_symbol(), &[host, replacement])
            .unwrap();
        assert_eq!(algebra.to_external(&result).to_string(), "f(a, a)");
        assert!(algebra.evaluate(b, &[]).is_some());
    }

    #[test]
    fn decomposition_accepts_target_tree() {
        let signature = signature(&[("f", 1), ("a", 0)]);
        let f = signature.get("f").unwrap();
        let a = signature.get("a").unwrap();
        let mut algebra = TagTreeAlgebra::tree(signature);
        let value = algebra.parse_object("f(a)").unwrap();
        let decomp = algebra.decompose(value);
        let leaf = {
            let mut result = Vec::new();
            decomp.step(a, &[], &mut |state| result.push(state));
            result[0]
        };
        let root = {
            let mut result = Vec::new();
            decomp.step(f, &[leaf], &mut |state| result.push(state));
            result[0]
        };
        assert!(decomp.is_accepting(&root));
    }

    // Ported from Alto's TagAlgebrasTest.testNessonShieberPrePos.
    #[test]
    fn alto_nesson_shieber_substitution_example() {
        let signature = signature(&[
            ("s", 2),
            ("np", 1),
            ("john", 0),
            ("mary", 0),
            ("vp", 2),
            ("adv", 1),
            ("apparently", 0),
            ("v", 1),
            ("likes", 0),
        ]);
        let s = signature.get("s").unwrap();
        let np = signature.get("np").unwrap();
        let john = signature.get("john").unwrap();
        let mary = signature.get("mary").unwrap();
        let vp = signature.get("vp").unwrap();
        let adv = signature.get("adv").unwrap();
        let apparently = signature.get("apparently").unwrap();
        let v = signature.get("v").unwrap();
        let likes = signature.get("likes").unwrap();
        let algebra = TagTreeAlgebra::tree(signature);

        let john = algebra.evaluate(john, &[]).unwrap();
        let john = algebra.evaluate(np, &[john]).unwrap();
        let mary = algebra.evaluate(mary, &[]).unwrap();
        let mary = algebra.evaluate(np, &[mary]).unwrap();
        let likes = algebra.evaluate(likes, &[]).unwrap();
        let likes = algebra.evaluate(v, &[likes]).unwrap();
        let inner_vp = algebra.evaluate(vp, &[likes, mary]).unwrap();
        let apparently = algebra.evaluate(apparently, &[]).unwrap();
        let apparently = algebra.evaluate(adv, &[apparently]).unwrap();
        let hole = algebra.evaluate(algebra.hole_symbol(), &[]).unwrap();
        let context = algebra.evaluate(vp, &[apparently, hole]).unwrap();
        let derived_vp = algebra
            .evaluate(algebra.substitute_symbol(), &[context, inner_vp])
            .unwrap();
        let result = algebra.evaluate(s, &[john, derived_vp]).unwrap();

        assert_eq!(
            algebra.to_external(&result).to_string(),
            "s(np(john), vp(adv(apparently), vp(v(likes), np(mary))))"
        );
    }
}
