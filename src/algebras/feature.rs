//! Feature structures and the algebra used by Tulipac TAG grammars.
//!
//! Values are immutable graphs. Repeated variables in a parsed literal denote
//! reentrant nodes; unification preserves this sharing. The algebra implements
//! Alto's `unify`, `proj_*`, `emb_*`, and `emba_*` operations.

use super::Algebra;
use crate::{BottomUpTa, FxHashMap, Signature, Symbol};
use std::{
    collections::{BTreeMap, HashMap},
    fmt,
};

/// Binary feature-structure unification operation.
pub const FS_UNIFY: &str = "unify";
/// Prefix for unary projection operations such as `proj_root`.
pub const FS_PROJECT_PREFIX: &str = "proj_";
/// Prefix for unary embedding operations such as `emb_n1`.
pub const FS_EMBED_PREFIX: &str = "emb_";
/// Prefix for auxiliary-tree embedding operations such as `emba_n1t_n1b`.
pub const FS_EMBED_AUX_PREFIX: &str = "emba_";

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    Variable,
    Atom(String),
    Map(Vec<(String, usize)>),
}

/// Immutable canonical feature structure with explicit reentrancies.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FeatureStructure {
    nodes: Vec<Node>,
}

impl FeatureStructure {
    /// Construct an empty attribute-value matrix.
    pub fn empty() -> Self {
        Self {
            nodes: vec![Node::Map(Vec::new())],
        }
    }

    /// Parse Alto feature-structure syntax.
    ///
    /// Attribute-value matrices use `[attribute: value]`; `#name` introduces
    /// or refers to a reentrant variable.
    pub fn parse(input: &str) -> Result<Self, FeatureStructureParseError> {
        Parser::new(input).parse()
    }

    /// Compute non-destructive unification, or return `None` on a clash.
    pub fn unify(&self, other: &Self) -> Option<Self> {
        let mut graph = Graph::default();
        let left = graph.append(self);
        let right = graph.append(other);
        graph.unify(left, right)?;
        Some(graph.freeze(left))
    }

    /// Return the value stored below a root attribute.
    pub fn project(&self, attribute: &str) -> Option<Self> {
        let Node::Map(attributes) = &self.nodes[0] else {
            return None;
        };
        let child = attributes
            .binary_search_by(|(candidate, _)| candidate.as_str().cmp(attribute))
            .ok()
            .map(|index| attributes[index].1)?;
        Some(self.subgraph(child))
    }

    /// Wrap this value in a new one-attribute feature structure.
    pub fn embed(&self, attribute: &str) -> Self {
        self.with_new_root(vec![(attribute.to_owned(), 1)])
    }

    /// Embed the source `root` and `foot` values under two new attributes.
    pub fn embed_aux(&self, top: &str, bottom: &str) -> Option<Self> {
        let root = self.attribute("root")? + 1;
        let foot = self.attribute("foot")? + 1;
        let mut attributes = vec![(top.to_owned(), root), (bottom.to_owned(), foot)];
        attributes.sort_by(|left, right| left.0.cmp(&right.0));
        Some(self.with_new_root(attributes))
    }

    fn attribute(&self, name: &str) -> Option<usize> {
        let Node::Map(attributes) = &self.nodes[0] else {
            return None;
        };
        attributes
            .binary_search_by(|(candidate, _)| candidate.as_str().cmp(name))
            .ok()
            .map(|index| attributes[index].1)
    }

    fn with_new_root(&self, attributes: Vec<(String, usize)>) -> Self {
        let mut nodes = vec![Node::Map(attributes)];
        nodes.extend(self.nodes.iter().map(|node| shift(node, 1)));
        Self { nodes }
    }

    fn subgraph(&self, root: usize) -> Self {
        fn copy(
            source: &FeatureStructure,
            node: usize,
            remap: &mut HashMap<usize, usize>,
            target: &mut Vec<Node>,
        ) -> usize {
            if let Some(&mapped) = remap.get(&node) {
                return mapped;
            }
            let mapped = target.len();
            remap.insert(node, mapped);
            target.push(Node::Variable);
            target[mapped] = match &source.nodes[node] {
                Node::Variable => Node::Variable,
                Node::Atom(atom) => Node::Atom(atom.clone()),
                Node::Map(attributes) => Node::Map(
                    attributes
                        .iter()
                        .map(|(attribute, child)| {
                            (attribute.clone(), copy(source, *child, remap, target))
                        })
                        .collect(),
                ),
            };
            mapped
        }
        let mut nodes = Vec::new();
        copy(self, root, &mut HashMap::new(), &mut nodes);
        Self { nodes }
    }
}

fn shift(node: &Node, offset: usize) -> Node {
    match node {
        Node::Variable => Node::Variable,
        Node::Atom(atom) => Node::Atom(atom.clone()),
        Node::Map(attributes) => Node::Map(
            attributes
                .iter()
                .map(|(attribute, child)| (attribute.clone(), child + offset))
                .collect(),
        ),
    }
}

impl fmt::Display for FeatureStructure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write_node(
            value: &FeatureStructure,
            node: usize,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result {
            match &value.nodes[node] {
                Node::Variable => f.write_str("[]"),
                Node::Atom(atom) => f.write_str(atom),
                Node::Map(attributes) => {
                    f.write_str("[")?;
                    for (index, (attribute, child)) in attributes.iter().enumerate() {
                        if index > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{attribute}: ")?;
                        write_node(value, *child, f)?;
                    }
                    f.write_str("]")
                }
            }
        }
        write_node(self, 0, f)
    }
}

#[derive(Clone, Debug)]
enum WorkNode {
    Variable,
    Atom(String),
    Map(BTreeMap<String, usize>),
}

#[derive(Default)]
struct Graph {
    nodes: Vec<WorkNode>,
    parents: Vec<usize>,
}

impl Graph {
    fn add(&mut self, node: WorkNode) -> usize {
        let id = self.nodes.len();
        self.nodes.push(node);
        self.parents.push(id);
        id
    }

    fn append(&mut self, value: &FeatureStructure) -> usize {
        let offset = self.nodes.len();
        for node in &value.nodes {
            self.add(match node {
                Node::Variable => WorkNode::Variable,
                Node::Atom(atom) => WorkNode::Atom(atom.clone()),
                Node::Map(attributes) => WorkNode::Map(
                    attributes
                        .iter()
                        .map(|(attribute, child)| (attribute.clone(), child + offset))
                        .collect(),
                ),
            });
        }
        offset
    }

    fn find(&mut self, node: usize) -> usize {
        if self.parents[node] == node {
            node
        } else {
            let root = self.find(self.parents[node]);
            self.parents[node] = root;
            root
        }
    }

    fn unify(&mut self, left: usize, right: usize) -> Option<usize> {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return Some(left);
        }
        match (self.nodes[left].clone(), self.nodes[right].clone()) {
            (WorkNode::Variable, _) => {
                self.parents[left] = right;
                Some(right)
            }
            (_, WorkNode::Variable) => {
                self.parents[right] = left;
                Some(left)
            }
            (WorkNode::Atom(left_atom), WorkNode::Atom(right_atom)) => {
                if left_atom != right_atom {
                    None
                } else {
                    self.parents[right] = left;
                    Some(left)
                }
            }
            (WorkNode::Map(mut left_map), WorkNode::Map(right_map)) => {
                self.parents[right] = left;
                for (attribute, right_child) in right_map {
                    if let Some(&left_child) = left_map.get(&attribute) {
                        let child = self.unify(left_child, right_child)?;
                        left_map.insert(attribute, child);
                    } else {
                        left_map.insert(attribute, right_child);
                    }
                }
                self.nodes[left] = WorkNode::Map(left_map);
                Some(left)
            }
            _ => None,
        }
    }

    fn freeze(mut self, root: usize) -> FeatureStructure {
        fn copy(
            graph: &mut Graph,
            node: usize,
            remap: &mut HashMap<usize, usize>,
            target: &mut Vec<Node>,
        ) -> usize {
            let node = graph.find(node);
            if let Some(&mapped) = remap.get(&node) {
                return mapped;
            }
            let mapped = target.len();
            remap.insert(node, mapped);
            target.push(Node::Variable);
            let work = graph.nodes[node].clone();
            target[mapped] = match work {
                WorkNode::Variable => Node::Variable,
                WorkNode::Atom(atom) => Node::Atom(atom),
                WorkNode::Map(attributes) => Node::Map(
                    attributes
                        .into_iter()
                        .map(|(attribute, child)| (attribute, copy(graph, child, remap, target)))
                        .collect(),
                ),
            };
            mapped
        }
        let mut nodes = Vec::new();
        copy(&mut self, root, &mut HashMap::new(), &mut nodes);
        FeatureStructure { nodes }
    }
}

#[derive(Clone, Debug)]
enum Operation {
    Unify,
    Project(String),
    Embed(String),
    EmbedAux(String, String),
    Literal(FeatureStructure),
    InvalidLiteral,
}

/// Alto-compatible feature-structure algebra.
///
/// Literal operation symbols parse to [`FeatureStructure`] values. Malformed
/// literals and failed unifications make evaluation undefined.
#[derive(Clone, Debug)]
pub struct FeatureStructureAlgebra {
    signature: Signature,
    operations: FxHashMap<Symbol, Operation>,
}

impl FeatureStructureAlgebra {
    /// Build an algebra by classifying every operation in `signature`.
    pub fn with_signature(signature: Signature) -> Self {
        let mut operations = FxHashMap::default();
        for raw in 0..signature.len() {
            let symbol = Symbol(raw as u32);
            let label = signature.resolve(symbol);
            let operation = if label == FS_UNIFY {
                Operation::Unify
            } else if let Some(attribute) = label.strip_prefix(FS_PROJECT_PREFIX) {
                Operation::Project(attribute.to_owned())
            } else if let Some(attributes) = label.strip_prefix(FS_EMBED_AUX_PREFIX) {
                let mut parts = attributes.splitn(2, '_');
                Operation::EmbedAux(
                    parts.next().unwrap_or_default().to_owned(),
                    parts.next().unwrap_or_default().to_owned(),
                )
            } else if let Some(attribute) = label.strip_prefix(FS_EMBED_PREFIX) {
                Operation::Embed(attribute.to_owned())
            } else {
                match FeatureStructure::parse(label) {
                    Ok(value) => Operation::Literal(value),
                    Err(_) => Operation::InvalidLiteral,
                }
            };
            operations.insert(symbol, operation);
        }
        Self {
            signature,
            operations,
        }
    }

    /// Return an automaton accepting successfully evaluated feature terms.
    pub fn filter(&self) -> FeatureStructureFilter<'_> {
        FeatureStructureFilter { algebra: self }
    }
}

impl Algebra for FeatureStructureAlgebra {
    type InternalValue = FeatureStructure;
    type Value = FeatureStructure;
    type ParseError = FeatureStructureParseError;

    fn signature(&self) -> &Signature {
        &self.signature
    }

    fn evaluate(
        &self,
        symbol: Symbol,
        children: &[Self::InternalValue],
    ) -> Option<Self::InternalValue> {
        match (self.operations.get(&symbol)?, children) {
            (Operation::Unify, [left, right]) => left.unify(right),
            (Operation::Project(attribute), [value]) => value.project(attribute),
            (Operation::Embed(attribute), [value]) => Some(value.embed(attribute)),
            (Operation::EmbedAux(top, bottom), [value]) => value.embed_aux(top, bottom),
            (Operation::Literal(value), []) => Some(value.clone()),
            (Operation::InvalidLiteral, _) => None,
            _ => None,
        }
    }

    fn parse_object(&mut self, input: &str) -> Result<Self::InternalValue, Self::ParseError> {
        FeatureStructure::parse(input)
    }

    fn to_external(&self, value: &Self::InternalValue) -> Self::Value {
        value.clone()
    }
}

/// Bottom-up evaluator that rejects failed feature-structure operations.
pub struct FeatureStructureFilter<'a> {
    algebra: &'a FeatureStructureAlgebra,
}

impl BottomUpTa for FeatureStructureFilter<'_> {
    type State = FeatureStructure;

    fn step(&self, symbol: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        if let Some(value) = self.algebra.evaluate(symbol, children) {
            out(value);
        }
    }

    fn is_accepting(&self, _state: &Self::State) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Error produced while parsing a feature-structure literal.
pub struct FeatureStructureParseError {
    offset: usize,
    message: String,
}

impl fmt::Display for FeatureStructureParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "feature-structure syntax error at byte {}: {}",
            self.offset, self.message
        )
    }
}

impl std::error::Error for FeatureStructureParseError {}

struct Parser<'a> {
    input: &'a str,
    position: usize,
    graph: Graph,
    indices: HashMap<String, usize>,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input,
            position: 0,
            graph: Graph::default(),
            indices: HashMap::new(),
        }
    }

    fn parse(mut self) -> Result<FeatureStructure, FeatureStructureParseError> {
        let root = self.value()?;
        self.ws();
        if self.position != self.input.len() {
            return self.error("trailing input");
        }
        Ok(self.graph.freeze(root))
    }

    fn value(&mut self) -> Result<usize, FeatureStructureParseError> {
        self.ws();
        if self.consume('#') {
            let name = self.word()?;
            if let Some(&existing) = self.indices.get(&name) {
                return Ok(existing);
            }
            let placeholder = self.graph.add(WorkNode::Variable);
            self.indices.insert(name, placeholder);
            self.ws();
            if self.peek() == Some('[') {
                let value = self.value()?;
                self.graph
                    .unify(placeholder, value)
                    .ok_or_else(|| self.make_error("incompatible indexed values"))?;
            }
            return Ok(placeholder);
        }
        if self.consume('[') {
            let mut attributes = BTreeMap::new();
            self.ws();
            if self.consume(']') {
                return Ok(self.graph.add(WorkNode::Map(attributes)));
            }
            loop {
                let attribute = self.word()?;
                self.ws();
                if !self.consume(':') {
                    return self.error("expected ':'");
                }
                let child = self.value()?;
                attributes.insert(attribute, child);
                self.ws();
                if self.consume(']') {
                    break;
                }
                if !self.consume(',') {
                    return self.error("expected ',' or ']'");
                }
            }
            return Ok(self.graph.add(WorkNode::Map(attributes)));
        }
        let atom = self.word()?;
        Ok(self.graph.add(WorkNode::Atom(atom)))
    }

    fn word(&mut self) -> Result<String, FeatureStructureParseError> {
        self.ws();
        let start = self.position;
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() || matches!(ch, '[' | ']' | ':' | ',') {
                break;
            }
            self.position += ch.len_utf8();
        }
        if start == self.position {
            self.error("expected value")
        } else {
            Ok(self.input[start..self.position].to_owned())
        }
    }

    fn ws(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.position += self.peek().unwrap().len_utf8();
        }
    }

    fn peek(&self) -> Option<char> {
        self.input[self.position..].chars().next()
    }

    fn consume(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.position += expected.len_utf8();
            true
        } else {
            false
        }
    }

    fn make_error(&self, message: &str) -> FeatureStructureParseError {
        FeatureStructureParseError {
            offset: self.position,
            message: message.to_owned(),
        }
    }

    fn error<T>(&self, message: &str) -> Result<T, FeatureStructureParseError> {
        Err(self.make_error(message))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unification_detects_clashes() {
        let nom = FeatureStructure::parse("[case: nom]").unwrap();
        let acc = FeatureStructure::parse("[case: acc]").unwrap();
        assert!(nom.unify(&acc).is_none());
    }

    #[test]
    fn auxiliary_embedding_unifies_top_and_bottom() {
        let core = FeatureStructure::parse("[n2t: [gen: #g], n2b: [gen: masc]]").unwrap();
        let nop = FeatureStructure::parse("[foot: #1 [], root: #1]").unwrap();
        let embedded = nop.embed_aux("n2t", "n2b").unwrap();
        assert!(core.unify(&embedded).is_some());
    }
}
