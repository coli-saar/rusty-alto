use packed_term_arena::tree::{Tree as ArenaTree, TreeArena};
use pyo3::{
    create_exception,
    exceptions::{PyRuntimeError, PyValueError},
    prelude::*,
    types::{PyDict, PyModule},
};
use rusty_alto::{
    APPEND_SYMBOL, Algebra, AstarHeuristic, AstarOptions, BinarizedTagTreeDecompositionAutomaton,
    BinarizedTagTreeState, Binarizing, BottomUpTa, CondensedTa, DecompositionAutomaton, Explicit,
    ExplicitBuilder, ExplicitWithSignature, FeatureStructure, IndexedBottomUpTa,
    InputCodecRegistry, Irtg, LanguageCardinality, MaterializationStrategy, ParseControl,
    Signature, Span, StateId, StateUniverse, StringAlgebra, StringDecompositionAutomaton, Symbol,
    TagSpan, TagStringAlgebra, TagStringDecompositionAutomaton, TagTreeAlgebra, TagTreeContext,
    TagTreeDecompositionAutomaton, TopDownTa, VisualRepresentation, ViterbiTree, parse_irtg,
};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    hash::{Hash, Hasher},
    path::Path,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
    },
};

create_exception!(_rusty_alto, RustyAltoError, PyRuntimeError);
create_exception!(_rusty_alto, UnsupportedOperationError, RustyAltoError);
create_exception!(_rusty_alto, StateOwnerError, RustyAltoError);

static NEXT_OWNER: AtomicU64 = AtomicU64::new(1);

fn next_owner() -> u64 {
    NEXT_OWNER.fetch_add(1, Ordering::Relaxed)
}

fn value_error(error: impl fmt::Display) -> PyErr {
    PyValueError::new_err(error.to_string())
}

fn runtime_error(error: impl fmt::Display) -> PyErr {
    RustyAltoError::new_err(error.to_string())
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StateValue {
    Explicit(StateId),
    Span(Span),
    TagSpan(TagSpan),
    TagTree(TagTreeContext),
    BinarizedTagTree(BinarizedTagTreeState),
    Product(Box<StateValue>, Box<StateValue>),
    Determinized(Vec<StateValue>),
}

impl fmt::Display for StateValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Explicit(q) => write!(f, "q{}", q.0),
            Self::Span(q) => q.fmt(f),
            Self::TagSpan(q) => q.fmt(f),
            Self::TagTree(q) => q.fmt(f),
            Self::BinarizedTagTree(q) => q.fmt(f),
            Self::Product(left, right) => write!(f, "({left}, {right})"),
            Self::Determinized(states) => {
                f.write_str("{")?;
                for (index, state) in states.iter().enumerate() {
                    if index > 0 {
                        f.write_str(", ")?;
                    }
                    state.fmt(f)?;
                }
                f.write_str("}")
            }
        }
    }
}

#[pyclass(name = "State", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyState {
    owner: u64,
    value: StateValue,
    display: String,
}

impl PyState {
    fn new(owner: u64, value: StateValue, display: String) -> Self {
        Self {
            owner,
            value,
            display,
        }
    }
}

#[pymethods]
impl PyState {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.value {
            StateValue::Explicit(_) => "explicit",
            StateValue::Span(_) => "span",
            StateValue::TagSpan(_) => "tag_span",
            StateValue::TagTree(_) => "tag_tree_context",
            StateValue::BinarizedTagTree(_) => "binarized_tag_tree",
            StateValue::Product(_, _) => "product",
            StateValue::Determinized(_) => "set",
        }
    }

    #[getter]
    fn id(&self) -> Option<u32> {
        match self.value {
            StateValue::Explicit(q) => Some(q.0),
            _ => None,
        }
    }

    #[getter]
    fn start(&self) -> Option<usize> {
        match self.value {
            StateValue::Span(span) => Some(span.start),
            StateValue::TagSpan(TagSpan::String(span)) => Some(span.start),
            _ => None,
        }
    }

    #[getter]
    fn end(&self) -> Option<usize> {
        match self.value {
            StateValue::Span(span) => Some(span.end),
            StateValue::TagSpan(TagSpan::String(span)) => Some(span.end),
            _ => None,
        }
    }

    fn components(&self) -> Vec<PyState> {
        match &self.value {
            StateValue::Product(left, right) => vec![
                PyState::new(self.owner, (**left).clone(), left.to_string()),
                PyState::new(self.owner, (**right).clone(), right.to_string()),
            ],
            StateValue::Determinized(states) => states
                .iter()
                .cloned()
                .map(|value| PyState::new(self.owner, value.clone(), value.to_string()))
                .collect(),
            StateValue::TagSpan(TagSpan::Pair(left, right)) => vec![
                PyState::new(self.owner, StateValue::Span(*left), left.to_string()),
                PyState::new(self.owner, StateValue::Span(*right), right.to_string()),
            ],
            _ => Vec::new(),
        }
    }

    fn __str__(&self) -> &str {
        &self.display
    }

    fn __repr__(&self) -> String {
        format!("State({:?})", self.display)
    }

    fn __hash__(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.owner.hash(&mut hasher);
        self.value.hash(&mut hasher);
        hasher.finish()
    }

    fn __richcmp__(&self, other: &PyState, op: pyo3::basic::CompareOp) -> bool {
        match op {
            pyo3::basic::CompareOp::Eq => self.owner == other.owner && self.value == other.value,
            pyo3::basic::CompareOp::Ne => self.owner != other.owner || self.value != other.value,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct TreeNode {
    label: String,
    children: Vec<TreeNode>,
}

#[pyclass(name = "Tree", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyTree {
    node: TreeNode,
}

impl PyTree {
    fn from_arena(arena: &TreeArena<String>, root: ArenaTree) -> Self {
        fn copy(arena: &TreeArena<String>, node: ArenaTree) -> TreeNode {
            TreeNode {
                label: arena.get_label(node).clone(),
                children: arena
                    .get_children(node)
                    .iter()
                    .map(|&child| copy(arena, child))
                    .collect(),
            }
        }
        Self {
            node: copy(arena, root),
        }
    }
}

#[pymethods]
impl PyTree {
    #[new]
    #[pyo3(signature = (label, children=Vec::new()))]
    fn new(label: String, children: Vec<PyTree>) -> Self {
        Self {
            node: TreeNode {
                label,
                children: children.into_iter().map(|tree| tree.node).collect(),
            },
        }
    }

    #[getter]
    fn label(&self) -> &str {
        &self.node.label
    }

    #[getter]
    fn children(&self) -> Vec<PyTree> {
        self.node
            .children
            .iter()
            .cloned()
            .map(|node| PyTree { node })
            .collect()
    }

    fn __len__(&self) -> usize {
        self.node.children.len()
    }

    fn __str__(&self) -> String {
        fn render(node: &TreeNode, out: &mut String) {
            out.push_str(&node.label);
            if !node.children.is_empty() {
                out.push('(');
                for (index, child) in node.children.iter().enumerate() {
                    if index > 0 {
                        out.push_str(", ");
                    }
                    render(child, out);
                }
                out.push(')');
            }
        }
        let mut out = String::new();
        render(&self.node, &mut out);
        out
    }

    fn __repr__(&self) -> String {
        format!("Tree({:?})", self.__str__())
    }

    fn __hash__(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.node.hash(&mut hasher);
        hasher.finish()
    }

    fn __richcmp__(&self, other: &PyTree, op: pyo3::basic::CompareOp) -> bool {
        match op {
            pyo3::basic::CompareOp::Eq => self.node == other.node,
            pyo3::basic::CompareOp::Ne => self.node != other.node,
            _ => false,
        }
    }
}

#[pyclass(name = "Signature", from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PySignature {
    inner: Arc<Signature>,
}

#[pymethods]
impl PySignature {
    #[staticmethod]
    fn from_symbols(symbols: Vec<(String, usize)>) -> PyResult<Self> {
        let mut signature = Signature::new();
        for (name, arity) in symbols {
            signature.intern(name, arity).map_err(value_error)?;
        }
        Ok(Self {
            inner: Arc::new(signature),
        })
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn symbols(&self) -> Vec<(u32, String, usize)> {
        (0..self.inner.len())
            .map(|raw| {
                let symbol = Symbol(raw as u32);
                (
                    symbol.0,
                    self.inner.resolve(symbol).to_owned(),
                    self.inner.arity(symbol),
                )
            })
            .collect()
    }

    fn id(&self, name: &str) -> Option<u32> {
        self.inner.get(name).map(|symbol| symbol.0)
    }

    fn name(&self, symbol: u32) -> PyResult<String> {
        if symbol as usize >= self.inner.len() {
            return Err(value_error("symbol ID is outside this signature"));
        }
        Ok(self.inner.resolve(Symbol(symbol)).to_owned())
    }

    fn arity(&self, symbol: u32) -> PyResult<usize> {
        if symbol as usize >= self.inner.len() {
            return Err(value_error("symbol ID is outside this signature"));
        }
        Ok(self.inner.arity(Symbol(symbol)))
    }
}

#[pyclass(name = "Homomorphism", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyHomomorphism {
    inner: Arc<HomomorphismData>,
}

fn compile_hom_node(
    node: &TreeNode,
    target: &Signature,
    source_arity: usize,
    variables: &mut Vec<usize>,
) -> PyResult<HomNode> {
    if let Some(variable) = node.label.strip_prefix('?') {
        if !node.children.is_empty() {
            return Err(value_error("homomorphism variables cannot have children"));
        }
        let one_based = variable
            .parse::<usize>()
            .map_err(|_| value_error(format!("invalid homomorphism variable {:?}", node.label)))?;
        if one_based == 0 || one_based > source_arity {
            return Err(value_error(format!(
                "variable {:?} is outside source arity {}",
                node.label, source_arity
            )));
        }
        let index = one_based - 1;
        variables.push(index);
        return Ok(HomNode::Variable(index));
    }
    let symbol = target
        .get(&node.label)
        .ok_or_else(|| value_error(format!("unknown target symbol {:?}", node.label)))?;
    if target.arity(symbol) != node.children.len() {
        return Err(value_error(format!(
            "target symbol {:?} has arity {}, term uses {}",
            node.label,
            target.arity(symbol),
            node.children.len()
        )));
    }
    Ok(HomNode::Symbol(
        symbol,
        node.children
            .iter()
            .map(|child| compile_hom_node(child, target, source_arity, variables))
            .collect::<PyResult<Vec<_>>>()?,
    ))
}

#[pymethods]
impl PyHomomorphism {
    #[staticmethod]
    fn from_terms(
        source: &PySignature,
        target: &PySignature,
        terms: HashMap<u32, PyTree>,
    ) -> PyResult<Self> {
        let mut compiled = HashMap::new();
        for (raw, tree) in terms {
            if raw as usize >= source.inner.len() {
                return Err(value_error("source symbol ID is outside the signature"));
            }
            let symbol = Symbol(raw);
            let arity = source.inner.arity(symbol);
            let mut variables = Vec::new();
            let term = compile_hom_node(&tree.node, &target.inner, arity, &mut variables)?;
            variables.sort_unstable();
            if variables != (0..arity).collect::<Vec<_>>() {
                return Err(value_error(format!(
                    "image for {:?} must use each variable ?1..?{} exactly once",
                    source.inner.resolve(symbol),
                    arity
                )));
            }
            compiled.insert(symbol, term);
        }
        Ok(Self {
            inner: Arc::new(HomomorphismData {
                source: source.inner.clone(),
                target: target.inner.clone(),
                terms: compiled,
            }),
        })
    }

    #[getter]
    fn source_signature(&self) -> PySignature {
        PySignature {
            inner: self.inner.source.clone(),
        }
    }

    #[getter]
    fn target_signature(&self) -> PySignature {
        PySignature {
            inner: self.inner.target.clone(),
        }
    }
}

#[derive(Clone)]
struct NamedExplicit {
    automaton: Explicit,
    signature: Arc<Signature>,
    state_names: Arc<Vec<String>>,
}

#[derive(Clone)]
enum AutomatonKind {
    Explicit(NamedExplicit),
    String {
        automaton: StringDecompositionAutomaton,
        signature: Arc<Signature>,
    },
    TagString {
        automaton: TagStringDecompositionAutomaton,
        signature: Arc<Signature>,
    },
    TagTree {
        automaton: TagTreeDecompositionAutomaton,
        signature: Arc<Signature>,
    },
    BinarizedTagTree {
        automaton: BinarizedTagTreeDecompositionAutomaton,
        signature: Arc<Signature>,
    },
    Product {
        left: Arc<AutomatonData>,
        right: Arc<AutomatonData>,
        signature: Arc<Signature>,
    },
    Determinized {
        inner: Arc<AutomatonData>,
    },
    Mapped {
        inner: Arc<AutomatonData>,
        signature: Arc<Signature>,
        mapping: Arc<HashMap<Symbol, Symbol>>,
    },
    InverseHomomorphism {
        inner: Arc<AutomatonData>,
        homomorphism: Arc<HomomorphismData>,
    },
}

#[derive(Clone)]
struct AutomatonData {
    owner: u64,
    kind: AutomatonKind,
}

impl AutomatonData {
    fn signature(&self) -> Arc<Signature> {
        match &self.kind {
            AutomatonKind::Explicit(value) => value.signature.clone(),
            AutomatonKind::String { signature, .. }
            | AutomatonKind::TagString { signature, .. }
            | AutomatonKind::TagTree { signature, .. }
            | AutomatonKind::BinarizedTagTree { signature, .. }
            | AutomatonKind::Product { signature, .. }
            | AutomatonKind::Mapped { signature, .. } => signature.clone(),
            AutomatonKind::Determinized { inner } => inner.signature(),
            AutomatonKind::InverseHomomorphism { homomorphism, .. } => homomorphism.source.clone(),
        }
    }

    fn state_display(&self, value: &StateValue) -> String {
        match (&self.kind, value) {
            (AutomatonKind::Explicit(named), StateValue::Explicit(q)) => named
                .state_names
                .get(q.index())
                .cloned()
                .unwrap_or_else(|| format!("q{}", q.0)),
            (AutomatonKind::Product { left, right, .. }, StateValue::Product(a, b)) => {
                format!("({}, {})", left.state_display(a), right.state_display(b))
            }
            (AutomatonKind::Determinized { inner }, StateValue::Determinized(states)) => {
                let values = states
                    .iter()
                    .map(|state| inner.state_display(state))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{values}}}")
            }
            (AutomatonKind::Mapped { inner, .. }, state) => inner.state_display(state),
            (AutomatonKind::InverseHomomorphism { inner, .. }, state) => inner.state_display(state),
            (_, state) => state.to_string(),
        }
    }

    fn py_state(&self, value: StateValue) -> PyState {
        let display = self.state_display(&value);
        PyState::new(self.owner, value, display)
    }

    fn check_state<'a>(&self, state: &'a PyState) -> PyResult<&'a StateValue> {
        if state.owner != self.owner {
            return Err(StateOwnerError::new_err(
                "state belongs to a different automaton",
            ));
        }
        Ok(&state.value)
    }

    fn step(&self, symbol: Symbol, children: &[StateValue]) -> Vec<StateValue> {
        let mut out = Vec::new();
        match &self.kind {
            AutomatonKind::Explicit(named) => {
                let Some(children) = explicit_states(children) else {
                    return out;
                };
                named.automaton.step(symbol, &children, &mut |q| {
                    out.push(StateValue::Explicit(q))
                });
            }
            AutomatonKind::String { automaton, .. } => {
                let Some(children) = span_states(children) else {
                    return out;
                };
                automaton.step(symbol, &children, &mut |q| out.push(StateValue::Span(q)));
            }
            AutomatonKind::TagString { automaton, .. } => {
                let Some(children) = tag_span_states(children) else {
                    return out;
                };
                automaton.step(symbol, &children, &mut |q| out.push(StateValue::TagSpan(q)));
            }
            AutomatonKind::TagTree { automaton, .. } => {
                let Some(children) = tag_tree_states(children) else {
                    return out;
                };
                automaton.step(symbol, &children, &mut |q| out.push(StateValue::TagTree(q)));
            }
            AutomatonKind::BinarizedTagTree { automaton, .. } => {
                let Some(children) = bin_tag_tree_states(children) else {
                    return out;
                };
                automaton.step(symbol, &children, &mut |q| {
                    out.push(StateValue::BinarizedTagTree(q))
                });
            }
            AutomatonKind::Product { left, right, .. } => {
                let mut left_children = Vec::with_capacity(children.len());
                let mut right_children = Vec::with_capacity(children.len());
                for child in children {
                    let StateValue::Product(a, b) = child else {
                        return out;
                    };
                    left_children.push((**a).clone());
                    right_children.push((**b).clone());
                }
                let left_results = left.step(symbol, &left_children);
                let right_results = right.step(symbol, &right_children);
                for a in &left_results {
                    for b in &right_results {
                        out.push(StateValue::Product(
                            Box::new(a.clone()),
                            Box::new(b.clone()),
                        ));
                    }
                }
            }
            AutomatonKind::Determinized { inner } => {
                let mut pools = Vec::with_capacity(children.len());
                for child in children {
                    let StateValue::Determinized(states) = child else {
                        return out;
                    };
                    pools.push(states.iter().cloned().collect::<Vec<_>>());
                }
                let mut result = HashSet::new();
                cartesian(&pools, &mut |tuple| {
                    result.extend(inner.step(symbol, tuple));
                });
                if !result.is_empty() {
                    let mut result = result.into_iter().collect::<Vec<_>>();
                    result.sort_by_key(StateValue::to_string);
                    out.push(StateValue::Determinized(result));
                }
            }
            AutomatonKind::Mapped { inner, mapping, .. } => {
                let mapped = mapping.get(&symbol).copied().unwrap_or(symbol);
                out = inner.step(mapped, children);
            }
            AutomatonKind::InverseHomomorphism {
                inner,
                homomorphism,
            } => {
                if let Some(term) = homomorphism.terms.get(&symbol) {
                    let mut unique = HashSet::new();
                    evaluate_hom_term(term, children, inner, &mut unique);
                    out.extend(unique);
                }
            }
        }
        out
    }

    fn is_accepting(&self, state: &StateValue) -> bool {
        match (&self.kind, state) {
            (AutomatonKind::Explicit(named), StateValue::Explicit(q)) => {
                named.automaton.is_accepting(q)
            }
            (AutomatonKind::String { automaton, .. }, StateValue::Span(q)) => {
                automaton.is_accepting(q)
            }
            (AutomatonKind::TagString { automaton, .. }, StateValue::TagSpan(q)) => {
                automaton.is_accepting(q)
            }
            (AutomatonKind::TagTree { automaton, .. }, StateValue::TagTree(q)) => {
                automaton.is_accepting(q)
            }
            (
                AutomatonKind::BinarizedTagTree { automaton, .. },
                StateValue::BinarizedTagTree(q),
            ) => automaton.is_accepting(q),
            (AutomatonKind::Product { left, right, .. }, StateValue::Product(a, b)) => {
                left.is_accepting(a) && right.is_accepting(b)
            }
            (AutomatonKind::Determinized { inner }, StateValue::Determinized(states)) => {
                states.iter().any(|state| inner.is_accepting(state))
            }
            (AutomatonKind::Mapped { inner, .. }, state) => inner.is_accepting(state),
            (AutomatonKind::InverseHomomorphism { inner, .. }, state) => inner.is_accepting(state),
            _ => false,
        }
    }

    fn all_states(&self) -> Option<Vec<StateValue>> {
        let mut out = Vec::new();
        match &self.kind {
            AutomatonKind::Explicit(named) => named
                .automaton
                .all_states(&mut |q| out.push(StateValue::Explicit(q))),
            AutomatonKind::String { automaton, .. } => {
                automaton.all_states(&mut |q| out.push(StateValue::Span(q)))
            }
            AutomatonKind::TagString { automaton, .. } => {
                automaton.all_states(&mut |q| out.push(StateValue::TagSpan(q)))
            }
            AutomatonKind::TagTree { automaton, .. } => {
                automaton.all_states(&mut |q| out.push(StateValue::TagTree(q)))
            }
            AutomatonKind::BinarizedTagTree { automaton, .. } => {
                automaton.all_states(&mut |q| out.push(StateValue::BinarizedTagTree(q)))
            }
            AutomatonKind::Product { left, right, .. } => {
                let left = left.all_states()?;
                let right = right.all_states()?;
                for a in &left {
                    for b in &right {
                        out.push(StateValue::Product(
                            Box::new(a.clone()),
                            Box::new(b.clone()),
                        ));
                    }
                }
            }
            AutomatonKind::Determinized { .. } => return None,
            AutomatonKind::Mapped { inner, .. } => return inner.all_states(),
            AutomatonKind::InverseHomomorphism { inner, .. } => return inner.all_states(),
        }
        Some(out)
    }

    fn initial_states(&self) -> Option<Vec<StateValue>> {
        let mut out = Vec::new();
        match &self.kind {
            AutomatonKind::Explicit(named) => named
                .automaton
                .initial_states(&mut |q| out.push(StateValue::Explicit(q))),
            AutomatonKind::String { automaton, .. } => {
                automaton.initial_states(&mut |q| out.push(StateValue::Span(q)))
            }
            AutomatonKind::TagString { automaton, .. } => {
                automaton.initial_states(&mut |q| out.push(StateValue::TagSpan(q)))
            }
            AutomatonKind::TagTree { automaton, .. } => {
                automaton.initial_states(&mut |q| out.push(StateValue::TagTree(q)))
            }
            AutomatonKind::BinarizedTagTree { automaton, .. } => {
                automaton.initial_states(&mut |q| out.push(StateValue::BinarizedTagTree(q)))
            }
            AutomatonKind::Product { left, right, .. } => {
                for a in left.initial_states()? {
                    for b in right.initial_states()? {
                        out.push(StateValue::Product(Box::new(a.clone()), Box::new(b)));
                    }
                }
            }
            AutomatonKind::Determinized { .. } => return None,
            AutomatonKind::Mapped { inner, .. } => return inner.initial_states(),
            AutomatonKind::InverseHomomorphism { .. } => return None,
        }
        Some(out)
    }

    fn rules_for_parent(&self, parent: &StateValue) -> Option<Vec<(Symbol, Vec<StateValue>)>> {
        let mut out = Vec::new();
        match (&self.kind, parent) {
            (AutomatonKind::Explicit(named), StateValue::Explicit(q)) => {
                named.automaton.step_topdown(q, &mut |symbol, children| {
                    out.push((
                        symbol,
                        children.iter().copied().map(StateValue::Explicit).collect(),
                    ));
                });
            }
            (AutomatonKind::String { automaton, .. }, StateValue::Span(q)) => {
                automaton.step_topdown(q, &mut |symbol, children| {
                    out.push((
                        symbol,
                        children.iter().copied().map(StateValue::Span).collect(),
                    ));
                });
            }
            (AutomatonKind::TagString { automaton, .. }, StateValue::TagSpan(q)) => {
                automaton.step_topdown(q, &mut |symbol, children| {
                    out.push((
                        symbol,
                        children.iter().copied().map(StateValue::TagSpan).collect(),
                    ));
                });
            }
            (AutomatonKind::TagTree { automaton, .. }, StateValue::TagTree(q)) => {
                automaton.step_topdown(q, &mut |symbol, children| {
                    out.push((
                        symbol,
                        children.iter().copied().map(StateValue::TagTree).collect(),
                    ));
                });
            }
            (
                AutomatonKind::BinarizedTagTree { automaton, .. },
                StateValue::BinarizedTagTree(q),
            ) => {
                automaton.step_topdown(q, &mut |symbol, children| {
                    out.push((
                        symbol,
                        children
                            .iter()
                            .cloned()
                            .map(StateValue::BinarizedTagTree)
                            .collect(),
                    ));
                });
            }
            (AutomatonKind::Product { left, right, .. }, StateValue::Product(a, b)) => {
                let left_rules = left.rules_for_parent(a)?;
                let right_rules = right.rules_for_parent(b)?;
                for (left_symbol, left_children) in &left_rules {
                    for (right_symbol, right_children) in &right_rules {
                        if left_symbol == right_symbol
                            && left_children.len() == right_children.len()
                        {
                            out.push((
                                *left_symbol,
                                left_children
                                    .iter()
                                    .cloned()
                                    .zip(right_children.iter().cloned())
                                    .map(|(x, y)| StateValue::Product(Box::new(x), Box::new(y)))
                                    .collect(),
                            ));
                        }
                    }
                }
            }
            (AutomatonKind::Mapped { inner, mapping, .. }, state) => {
                let reverse: HashMap<Symbol, Vec<Symbol>> =
                    mapping
                        .iter()
                        .fold(HashMap::new(), |mut map, (&src, &dst)| {
                            map.entry(dst).or_default().push(src);
                            map
                        });
                for (symbol, children) in inner.rules_for_parent(state)? {
                    if let Some(sources) = reverse.get(&symbol) {
                        for source in sources {
                            out.push((*source, children.clone()));
                        }
                    } else {
                        out.push((symbol, children));
                    }
                }
            }
            (AutomatonKind::InverseHomomorphism { .. }, _) => return None,
            _ => return None,
        }
        Some(out)
    }

    fn rules_for_child(
        &self,
        symbol: Symbol,
        position: usize,
        state: &StateValue,
    ) -> Option<Vec<(Vec<StateValue>, StateValue)>> {
        let mut out = Vec::new();
        match (&self.kind, state) {
            (AutomatonKind::Explicit(named), StateValue::Explicit(q)) => {
                named
                    .automaton
                    .step_partial(symbol, position, q, &mut |children, result| {
                        out.push((
                            children.iter().copied().map(StateValue::Explicit).collect(),
                            StateValue::Explicit(result),
                        ));
                    });
            }
            (AutomatonKind::String { automaton, .. }, StateValue::Span(q)) => {
                automaton.step_partial(symbol, position, q, &mut |children, result| {
                    out.push((
                        children.iter().copied().map(StateValue::Span).collect(),
                        StateValue::Span(result),
                    ));
                });
            }
            (AutomatonKind::TagString { automaton, .. }, StateValue::TagSpan(q)) => {
                automaton.step_partial(symbol, position, q, &mut |children, result| {
                    out.push((
                        children.iter().copied().map(StateValue::TagSpan).collect(),
                        StateValue::TagSpan(result),
                    ));
                });
            }
            (AutomatonKind::Mapped { inner, mapping, .. }, state) => {
                return inner.rules_for_child(
                    mapping.get(&symbol).copied().unwrap_or(symbol),
                    position,
                    state,
                );
            }
            _ => return None,
        }
        Some(out)
    }

    fn condensed_rules(&self) -> Option<Vec<(Vec<StateValue>, Vec<Symbol>, StateValue)>> {
        let mut out = Vec::new();
        match &self.kind {
            AutomatonKind::Explicit(named) => {
                named
                    .automaton
                    .condensed_rules(&mut |children, symbols, result| {
                        out.push((
                            children.iter().copied().map(StateValue::Explicit).collect(),
                            symbols.iter().collect(),
                            StateValue::Explicit(result),
                        ));
                    });
            }
            AutomatonKind::String { automaton, .. } => {
                automaton.condensed_rules(&mut |children, symbols, result| {
                    out.push((
                        children.iter().copied().map(StateValue::Span).collect(),
                        symbols.iter().collect(),
                        StateValue::Span(result),
                    ));
                });
            }
            AutomatonKind::TagString { automaton, .. } => {
                automaton.condensed_rules(&mut |children, symbols, result| {
                    out.push((
                        children.iter().copied().map(StateValue::TagSpan).collect(),
                        symbols.iter().collect(),
                        StateValue::TagSpan(result),
                    ));
                });
            }
            AutomatonKind::TagTree { automaton, .. } => {
                automaton.condensed_rules(&mut |children, symbols, result| {
                    out.push((
                        children.iter().copied().map(StateValue::TagTree).collect(),
                        symbols.iter().collect(),
                        StateValue::TagTree(result),
                    ));
                });
            }
            AutomatonKind::BinarizedTagTree { automaton, .. } => {
                automaton.condensed_rules(&mut |children, symbols, result| {
                    out.push((
                        children
                            .iter()
                            .cloned()
                            .map(StateValue::BinarizedTagTree)
                            .collect(),
                        symbols.iter().collect(),
                        StateValue::BinarizedTagTree(result),
                    ));
                });
            }
            _ => return None,
        }
        Some(out)
    }

    fn capabilities(&self) -> Capabilities {
        match &self.kind {
            AutomatonKind::Explicit(_) => Capabilities::all(),
            AutomatonKind::String { .. } => Capabilities::all(),
            AutomatonKind::TagString { .. } => Capabilities {
                deterministic: false,
                state_universe: true,
                top_down: true,
                indexed: true,
                condensed: true,
            },
            AutomatonKind::TagTree { .. } | AutomatonKind::BinarizedTagTree { .. } => {
                Capabilities {
                    deterministic: false,
                    state_universe: true,
                    top_down: true,
                    indexed: false,
                    condensed: true,
                }
            }
            AutomatonKind::Product { left, right, .. } => {
                let a = left.capabilities();
                let b = right.capabilities();
                Capabilities {
                    deterministic: a.deterministic && b.deterministic,
                    state_universe: a.state_universe && b.state_universe,
                    top_down: a.top_down && b.top_down,
                    indexed: a.indexed && b.indexed,
                    condensed: false,
                }
            }
            AutomatonKind::Determinized { inner: _ } => Capabilities {
                deterministic: true,
                state_universe: false,
                top_down: false,
                indexed: false,
                condensed: false,
            },
            AutomatonKind::Mapped { inner, .. } => inner.capabilities(),
            AutomatonKind::InverseHomomorphism { inner, .. } => {
                let inner = inner.capabilities();
                Capabilities {
                    deterministic: inner.deterministic,
                    state_universe: inner.state_universe,
                    top_down: false,
                    indexed: false,
                    condensed: false,
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
enum HomNode {
    Variable(usize),
    Symbol(Symbol, Vec<HomNode>),
}

#[derive(Clone)]
struct HomomorphismData {
    source: Arc<Signature>,
    target: Arc<Signature>,
    terms: HashMap<Symbol, HomNode>,
}

fn evaluate_hom_term(
    term: &HomNode,
    source_children: &[StateValue],
    inner: &AutomatonData,
    out: &mut HashSet<StateValue>,
) {
    match term {
        HomNode::Variable(index) => {
            if let Some(state) = source_children.get(*index) {
                out.insert(state.clone());
            }
        }
        HomNode::Symbol(symbol, children) => {
            let mut pools = Vec::with_capacity(children.len());
            for child in children {
                let mut values = HashSet::new();
                evaluate_hom_term(child, source_children, inner, &mut values);
                if values.is_empty() {
                    return;
                }
                pools.push(values.into_iter().collect::<Vec<_>>());
            }
            cartesian(&pools, &mut |tuple| {
                out.extend(inner.step(*symbol, tuple));
            });
        }
    }
}

#[derive(Clone, Copy)]
struct Capabilities {
    deterministic: bool,
    state_universe: bool,
    top_down: bool,
    indexed: bool,
    condensed: bool,
}

impl Capabilities {
    fn all() -> Self {
        Self {
            deterministic: true,
            state_universe: true,
            top_down: true,
            indexed: true,
            condensed: true,
        }
    }
}

fn explicit_states(values: &[StateValue]) -> Option<Vec<StateId>> {
    values
        .iter()
        .map(|value| match value {
            StateValue::Explicit(q) => Some(*q),
            _ => None,
        })
        .collect()
}

fn span_states(values: &[StateValue]) -> Option<Vec<Span>> {
    values
        .iter()
        .map(|value| match value {
            StateValue::Span(q) => Some(*q),
            _ => None,
        })
        .collect()
}

fn tag_span_states(values: &[StateValue]) -> Option<Vec<TagSpan>> {
    values
        .iter()
        .map(|value| match value {
            StateValue::TagSpan(q) => Some(*q),
            _ => None,
        })
        .collect()
}

fn tag_tree_states(values: &[StateValue]) -> Option<Vec<TagTreeContext>> {
    values
        .iter()
        .map(|value| match value {
            StateValue::TagTree(q) => Some(*q),
            _ => None,
        })
        .collect()
}

fn bin_tag_tree_states(values: &[StateValue]) -> Option<Vec<BinarizedTagTreeState>> {
    values
        .iter()
        .map(|value| match value {
            StateValue::BinarizedTagTree(q) => Some(q.clone()),
            _ => None,
        })
        .collect()
}

fn cartesian<T: Clone>(pools: &[Vec<T>], out: &mut dyn FnMut(&[T])) {
    if pools.iter().any(Vec::is_empty) {
        return;
    }
    if pools.is_empty() {
        out(&[]);
        return;
    }
    let mut indices = vec![0usize; pools.len()];
    let mut tuple = pools.iter().map(|pool| pool[0].clone()).collect::<Vec<_>>();
    loop {
        out(&tuple);
        let mut position = pools.len();
        loop {
            if position == 0 {
                return;
            }
            position -= 1;
            indices[position] += 1;
            if indices[position] < pools[position].len() {
                tuple[position] = pools[position][indices[position]].clone();
                for reset in position + 1..pools.len() {
                    indices[reset] = 0;
                    tuple[reset] = pools[reset][0].clone();
                }
                break;
            }
        }
    }
}

fn resolve_symbol(signature: &Signature, value: &Bound<'_, PyAny>) -> PyResult<Symbol> {
    if let Ok(id) = value.extract::<u32>() {
        if id as usize >= signature.len() {
            return Err(value_error("symbol ID is outside this signature"));
        }
        return Ok(Symbol(id));
    }
    let name = value.extract::<String>()?;
    signature
        .get(&name)
        .ok_or_else(|| value_error(format!("unknown symbol {name:?}")))
}

#[pyclass(name = "Automaton", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyAutomaton {
    data: Arc<AutomatonData>,
}

impl PyAutomaton {
    fn from_kind(kind: AutomatonKind) -> Self {
        Self {
            data: Arc::new(AutomatonData {
                owner: next_owner(),
                kind,
            }),
        }
    }
}

#[pymethods]
impl PyAutomaton {
    #[getter]
    fn signature(&self) -> PySignature {
        PySignature {
            inner: self.data.signature(),
        }
    }

    #[getter]
    fn is_deterministic(&self) -> bool {
        self.data.capabilities().deterministic
    }

    #[getter]
    fn has_state_universe(&self) -> bool {
        self.data.capabilities().state_universe
    }

    #[getter]
    fn is_top_down(&self) -> bool {
        self.data.capabilities().top_down
    }

    #[getter]
    fn is_indexed(&self) -> bool {
        self.data.capabilities().indexed
    }

    #[getter]
    fn is_condensed(&self) -> bool {
        self.data.capabilities().condensed
    }

    fn step(
        &self,
        symbol: &Bound<'_, PyAny>,
        children: Vec<PyRef<'_, PyState>>,
    ) -> PyResult<Vec<PyState>> {
        let signature = self.data.signature();
        let symbol = resolve_symbol(&signature, symbol)?;
        let children = children
            .iter()
            .map(|state| self.data.check_state(state).cloned())
            .collect::<PyResult<Vec<_>>>()?;
        Ok(self
            .data
            .step(symbol, &children)
            .into_iter()
            .map(|value| self.data.py_state(value))
            .collect())
    }

    fn step_deterministic(
        &self,
        symbol: &Bound<'_, PyAny>,
        children: Vec<PyRef<'_, PyState>>,
    ) -> PyResult<Option<PyState>> {
        if !self.is_deterministic() {
            return Err(UnsupportedOperationError::new_err(
                "automaton does not provide deterministic transitions",
            ));
        }
        let values = self.step(symbol, children)?;
        Ok((values.len() == 1).then(|| values[0].clone()))
    }

    fn is_accepting(&self, state: &PyState) -> PyResult<bool> {
        Ok(self.data.is_accepting(self.data.check_state(state)?))
    }

    fn states(&self) -> PyResult<Vec<PyState>> {
        let states = self.data.all_states().ok_or_else(|| {
            UnsupportedOperationError::new_err("automaton has no finite state universe")
        })?;
        Ok(states
            .into_iter()
            .map(|state| self.data.py_state(state))
            .collect())
    }

    fn initial_states(&self) -> PyResult<Vec<PyState>> {
        let states = self
            .data
            .initial_states()
            .ok_or_else(|| UnsupportedOperationError::new_err("automaton has no top-down view"))?;
        Ok(states
            .into_iter()
            .map(|state| self.data.py_state(state))
            .collect())
    }

    fn rules_for_parent(&self, parent: &PyState) -> PyResult<Vec<(u32, Vec<PyState>)>> {
        let parent = self.data.check_state(parent)?;
        let rules = self
            .data
            .rules_for_parent(parent)
            .ok_or_else(|| UnsupportedOperationError::new_err("automaton has no top-down view"))?;
        Ok(rules
            .into_iter()
            .map(|(symbol, children)| {
                (
                    symbol.0,
                    children
                        .into_iter()
                        .map(|state| self.data.py_state(state))
                        .collect(),
                )
            })
            .collect())
    }

    fn rules_for_child(
        &self,
        symbol: &Bound<'_, PyAny>,
        position: usize,
        state: &PyState,
    ) -> PyResult<Vec<(Vec<PyState>, PyState)>> {
        let signature = self.data.signature();
        let symbol = resolve_symbol(&signature, symbol)?;
        let state = self.data.check_state(state)?;
        let rules = self
            .data
            .rules_for_child(symbol, position, state)
            .ok_or_else(|| {
                UnsupportedOperationError::new_err("automaton has no indexed bottom-up view")
            })?;
        Ok(rules
            .into_iter()
            .map(|(children, result)| {
                (
                    children
                        .into_iter()
                        .map(|state| self.data.py_state(state))
                        .collect(),
                    self.data.py_state(result),
                )
            })
            .collect())
    }

    fn condensed_rules(&self) -> PyResult<Vec<(Vec<PyState>, Vec<u32>, PyState)>> {
        let rules = self
            .data
            .condensed_rules()
            .ok_or_else(|| UnsupportedOperationError::new_err("automaton has no condensed view"))?;
        Ok(rules
            .into_iter()
            .map(|(children, symbols, result)| {
                (
                    children
                        .into_iter()
                        .map(|state| self.data.py_state(state))
                        .collect(),
                    symbols.into_iter().map(|symbol| symbol.0).collect(),
                    self.data.py_state(result),
                )
            })
            .collect())
    }

    fn run(&self, tree: &PyTree) -> PyResult<Vec<PyState>> {
        fn visit(
            automaton: &AutomatonData,
            signature: &Signature,
            node: &TreeNode,
        ) -> PyResult<Vec<StateValue>> {
            let symbol = signature
                .get(&node.label)
                .ok_or_else(|| value_error(format!("unknown symbol {:?}", node.label)))?;
            let child_pools = node
                .children
                .iter()
                .map(|child| visit(automaton, signature, child))
                .collect::<PyResult<Vec<_>>>()?;
            let mut result = HashSet::new();
            cartesian(&child_pools, &mut |children| {
                result.extend(automaton.step(symbol, children));
            });
            Ok(result.into_iter().collect())
        }
        let signature = self.data.signature();
        Ok(visit(&self.data, &signature, &tree.node)?
            .into_iter()
            .map(|state| self.data.py_state(state))
            .collect())
    }

    fn rules(&self) -> PyResult<Vec<(u32, Vec<u32>, u32, f64)>> {
        let AutomatonKind::Explicit(named) = &self.data.kind else {
            return Err(UnsupportedOperationError::new_err(
                "only explicit automata store a finite weighted rule table",
            ));
        };
        Ok(named
            .automaton
            .rules()
            .map(|rule| {
                (
                    rule.symbol.0,
                    rule.children.iter().map(|state| state.0).collect(),
                    rule.result.0,
                    rule.weight,
                )
            })
            .collect())
    }

    fn viterbi(&self, py: Python<'_>) -> PyResult<Option<PyWeightedTree>> {
        let AutomatonKind::Explicit(named) = &self.data.kind else {
            return Err(UnsupportedOperationError::new_err(
                "Viterbi requires an explicit weighted automaton",
            ));
        };
        let named = named.clone();
        Ok(py.detach(move || {
            named
                .automaton
                .viterbi()
                .map(|tree| resolved_viterbi(&named.signature, tree))
        }))
    }

    #[pyo3(signature = (limit=10))]
    fn k_best(&self, py: Python<'_>, limit: usize) -> PyResult<Vec<PyWeightedTree>> {
        let AutomatonKind::Explicit(named) = &self.data.kind else {
            return Err(UnsupportedOperationError::new_err(
                "k-best enumeration requires an explicit weighted automaton",
            ));
        };
        let named = named.clone();
        Ok(py.detach(move || {
            let mut iterator = named.automaton.sorted_language();
            let mut values = Vec::new();
            for _ in 0..limit {
                let Some(weighted) = iterator.next() else {
                    break;
                };
                let weight = weighted.weight();
                let (arena, root) = iterator.clone_tree(weighted.tree());
                let (arena, root) = named.signature.resolve_tree(&arena, root);
                values.push(PyWeightedTree {
                    tree: PyTree::from_arena(&arena, root),
                    weight,
                    score: weight,
                });
            }
            values
        }))
    }

    fn language_cardinality(&self) -> PyResult<(String, Option<usize>)> {
        let AutomatonKind::Explicit(named) = &self.data.kind else {
            return Err(UnsupportedOperationError::new_err(
                "language cardinality requires an explicit automaton",
            ));
        };
        Ok(match named.automaton.language_cardinality() {
            LanguageCardinality::Finite(count) => ("finite".to_owned(), Some(count)),
            LanguageCardinality::Infinite => ("infinite".to_owned(), None),
            LanguageCardinality::TooLarge => ("too_large".to_owned(), None),
        })
    }

    fn accepts(&self, tree: &PyTree) -> PyResult<bool> {
        Ok(self
            .run(tree)?
            .iter()
            .any(|state| self.data.is_accepting(&state.value)))
    }

    fn product(&self, other: &PyAutomaton) -> PyResult<PyAutomaton> {
        let left_signature = self.data.signature();
        let right_signature = other.data.signature();
        if signature_shape(&left_signature) != signature_shape(&right_signature) {
            return Err(value_error(
                "product automata must use equivalent named signatures",
            ));
        }
        Ok(PyAutomaton::from_kind(AutomatonKind::Product {
            left: self.data.clone(),
            right: other.data.clone(),
            signature: left_signature,
        }))
    }

    fn determinize(&self) -> PyAutomaton {
        PyAutomaton::from_kind(AutomatonKind::Determinized {
            inner: self.data.clone(),
        })
    }

    fn map_symbols(&self, signature: &PySignature, mapping: HashMap<u32, u32>) -> PyResult<Self> {
        let inner_signature = self.data.signature();
        let mut resolved = HashMap::new();
        for (external, inner) in mapping {
            if external as usize >= signature.inner.len() || inner as usize >= inner_signature.len()
            {
                return Err(value_error("symbol mapping contains an out-of-range ID"));
            }
            resolved.insert(Symbol(external), Symbol(inner));
        }
        Ok(PyAutomaton::from_kind(AutomatonKind::Mapped {
            inner: self.data.clone(),
            signature: signature.inner.clone(),
            mapping: Arc::new(resolved),
        }))
    }

    fn inverse_homomorphism(&self, homomorphism: &PyHomomorphism) -> PyResult<Self> {
        if signature_shape(&self.data.signature()) != signature_shape(&homomorphism.inner.target) {
            return Err(value_error(
                "homomorphism target signature must match the inner automaton",
            ));
        }
        Ok(PyAutomaton::from_kind(AutomatonKind::InverseHomomorphism {
            inner: self.data.clone(),
            homomorphism: homomorphism.inner.clone(),
        }))
    }

    #[pyo3(signature = (alphabet=None))]
    fn materialize(
        &self,
        py: Python<'_>,
        alphabet: Option<Vec<(u32, usize)>>,
    ) -> PyResult<(PyAutomaton, Vec<PyState>)> {
        let signature = self.data.signature();
        let alphabet = alphabet.unwrap_or_else(|| {
            (0..signature.len())
                .map(|raw| {
                    let symbol = Symbol(raw as u32);
                    (symbol.0, signature.arity(symbol))
                })
                .collect()
        });
        let data = self.data.clone();
        let (automaton, states) = py.detach(move || materialize_dynamic(&data, &alphabet))?;
        let names = states
            .iter()
            .map(|state| self.data.state_display(state))
            .collect::<Vec<_>>();
        let explicit = PyAutomaton::from_kind(AutomatonKind::Explicit(NamedExplicit {
            automaton,
            signature,
            state_names: Arc::new(names),
        }));
        let mapping = states
            .into_iter()
            .map(|state| self.data.py_state(state))
            .collect();
        Ok((explicit, mapping))
    }

    fn __repr__(&self) -> String {
        let caps = self.data.capabilities();
        format!(
            "Automaton(deterministic={}, finite={}, top_down={}, indexed={}, condensed={})",
            caps.deterministic, caps.state_universe, caps.top_down, caps.indexed, caps.condensed
        )
    }
}

fn signature_shape(signature: &Signature) -> Vec<(String, usize)> {
    (0..signature.len())
        .map(|raw| {
            let symbol = Symbol(raw as u32);
            (
                signature.resolve(symbol).to_owned(),
                signature.arity(symbol),
            )
        })
        .collect()
}

fn materialize_dynamic(
    automaton: &AutomatonData,
    alphabet: &[(u32, usize)],
) -> PyResult<(Explicit, Vec<StateValue>)> {
    let mut builder = ExplicitBuilder::new();
    let mut ids = HashMap::<StateValue, StateId>::new();
    let mut states = Vec::<StateValue>::new();
    let mut queue = VecDeque::<StateValue>::new();
    let mut seen_rules = HashSet::<(Symbol, Vec<StateId>, StateId)>::new();

    let intern = |state: StateValue,
                  builder: &mut ExplicitBuilder,
                  ids: &mut HashMap<StateValue, StateId>,
                  states: &mut Vec<StateValue>,
                  queue: &mut VecDeque<StateValue>| {
        if let Some(&id) = ids.get(&state) {
            return id;
        }
        let id = builder.new_state();
        if automaton.is_accepting(&state) {
            builder.add_accepting(id);
        }
        ids.insert(state.clone(), id);
        states.push(state.clone());
        queue.push_back(state);
        id
    };

    for &(raw, arity) in alphabet {
        if arity != 0 {
            continue;
        }
        for result in automaton.step(Symbol(raw), &[]) {
            let parent = intern(result, &mut builder, &mut ids, &mut states, &mut queue);
            if seen_rules.insert((Symbol(raw), Vec::new(), parent)) {
                builder.add_rule(Symbol(raw), Vec::new(), parent);
            }
        }
    }

    while let Some(popped) = queue.pop_front() {
        let snapshot = states.clone();
        for &(raw, arity) in alphabet {
            if arity == 0 {
                continue;
            }
            let pools = vec![snapshot.clone(); arity];
            cartesian(&pools, &mut |tuple| {
                if !tuple.contains(&popped) {
                    return;
                }
                let child_ids = tuple.iter().map(|state| ids[state]).collect::<Vec<_>>();
                for result in automaton.step(Symbol(raw), tuple) {
                    let parent = intern(result, &mut builder, &mut ids, &mut states, &mut queue);
                    if seen_rules.insert((Symbol(raw), child_ids.clone(), parent)) {
                        builder.add_rule(Symbol(raw), child_ids.clone(), parent);
                    }
                }
            });
        }
    }
    Ok((builder.try_build().map_err(runtime_error)?, states))
}

#[pyclass(name = "AutomatonBuilder", module = "rusty_alto")]
struct PyAutomatonBuilder {
    signature: Signature,
    builder: Option<ExplicitBuilder>,
    states: HashMap<String, StateId>,
    state_names: Vec<String>,
}

#[pymethods]
impl PyAutomatonBuilder {
    #[new]
    fn new() -> Self {
        Self {
            signature: Signature::new(),
            builder: Some(ExplicitBuilder::new()),
            states: HashMap::new(),
            state_names: Vec::new(),
        }
    }

    #[pyo3(signature = (name, accepting=false))]
    fn add_state(&mut self, name: String, accepting: bool) -> PyResult<u32> {
        if self.states.contains_key(&name) {
            return Err(value_error(format!("duplicate state {name:?}")));
        }
        let builder = self
            .builder
            .as_mut()
            .ok_or_else(|| runtime_error("builder has already been consumed"))?;
        let state = builder.new_state();
        if accepting {
            builder.add_accepting(state);
        }
        self.states.insert(name.clone(), state);
        self.state_names.push(name);
        Ok(state.0)
    }

    #[pyo3(signature = (symbol, children, parent, weight=1.0))]
    fn add_rule(
        &mut self,
        symbol: String,
        children: Vec<String>,
        parent: String,
        weight: f64,
    ) -> PyResult<()> {
        let parent = *self
            .states
            .get(&parent)
            .ok_or_else(|| value_error("unknown parent state"))?;
        let children = children
            .iter()
            .map(|name| {
                self.states
                    .get(name)
                    .copied()
                    .ok_or_else(|| value_error(format!("unknown child state {name:?}")))
            })
            .collect::<PyResult<Vec<_>>>()?;
        let symbol = self
            .signature
            .intern(symbol, children.len())
            .map_err(value_error)?;
        self.builder
            .as_mut()
            .ok_or_else(|| runtime_error("builder has already been consumed"))?
            .add_weighted_rule(symbol, children, parent, weight);
        Ok(())
    }

    fn build(&mut self) -> PyResult<PyAutomaton> {
        let builder = self
            .builder
            .take()
            .ok_or_else(|| runtime_error("builder has already been consumed"))?;
        let automaton = builder.try_build().map_err(value_error)?;
        Ok(PyAutomaton::from_kind(AutomatonKind::Explicit(
            NamedExplicit {
                automaton,
                signature: Arc::new(self.signature.clone()),
                state_names: Arc::new(self.state_names.clone()),
            },
        )))
    }
}

#[pyclass(name = "StringAlgebra", module = "rusty_alto")]
struct PyStringAlgebra {
    inner: Mutex<StringAlgebra>,
}

#[pymethods]
impl PyStringAlgebra {
    #[new]
    fn new() -> Self {
        Self {
            inner: Mutex::new(StringAlgebra::new()),
        }
    }

    fn parse(&self, text: &str) -> Vec<String> {
        text.split_whitespace().map(str::to_owned).collect()
    }

    fn decompose(&self, text: &str) -> PyAutomaton {
        let mut algebra = self.inner.lock().unwrap();
        let value = algebra.parse_string(text);
        let automaton = algebra.decompose(value);
        let signature = Arc::new(algebra.signature().clone());
        PyAutomaton::from_kind(AutomatonKind::String {
            automaton,
            signature,
        })
    }
}

#[pyclass(name = "TagStringAlgebra", module = "rusty_alto")]
struct PyTagStringAlgebra {
    inner: Mutex<TagStringAlgebra>,
}

#[pymethods]
impl PyTagStringAlgebra {
    #[new]
    fn new() -> Self {
        Self {
            inner: Mutex::new(TagStringAlgebra::new()),
        }
    }

    fn parse(&self, text: &str) -> Vec<String> {
        text.split_whitespace().map(str::to_owned).collect()
    }

    fn decompose(&self, text: &str) -> PyResult<PyAutomaton> {
        let mut algebra = self.inner.lock().unwrap();
        let value = algebra.parse_string(text);
        let automaton = algebra
            .decompose(value)
            .ok_or_else(|| value_error("TAG input must be a contiguous string"))?;
        let signature = Arc::new(algebra.signature().clone());
        Ok(PyAutomaton::from_kind(AutomatonKind::TagString {
            automaton,
            signature,
        }))
    }
}

#[pyclass(name = "TagTreeAlgebra", module = "rusty_alto")]
struct PyTagTreeAlgebra {
    inner: Mutex<TagTreeAlgebra>,
}

#[pymethods]
impl PyTagTreeAlgebra {
    #[new]
    #[pyo3(signature = (signature, with_arities=false))]
    fn new(signature: &PySignature, with_arities: bool) -> Self {
        let algebra = if with_arities {
            TagTreeAlgebra::with_arities((*signature.inner).clone())
        } else {
            TagTreeAlgebra::tree((*signature.inner).clone())
        };
        Self {
            inner: Mutex::new(algebra),
        }
    }

    fn decompose(&self, text: &str) -> PyResult<PyAutomaton> {
        let mut algebra = self.inner.lock().unwrap();
        let value = algebra.parse_object(text).map_err(value_error)?;
        let automaton = algebra.decompose(value);
        let signature = Arc::new(algebra.signature().clone());
        Ok(PyAutomaton::from_kind(AutomatonKind::TagTree {
            automaton,
            signature,
        }))
    }
}

#[pyclass(name = "BinarizingTagTreeAlgebra", module = "rusty_alto")]
struct PyBinarizingTagTreeAlgebra {
    inner: Mutex<Binarizing<TagTreeAlgebra>>,
}

#[pymethods]
impl PyBinarizingTagTreeAlgebra {
    #[new]
    #[pyo3(signature = (signature, with_arities=false))]
    fn new(signature: &PySignature, with_arities: bool) -> PyResult<Self> {
        let mut signature = (*signature.inner).clone();
        let append = signature
            .intern(APPEND_SYMBOL.to_owned(), 2)
            .map_err(value_error)?;
        let inner = if with_arities {
            TagTreeAlgebra::with_arities(signature)
        } else {
            TagTreeAlgebra::tree(signature)
        };
        Ok(Self {
            inner: Mutex::new(Binarizing::new(inner, Some(append))),
        })
    }

    fn decompose(&self, text: &str) -> PyResult<PyAutomaton> {
        let mut algebra = self.inner.lock().unwrap();
        let value = algebra.parse_object(text).map_err(value_error)?;
        let inner = algebra.inner().decompose_binarized(value);
        let append = algebra
            .append_symbol()
            .ok_or_else(|| runtime_error("binarizing algebra has no append symbol"))?;
        let automaton = BinarizedTagTreeDecompositionAutomaton::new(inner, append);
        let signature = Arc::new(algebra.signature().clone());
        Ok(PyAutomaton::from_kind(AutomatonKind::BinarizedTagTree {
            automaton,
            signature,
        }))
    }
}

#[pyclass(
    name = "FeatureStructure",
    frozen,
    from_py_object,
    module = "rusty_alto"
)]
#[derive(Clone)]
struct PyFeatureStructure {
    inner: FeatureStructure,
}

#[pymethods]
impl PyFeatureStructure {
    #[staticmethod]
    fn parse(text: &str) -> PyResult<Self> {
        Ok(Self {
            inner: FeatureStructure::parse(text).map_err(value_error)?,
        })
    }

    fn unify(&self, other: &Self) -> Option<Self> {
        self.inner.unify(&other.inner).map(|inner| Self { inner })
    }

    fn project(&self, attribute: &str) -> Option<Self> {
        self.inner.project(attribute).map(|inner| Self { inner })
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }
}

#[pyclass(name = "FeatureStructureAlgebra", module = "rusty_alto")]
struct PyFeatureStructureAlgebra;

#[pymethods]
impl PyFeatureStructureAlgebra {
    #[new]
    fn new() -> Self {
        Self
    }

    fn parse(&self, text: &str) -> PyResult<PyFeatureStructure> {
        PyFeatureStructure::parse(text)
    }
}

#[pyclass(name = "WeightedTree", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyWeightedTree {
    #[pyo3(get)]
    tree: PyTree,
    #[pyo3(get)]
    weight: f64,
    #[pyo3(get)]
    score: f64,
}

fn resolved_viterbi(signature: &Signature, value: ViterbiTree) -> PyWeightedTree {
    let (arena, root) = signature.resolve_tree(value.arena(), value.root());
    PyWeightedTree {
        tree: PyTree::from_arena(&arena, root),
        weight: value.weight(),
        score: value.score(),
    }
}

#[pyclass(
    name = "InterpretationValue",
    frozen,
    from_py_object,
    module = "rusty_alto"
)]
#[derive(Clone)]
struct PyInterpretationValue {
    #[pyo3(get)]
    interpretation: String,
    #[pyo3(get)]
    text: String,
}

#[pyclass(name = "ParseControl", from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyParseControl {
    inner: ParseControl,
}

#[pymethods]
impl PyParseControl {
    #[new]
    fn new() -> Self {
        Self {
            inner: ParseControl::new(),
        }
    }

    fn cancel(&self) {
        self.inner.cancel();
    }

    #[getter]
    fn is_cancelled(&self) -> bool {
        self.inner.is_cancelled()
    }
}

#[pyclass(name = "Interpretation", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyInterpretation {
    irtg: Arc<Irtg>,
    name: String,
}

#[pymethods]
impl PyInterpretation {
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    #[getter]
    fn class_name(&self) -> PyResult<String> {
        Ok(self
            .irtg
            .interpretation_ref(&self.name)
            .ok_or_else(|| runtime_error("interpretation no longer exists"))?
            .class_name()
            .to_owned())
    }

    #[getter]
    fn is_inputable(&self) -> PyResult<bool> {
        Ok(self
            .irtg
            .interpretation_ref(&self.name)
            .ok_or_else(|| runtime_error("interpretation no longer exists"))?
            .is_inputable())
    }

    #[getter]
    fn signature(&self) -> PyResult<PySignature> {
        Ok(PySignature {
            inner: Arc::new(
                self.irtg
                    .interpretation_ref(&self.name)
                    .ok_or_else(|| runtime_error("interpretation no longer exists"))?
                    .algebra_signature()
                    .clone(),
            ),
        })
    }

    fn parse(&self, text: String) -> PyResult<PyInterpretationValue> {
        self.irtg
            .interpretation_ref(&self.name)
            .ok_or_else(|| runtime_error("interpretation no longer exists"))?
            .parse_object_erased(&text)
            .map_err(runtime_error)?;
        Ok(PyInterpretationValue {
            interpretation: self.name.clone(),
            text,
        })
    }

    fn decompose(&self, text: &str) -> PyResult<PyAutomaton> {
        let interpretation = self
            .irtg
            .interpretation_ref(&self.name)
            .ok_or_else(|| runtime_error("interpretation no longer exists"))?;
        let signature = Arc::new(interpretation.algebra_signature().clone());
        let kind = match interpretation
            .decompose_object(text)
            .map_err(runtime_error)?
        {
            DecompositionAutomaton::String(automaton) => AutomatonKind::String {
                automaton,
                signature,
            },
            DecompositionAutomaton::TagString(automaton) => AutomatonKind::TagString {
                automaton,
                signature,
            },
            DecompositionAutomaton::TagTree(automaton) => AutomatonKind::TagTree {
                automaton,
                signature,
            },
            DecompositionAutomaton::BinarizedTagTree(automaton) => {
                AutomatonKind::BinarizedTagTree {
                    automaton,
                    signature,
                }
            }
        };
        Ok(PyAutomaton::from_kind(kind))
    }
}

#[pyclass(name = "Irtg", frozen, from_py_object, module = "rusty_alto")]
#[derive(Clone)]
struct PyIrtg {
    inner: Arc<Irtg>,
}

fn parse_strategy(name: &str) -> PyResult<MaterializationStrategy<'static>> {
    match name {
        "top_down" | "top-down" | "top_down_condensed" => {
            Ok(MaterializationStrategy::TopDownCondensed)
        }
        "indexed" | "indexed_condensed" => Ok(MaterializationStrategy::IndexedCondensed),
        "astar" | "astar_zero" => Ok(MaterializationStrategy::Astar {
            heuristic: AstarHeuristic::Zero,
            options: AstarOptions {
                stop_at_first_goal: false,
                beam: None,
            },
        }),
        _ => Err(value_error(format!("unknown parse strategy {name:?}"))),
    }
}

fn chart_automaton(irtg: &Irtg, chart: &rusty_alto::ParseChart) -> PyAutomaton {
    PyAutomaton::from_kind(AutomatonKind::Explicit(NamedExplicit {
        automaton: chart.automaton.clone(),
        signature: Arc::new(irtg.grammar_signature().clone()),
        state_names: Arc::new(chart.state_names.clone()),
    }))
}

fn input_texts(inputs: &Bound<'_, PyDict>) -> PyResult<Vec<(String, String)>> {
    inputs
        .iter()
        .map(|(name, value)| {
            let name = name.extract::<String>()?;
            if let Ok(text) = value.extract::<String>() {
                return Ok((name, text));
            }
            let parsed = value.extract::<PyRef<'_, PyInterpretationValue>>()?;
            if parsed.interpretation != name {
                return Err(value_error(format!(
                    "value for {name:?} was parsed by interpretation {:?}",
                    parsed.interpretation
                )));
            }
            Ok((name, parsed.text.clone()))
        })
        .collect()
}

#[pymethods]
impl PyIrtg {
    #[staticmethod]
    fn load(path: &str) -> PyResult<Self> {
        let registry = InputCodecRegistry::standard();
        let inner = registry
            .codec_for_path::<Irtg>(Path::new(path))
            .and_then(|codec| codec.read_path(Path::new(path)))
            .map_err(runtime_error)?;
        Ok(Self {
            inner: Arc::new(inner),
        })
    }

    #[staticmethod]
    fn from_string(text: &str) -> PyResult<Self> {
        Ok(Self {
            inner: Arc::new(parse_irtg(text.as_bytes()).map_err(runtime_error)?),
        })
    }

    fn interpretations(&self) -> Vec<PyInterpretation> {
        self.inner
            .interpretation_info()
            .into_iter()
            .map(|info| PyInterpretation {
                irtg: self.inner.clone(),
                name: info.name,
            })
            .collect()
    }

    fn interpretation(&self, name: &str) -> PyResult<PyInterpretation> {
        if self.inner.interpretation_ref(name).is_none() {
            return Err(value_error(format!("unknown interpretation {name:?}")));
        }
        Ok(PyInterpretation {
            irtg: self.inner.clone(),
            name: name.to_owned(),
        })
    }

    #[getter]
    fn grammar(&self) -> PyAutomaton {
        let names = (0..self.inner.grammar().num_states())
            .map(|raw| self.inner.states().resolve(StateId(raw)).clone())
            .collect();
        PyAutomaton::from_kind(AutomatonKind::Explicit(NamedExplicit {
            automaton: self.inner.grammar().clone(),
            signature: Arc::new(self.inner.grammar_signature().clone()),
            state_names: Arc::new(names),
        }))
    }

    #[pyo3(signature = (inputs, strategy="top_down", control=None))]
    fn parse(
        &self,
        py: Python<'_>,
        inputs: &Bound<'_, PyDict>,
        strategy: &str,
        control: Option<&PyParseControl>,
    ) -> PyResult<PyParseChart> {
        let strategy = parse_strategy(strategy)?;
        let input_texts = input_texts(inputs)?;
        let mut parsed = Vec::with_capacity(inputs.len());
        for (name, text) in input_texts {
            let interpretation = self
                .inner
                .interpretation_ref(&name)
                .ok_or_else(|| value_error(format!("unknown interpretation {name:?}")))?;
            let value = interpretation
                .parse_object_erased(&text)
                .map_err(runtime_error)?;
            parsed.push(interpretation.input_erased(value));
        }
        let control = control
            .map(|control| control.inner.clone())
            .unwrap_or_default();
        let chart = py
            .detach(|| self.inner.parse_with_control(parsed, &strategy, &control))
            .map_err(runtime_error)?;
        let automaton = chart_automaton(&self.inner, &chart);
        let stats = chart
            .stats
            .iter()
            .map(|stat| {
                (
                    stat.output_states,
                    stat.output_rules,
                    stat.right_nullary_rules,
                    stat.right_indexed_queries,
                )
            })
            .collect();
        Ok(PyParseChart {
            irtg: self.inner.clone(),
            automaton,
            state_parts: chart.state_parts,
            stats,
        })
    }

    #[pyo3(signature = (inputs, strategy="top_down"))]
    fn best(
        &self,
        py: Python<'_>,
        inputs: &Bound<'_, PyDict>,
        strategy: &str,
    ) -> PyResult<Option<PyDerivation>> {
        let strategy = parse_strategy(strategy)?;
        let input_texts = input_texts(inputs)?;
        let mut parsed = Vec::with_capacity(inputs.len());
        for (name, text) in input_texts {
            let interpretation = self
                .inner
                .interpretation_ref(&name)
                .ok_or_else(|| value_error(format!("unknown interpretation {name:?}")))?;
            let value = interpretation
                .parse_object_erased(&text)
                .map_err(runtime_error)?;
            parsed.push(interpretation.input_erased(value));
        }
        Ok(py
            .detach(|| self.inner.best_with(parsed, &strategy))
            .map_err(runtime_error)?
            .map(|tree| PyDerivation {
                irtg: self.inner.clone(),
                tree,
            }))
    }
}

#[pyclass(name = "ParseChart", frozen, module = "rusty_alto")]
struct PyParseChart {
    irtg: Arc<Irtg>,
    automaton: PyAutomaton,
    state_parts: Vec<Vec<String>>,
    stats: Vec<(usize, usize, usize, usize)>,
}

#[pymethods]
impl PyParseChart {
    #[getter]
    fn automaton(&self) -> PyAutomaton {
        self.automaton.clone()
    }

    #[getter]
    fn state_parts(&self) -> Vec<Vec<String>> {
        self.state_parts.clone()
    }

    #[getter]
    fn stats(&self) -> Vec<(usize, usize, usize, usize)> {
        self.stats.clone()
    }

    fn best(&self) -> PyResult<Option<PyDerivation>> {
        let AutomatonKind::Explicit(named) = &self.automaton.data.kind else {
            unreachable!("parse charts are explicit");
        };
        Ok(named.automaton.viterbi().map(|tree| PyDerivation {
            irtg: self.irtg.clone(),
            tree,
        }))
    }
}

#[pyclass(name = "Derivation", module = "rusty_alto")]
struct PyDerivation {
    irtg: Arc<Irtg>,
    tree: ViterbiTree,
}

#[pymethods]
impl PyDerivation {
    #[getter]
    fn weight(&self) -> f64 {
        self.tree.weight()
    }

    #[getter]
    fn score(&self) -> f64 {
        self.tree.score()
    }

    #[getter]
    fn tree(&self) -> PyTree {
        let value = self
            .irtg
            .resolve_derivation(self.tree.arena(), self.tree.root());
        PyTree::from_arena(value.arena(), value.root())
    }

    fn interpret<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        let values = self
            .irtg
            .evaluate_derivation(self.tree.arena(), self.tree.root())
            .map_err(runtime_error)?;
        let result = PyDict::new(py);
        for value in values {
            match value.value.visual() {
                VisualRepresentation::Text(text) => result.set_item(value.name, text.clone())?,
                VisualRepresentation::Tree(tree) => result.set_item(
                    value.name,
                    Py::new(py, PyTree::from_arena(tree.arena(), tree.root()))?,
                )?,
                VisualRepresentation::FeatureStructure(feature) => result.set_item(
                    value.name,
                    Py::new(
                        py,
                        PyFeatureStructure {
                            inner: feature.clone(),
                        },
                    )?,
                )?,
            }
        }
        Ok(result)
    }

    fn encode(&self, interpretation: &str, codec: &str) -> PyResult<String> {
        let values = self
            .irtg
            .evaluate_derivation(self.tree.arena(), self.tree.root())
            .map_err(runtime_error)?;
        let value = values
            .into_iter()
            .find(|value| value.name == interpretation)
            .ok_or_else(|| value_error(format!("unknown interpretation {interpretation:?}")))?;
        value.value.encode(codec).map_err(runtime_error)
    }
}

#[pyfunction]
fn load_automaton(path: &str) -> PyResult<PyAutomaton> {
    let registry = InputCodecRegistry::standard();
    let parsed: ExplicitWithSignature = registry
        .codec_for_path(Path::new(path))
        .and_then(|codec| codec.read_path(Path::new(path)))
        .map_err(runtime_error)?;
    let names = (0..parsed.automaton.num_states())
        .map(|raw| parsed.states.resolve(StateId(raw)).clone())
        .collect();
    Ok(PyAutomaton::from_kind(AutomatonKind::Explicit(
        NamedExplicit {
            automaton: parsed.automaton,
            signature: Arc::new(parsed.signature),
            state_names: Arc::new(names),
        },
    )))
}

#[pymodule]
fn _rusty_alto(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add("__version__", env!("CARGO_PKG_VERSION"))?;
    module.add("RustyAltoError", module.py().get_type::<RustyAltoError>())?;
    module.add(
        "UnsupportedOperationError",
        module.py().get_type::<UnsupportedOperationError>(),
    )?;
    module.add("StateOwnerError", module.py().get_type::<StateOwnerError>())?;
    module.add_class::<PyState>()?;
    module.add_class::<PyTree>()?;
    module.add_class::<PySignature>()?;
    module.add_class::<PyHomomorphism>()?;
    module.add_class::<PyAutomaton>()?;
    module.add_class::<PyAutomatonBuilder>()?;
    module.add_class::<PyStringAlgebra>()?;
    module.add_class::<PyTagStringAlgebra>()?;
    module.add_class::<PyTagTreeAlgebra>()?;
    module.add_class::<PyBinarizingTagTreeAlgebra>()?;
    module.add_class::<PyFeatureStructure>()?;
    module.add_class::<PyFeatureStructureAlgebra>()?;
    module.add_class::<PyWeightedTree>()?;
    module.add_class::<PyInterpretationValue>()?;
    module.add_class::<PyParseControl>()?;
    module.add_class::<PyInterpretation>()?;
    module.add_class::<PyIrtg>()?;
    module.add_class::<PyParseChart>()?;
    module.add_class::<PyDerivation>()?;
    module.add_function(wrap_pyfunction!(load_automaton, module)?)?;
    Ok(())
}
