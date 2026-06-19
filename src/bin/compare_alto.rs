//! Benchmark and correctness comparison between rusty-alto and Alto automata.

use packed_term_arena::tree::{Tree, TreeArena};
use rusty_alto::{
    BottomUpTa, DetBottomUpTa, ParsedTreeAutomaton, Signature, StateId, Symbol, parse_alto,
};
use std::collections::HashSet;
use std::env;
use std::fs;
use std::process;
use std::time::{Duration, Instant};

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = Args::parse()?;
    let auto_text = fs::read_to_string(&args.auto)
        .map_err(|e| format!("failed to read automaton {}: {e}", args.auto))?;
    let trees_text =
        fs::read_to_string(&args.trees).map_err(|e| format!("failed to read trees: {e}"))?;

    let parsed = parse_alto(&auto_text).map_err(|e| format!("failed to parse automaton: {e}"))?;
    let trees = parse_tree_file(&trees_text, &parsed)?;
    if trees.is_empty() {
        return Err("tree file did not contain any trees".to_owned());
    }
    let deterministic = is_deterministic(&parsed);

    let mut accepted = 0usize;
    let mut root_states = 0usize;
    for _ in 0..args.warmup {
        let result = if deterministic {
            run_all_det(&parsed, &trees)
        } else {
            run_all_nondet(&parsed, &trees)
        };
        accepted = result.accepted;
        root_states = result.root_states;
    }

    let start = Instant::now();
    for _ in 0..args.iterations {
        let result = if deterministic {
            run_all_det(&parsed, &trees)
        } else {
            run_all_nondet(&parsed, &trees)
        };
        accepted = result.accepted;
        root_states = result.root_states;
    }
    let elapsed = start.elapsed();
    let runs = args.iterations * trees.len();

    println!("engine=rusty-alto");
    println!("automaton={}", args.auto);
    println!("trees={}", args.trees);
    println!("tree_count={}", trees.len());
    println!("mode={}", if deterministic { "det" } else { "nondet" });
    println!("iterations={}", args.iterations);
    println!("runs={runs}");
    println!("accepted_last={accepted}");
    println!("root_states_last={root_states}");
    println!("elapsed_ms={:.3}", millis(elapsed));
    println!("ns_per_tree={:.3}", elapsed.as_nanos() as f64 / runs as f64);

    Ok(())
}

fn is_deterministic(parsed: &ParsedTreeAutomaton) -> bool {
    let mut seen = HashSet::new();
    for rule in parsed.automaton.rules() {
        if !seen.insert((rule.symbol, rule.children.to_vec())) {
            return false;
        }
    }
    true
}

fn run_all_det(parsed: &ParsedTreeAutomaton, trees: &[ParsedTree]) -> RunSummary {
    let mut accepted = 0usize;
    let mut root_states = 0usize;
    for tree in trees {
        let mut states = vec![StateId::STUCK; tree.arena.len()];
        for node in tree.postorder.iter().copied() {
            let mut child_states = Vec::with_capacity(tree.children[node].len());
            let mut any_stuck = false;
            for &child in &tree.children[node] {
                let state = states[child];
                if state.is_stuck() {
                    any_stuck = true;
                    break;
                }
                child_states.push(state);
            }
            if any_stuck {
                continue;
            }
            states[node] = parsed
                .automaton
                .step_det(tree.symbols[node], &child_states)
                .unwrap_or(StateId::STUCK);
        }

        let root = states[tree.root.index()];
        if !root.is_stuck() {
            root_states += 1;
            if parsed.automaton.is_accepting(&root) {
                accepted += 1;
            }
        }
    }
    RunSummary {
        accepted,
        root_states,
    }
}

fn run_all_nondet(parsed: &ParsedTreeAutomaton, trees: &[ParsedTree]) -> RunSummary {
    let mut accepted = 0usize;
    let mut root_states = 0usize;
    for tree in trees {
        let mut states = vec![StateSet::new(); tree.arena.len()];
        for node in tree.postorder.iter().copied() {
            let child_states: Vec<&[StateId]> = tree.children[node]
                .iter()
                .map(|&c| states[c].as_slice())
                .collect();
            if child_states.iter().any(|s| s.is_empty()) {
                continue;
            }
            let mut local = StateSet::new();
            cartesian(&child_states, |tuple| {
                parsed
                    .automaton
                    .step(tree.symbols[node], tuple, &mut |q| local.insert(q));
            });
            states[node] = local;
        }
        let root = &states[tree.root.index()];
        root_states += root.len();
        if root.iter().any(|q| parsed.automaton.is_accepting(q)) {
            accepted += 1;
        }
    }
    RunSummary {
        accepted,
        root_states,
    }
}

#[derive(Clone)]
struct StateSet(Vec<StateId>);

impl StateSet {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn insert(&mut self, q: StateId) {
        if !self.0.contains(&q) {
            self.0.push(q);
        }
    }

    fn as_slice(&self) -> &[StateId] {
        &self.0
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn iter(&self) -> impl Iterator<Item = &StateId> {
        self.0.iter()
    }
}

struct RunSummary {
    accepted: usize,
    root_states: usize,
}

struct ParsedTree {
    arena: TreeArena<Symbol>,
    root: Tree,
    symbols: Vec<Symbol>,
    children: Vec<Vec<usize>>,
    postorder: Vec<usize>,
}

fn parse_tree_file(input: &str, auto: &ParsedTreeAutomaton) -> Result<Vec<ParsedTree>, String> {
    let mut signature = auto.signature.clone();
    let mut trees = Vec::new();
    for (line_idx, line) in input.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') || trimmed.starts_with("//") {
            continue;
        }
        trees.push(
            TreeParser::new(trimmed, &mut signature)
                .parse()
                .map_err(|e| format!("tree line {}: {e}", line_idx + 1))?,
        );
    }
    Ok(trees)
}

struct TreeParser<'a, 'b> {
    input: &'a str,
    pos: usize,
    signature: &'b mut Signature,
    arena: TreeArena<Symbol>,
    symbols: Vec<Symbol>,
    children: Vec<Vec<usize>>,
}

impl<'a, 'b> TreeParser<'a, 'b> {
    fn new(input: &'a str, signature: &'b mut Signature) -> Self {
        Self {
            input,
            pos: 0,
            signature,
            arena: TreeArena::new(),
            symbols: Vec::new(),
            children: Vec::new(),
        }
    }

    fn parse(mut self) -> Result<ParsedTree, String> {
        let root = self.node()?;
        self.skip_ws();
        if !self.is_eof() {
            return Err(format!("unexpected trailing input at byte {}", self.pos));
        }

        let mut postorder = Vec::new();
        collect_postorder(root.index(), &self.children, &mut postorder);
        Ok(ParsedTree {
            arena: self.arena,
            root,
            symbols: self.symbols,
            children: self.children,
            postorder,
        })
    }

    fn node(&mut self) -> Result<Tree, String> {
        self.skip_ws();
        let label = self.name()?;
        self.skip_ws();
        let mut children = Vec::new();
        if self.eat('(') {
            self.skip_ws();
            if !self.eat(')') {
                loop {
                    children.push(self.node()?);
                    self.skip_ws();
                    if self.eat(',') {
                        continue;
                    }
                    self.expect(')')?;
                    break;
                }
            }
        }

        let symbol = self.symbol_for(&label, children.len())?;
        let child_indices: Vec<usize> = children.iter().map(|node| node.index()).collect();
        let node = self.arena.add_node(symbol, children);
        self.symbols.push(symbol);
        self.children.push(child_indices);
        Ok(node)
    }

    fn symbol_for(&mut self, label: &str, arity: usize) -> Result<Symbol, String> {
        self.signature
            .intern(label.to_owned(), arity)
            .map_err(|e| e.to_string())
    }

    fn name(&mut self) -> Result<String, String> {
        self.skip_ws();
        let Some(ch) = self.peek() else {
            return Err(format!("expected tree node label at byte {}", self.pos));
        };
        if ch == '\'' || ch == '"' {
            self.bump();
            let quote = ch;
            let start = self.pos;
            let mut out = String::new();
            while let Some(c) = self.bump() {
                if c == quote {
                    return Ok(out);
                }
                out.push(c);
            }
            Err(format!(
                "unterminated quoted label starting at byte {start}"
            ))
        } else {
            let start = self.pos;
            let mut out = String::new();
            while let Some(c) = self.peek() {
                if c.is_whitespace() || matches!(c, '(' | ')' | ',') {
                    break;
                }
                out.push(c);
                self.bump();
            }
            if out.is_empty() {
                Err(format!("expected tree node label at byte {start}"))
            } else {
                Ok(out)
            }
        }
    }

    fn expect(&mut self, expected: char) -> Result<(), String> {
        if self.eat(expected) {
            Ok(())
        } else {
            Err(format!("expected {expected:?} at byte {}", self.pos))
        }
    }

    fn eat(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn skip_ws(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.bump();
        }
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }
}

fn collect_postorder(node: usize, children: &[Vec<usize>], out: &mut Vec<usize>) {
    for &child in &children[node] {
        collect_postorder(child, children, out);
    }
    out.push(node);
}

fn cartesian<T: Copy>(pools: &[&[T]], mut f: impl FnMut(&[T])) {
    if pools.iter().any(|pool| pool.is_empty()) {
        return;
    }
    if pools.is_empty() {
        f(&[]);
        return;
    }

    let mut indices = vec![0; pools.len()];
    let mut tuple: Vec<T> = pools.iter().map(|pool| pool[0]).collect();
    loop {
        f(&tuple);
        let mut pos = pools.len();
        loop {
            if pos == 0 {
                return;
            }
            pos -= 1;
            indices[pos] += 1;
            if indices[pos] < pools[pos].len() {
                tuple[pos] = pools[pos][indices[pos]];
                for reset in pos + 1..pools.len() {
                    indices[reset] = 0;
                    tuple[reset] = pools[reset][0];
                }
                break;
            }
        }
    }
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

struct Args {
    auto: String,
    trees: String,
    iterations: usize,
    warmup: usize,
}

impl Args {
    fn parse() -> Result<Self, String> {
        let mut auto = None;
        let mut trees = None;
        let mut iterations = 100usize;
        let mut warmup = 10usize;
        let mut args = env::args().skip(1);

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--auto" => auto = args.next(),
                "--trees" => trees = args.next(),
                "--iterations" => {
                    iterations = args
                        .next()
                        .ok_or("--iterations requires a value")?
                        .parse()
                        .map_err(|_| "--iterations must be a positive integer")?;
                }
                "--warmup" => {
                    warmup = args
                        .next()
                        .ok_or("--warmup requires a value")?
                        .parse()
                        .map_err(|_| "--warmup must be a non-negative integer")?;
                }
                "--help" | "-h" => {
                    return Err(usage());
                }
                other => return Err(format!("unknown argument {other:?}\n{}", usage())),
            }
        }

        Ok(Self {
            auto: auto.ok_or_else(usage)?,
            trees: trees.ok_or_else(usage)?,
            iterations,
            warmup,
        })
    }
}

fn usage() -> String {
    "usage: compare_alto --auto FILE.auto --trees TREES.txt [--iterations N] [--warmup N]"
        .to_owned()
}
