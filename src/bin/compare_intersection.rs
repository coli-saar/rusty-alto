//! Compare baseline and sibling-indexed automaton intersection algorithms.

use rusty_alto::{Explicit, ExplicitBuilder, Rule, StateId, Symbol};
use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::process;
use std::time::{Duration, Instant};

const CONCAT: Symbol = Symbol(0);

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = Args::parse()?;
    let workload = Workload::new(args.states, args.len, args.vocab);

    let mut last = Summary::default();
    for _ in 0..args.warmup {
        last = match args.algorithm {
            Algorithm::Naive => intersect_naive(&workload.left, &workload.right),
            Algorithm::Sibling => intersect_sibling(&workload.left, &workload.right),
        };
    }

    let start = Instant::now();
    for _ in 0..args.iterations {
        last = match args.algorithm {
            Algorithm::Naive => intersect_naive(&workload.left, &workload.right),
            Algorithm::Sibling => intersect_sibling(&workload.left, &workload.right),
        };
    }
    let elapsed = start.elapsed();

    println!("engine=rusty-alto");
    println!("algorithm={}", args.algorithm.name());
    println!("grammar_states={}", args.states);
    println!("sentence_len={}", args.len);
    println!("vocab={}", args.vocab);
    println!("iterations={}", args.iterations);
    println!("warmup={}", args.warmup);
    println!("left_rules={}", workload.left_rules);
    println!("right_rules={}", workload.right_rules);
    println!("output_states={}", last.states);
    println!("output_rules={}", last.rules);
    println!("elapsed_ms={:.3}", millis(elapsed));
    println!(
        "ns_per_intersection={:.3}",
        elapsed.as_nanos() as f64 / args.iterations as f64
    );

    Ok(())
}

#[derive(Clone, Copy, Debug)]
enum Algorithm {
    Naive,
    Sibling,
}

impl Algorithm {
    fn parse(s: &str) -> Result<Self, String> {
        match s {
            "naive" => Ok(Self::Naive),
            "sibling" => Ok(Self::Sibling),
            _ => Err(format!(
                "unknown algorithm {s:?}; expected naive or sibling"
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Naive => "naive",
            Self::Sibling => "sibling",
        }
    }
}

struct Args {
    algorithm: Algorithm,
    states: usize,
    len: usize,
    vocab: usize,
    iterations: usize,
    warmup: usize,
}

impl Args {
    fn parse() -> Result<Self, String> {
        let mut algorithm = Algorithm::Sibling;
        let mut states = 16;
        let mut len = 12;
        let mut vocab = 4;
        let mut iterations = 100;
        let mut warmup = 10;

        let mut args = env::args().skip(1);
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--algorithm" => {
                    algorithm = Algorithm::parse(&next_arg(&mut args, "--algorithm")?)?;
                }
                "--states" => states = parse_usize(&mut args, "--states")?,
                "--len" => len = parse_usize(&mut args, "--len")?,
                "--vocab" => vocab = parse_usize(&mut args, "--vocab")?,
                "--iterations" => iterations = parse_usize(&mut args, "--iterations")?,
                "--warmup" => warmup = parse_usize(&mut args, "--warmup")?,
                "-h" | "--help" => {
                    println!("{}", usage());
                    process::exit(0);
                }
                _ => return Err(format!("unknown argument {arg:?}\n{}", usage())),
            }
        }

        if states == 0 || len == 0 || vocab == 0 || iterations == 0 {
            return Err("states, len, vocab, and iterations must be positive".to_owned());
        }

        Ok(Self {
            algorithm,
            states,
            len,
            vocab,
            iterations,
            warmup,
        })
    }
}

struct Workload {
    left: Explicit,
    right: Explicit,
    left_rules: usize,
    right_rules: usize,
}

impl Workload {
    fn new(states: usize, len: usize, vocab: usize) -> Self {
        let left = grammar_automaton(states, vocab);
        let right = span_automaton(len, vocab);
        let left_rules = left.rules().count();
        let right_rules = right.rules().count();
        Self {
            left,
            right,
            left_rules,
            right_rules,
        }
    }
}

fn grammar_automaton(states: usize, vocab: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let qs: Vec<_> = (0..states).map(|_| builder.new_state()).collect();

    for (idx, &q) in qs.iter().enumerate() {
        if idx == 0 {
            builder.add_accepting(q);
        }
        for word in 0..vocab {
            builder.add_rule(word_symbol(word), vec![], q);
        }
    }

    for left in 0..states {
        for right in 0..states {
            let parent = (left * 31 + right * 17) % states;
            builder.add_rule(CONCAT, vec![qs[left], qs[right]], qs[parent]);
        }
    }

    builder.build()
}

fn span_automaton(len: usize, vocab: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let mut spans = vec![vec![StateId::STUCK; len + 1]; len + 1];
    for (i, row) in spans.iter_mut().enumerate().take(len) {
        for cell in row.iter_mut().take(len + 1).skip(i + 1) {
            *cell = builder.new_state();
        }
    }
    builder.add_accepting(spans[0][len]);

    for i in 0..len {
        builder.add_rule(word_symbol(i % vocab), vec![], spans[i][i + 1]);
    }
    for width in 2..=len {
        for i in 0..=len - width {
            let j = i + width;
            for k in i + 1..j {
                builder.add_rule(CONCAT, vec![spans[i][k], spans[k][j]], spans[i][j]);
            }
        }
    }

    builder.build()
}

#[derive(Clone)]
struct OwnedRule {
    symbol: Symbol,
    children: Vec<StateId>,
    result: StateId,
}

impl From<Rule<'_>> for OwnedRule {
    fn from(rule: Rule<'_>) -> Self {
        Self {
            symbol: rule.symbol,
            children: rule.children.to_vec(),
            result: rule.result,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Summary {
    states: usize,
    rules: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OutRule {
    symbol: Symbol,
    children: Vec<StateId>,
    result: StateId,
}

fn intersect_naive(left: &Explicit, right: &Explicit) -> Summary {
    let left_rules: Vec<_> = left.rules().map(OwnedRule::from).collect();
    let right_rules: Vec<_> = right.rules().map(OwnedRule::from).collect();
    let mut pairs = HashMap::<(StateId, StateId), StateId>::new();
    let mut rules = HashSet::<OutRule>::new();

    let mut changed = true;
    while changed {
        changed = false;
        for l in &left_rules {
            for r in &right_rules {
                if l.symbol != r.symbol || l.children.len() != r.children.len() {
                    continue;
                }

                let mut children = Vec::with_capacity(l.children.len());
                let mut ok = true;
                for (&lc, &rc) in l.children.iter().zip(&r.children) {
                    if let Some(&child) = pairs.get(&(lc, rc)) {
                        children.push(child);
                    } else {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }

                let parent = intern_pair(&mut pairs, l.result, r.result);
                let rule = OutRule {
                    symbol: l.symbol,
                    children,
                    result: parent,
                };
                if rules.insert(rule) {
                    changed = true;
                }
            }
        }
    }

    Summary {
        states: pairs.len(),
        rules: rules.len(),
    }
}

fn intersect_sibling(left: &Explicit, right: &Explicit) -> Summary {
    let left_rules: Vec<_> = left.rules().map(OwnedRule::from).collect();
    let right_rules: Vec<_> = right.rules().map(OwnedRule::from).collect();
    let left_index = child_index(&left_rules);
    let right_index = child_index(&right_rules);
    let mut pairs = HashMap::<(StateId, StateId), StateId>::new();
    let mut queue = VecDeque::<(StateId, StateId)>::new();
    let mut rules = HashSet::<OutRule>::new();

    for l in &left_rules {
        if !l.children.is_empty() {
            continue;
        }
        for r in &right_rules {
            if r.children.is_empty() && l.symbol == r.symbol {
                let parent = intern_pair(&mut pairs, l.result, r.result);
                queue.push_back((l.result, r.result));
                rules.insert(OutRule {
                    symbol: l.symbol,
                    children: Vec::new(),
                    result: parent,
                });
            }
        }
    }

    while let Some((left_state, right_state)) = queue.pop_front() {
        let Some(left_occurrences) = left_index.by_state.get(&left_state) else {
            continue;
        };

        for &(symbol, position, left_rule_idx) in left_occurrences {
            let Some(right_rule_indexes) = right_index.by_key.get(&(symbol, position, right_state))
            else {
                continue;
            };
            let left_rule = &left_rules[left_rule_idx];
            for &right_rule_idx in right_rule_indexes {
                let right_rule = &right_rules[right_rule_idx];
                if left_rule.children.len() != right_rule.children.len() {
                    continue;
                }

                let mut children = Vec::with_capacity(left_rule.children.len());
                let mut ok = true;
                for (&lc, &rc) in left_rule.children.iter().zip(&right_rule.children) {
                    if let Some(&child) = pairs.get(&(lc, rc)) {
                        children.push(child);
                    } else {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }

                let existed = pairs.contains_key(&(left_rule.result, right_rule.result));
                let parent = intern_pair(&mut pairs, left_rule.result, right_rule.result);
                if !existed {
                    queue.push_back((left_rule.result, right_rule.result));
                }

                rules.insert(OutRule {
                    symbol,
                    children,
                    result: parent,
                });
            }
        }
    }

    Summary {
        states: pairs.len(),
        rules: rules.len(),
    }
}

#[derive(Default)]
struct ChildIndex {
    by_state: HashMap<StateId, Vec<(Symbol, usize, usize)>>,
    by_key: HashMap<(Symbol, usize, StateId), Vec<usize>>,
}

fn child_index(rules: &[OwnedRule]) -> ChildIndex {
    let mut index = ChildIndex::default();
    for (rule_idx, rule) in rules.iter().enumerate() {
        for (position, &child) in rule.children.iter().enumerate() {
            index
                .by_state
                .entry(child)
                .or_default()
                .push((rule.symbol, position, rule_idx));
            index
                .by_key
                .entry((rule.symbol, position, child))
                .or_default()
                .push(rule_idx);
        }
    }
    index
}

fn intern_pair(
    pairs: &mut HashMap<(StateId, StateId), StateId>,
    left: StateId,
    right: StateId,
) -> StateId {
    if let Some(&id) = pairs.get(&(left, right)) {
        return id;
    }
    let id = StateId(pairs.len() as u32);
    pairs.insert((left, right), id);
    id
}

fn word_symbol(word: usize) -> Symbol {
    Symbol((word + 1) as u32)
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn parse_usize(args: &mut impl Iterator<Item = String>, name: &str) -> Result<usize, String> {
    next_arg(args, name)?
        .parse()
        .map_err(|e| format!("invalid value for {name}: {e}"))
}

fn next_arg(args: &mut impl Iterator<Item = String>, name: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("missing value for {name}\n{}", usage()))
}

fn usage() -> &'static str {
    "usage: compare_intersection --algorithm naive|sibling [--states N] [--len N] [--vocab N] [--iterations N] [--warmup N]"
}
