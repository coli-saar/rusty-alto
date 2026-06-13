use rusty_alto::{
    CondensedTa, Explicit, ExplicitBuilder, HomLabel, Homomorphism, InvHom, Rule, StateId,
    StateUniverse, StringDecompositionAutomaton, Symbol, SymbolSet,
    materialize_indexed_condensed_intersection,
};
use rusty_tree::tree::TreeArena;
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::env;
use std::hash::Hash;
use std::process;
use std::time::{Duration, Instant};

type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;
type FxHashSet<T> = hashbrown::HashSet<T, rustc_hash::FxBuildHasher>;
type Children = SmallVec<[StateId; 2]>;

const CONCAT: Symbol = Symbol(0);
const WORD_BASE: u32 = 1;
const LEX_BASE: u32 = 1_000;
const BIN_BASE: u32 = 10_000;

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = Args::parse()?;
    let workload = Workload::new(
        args.states,
        args.len,
        args.vocab,
        args.lexical_labels,
        args.binary_labels,
        args.decomp,
    )?;

    match workload {
        Workload::Explicit(workload) => run_workload(&args, "explicit", &workload),
        Workload::Implicit(workload) => run_workload(&args, "implicit", &workload),
    }
}

fn run_workload<A>(
    args: &Args,
    decomp_mode: &str,
    workload: &TypedWorkload<A>,
) -> Result<(), String>
where
    A: CondensedTa + StateUniverse + Clone,
    A::State: Clone + Eq + Hash,
{
    let mut last = Summary::default();
    for _ in 0..args.warmup {
        last = intersect_workload(
            args.intersection,
            &workload.left,
            &workload.decomp,
            &workload.hom,
        );
    }

    let start = Instant::now();
    for _ in 0..args.iterations {
        last = intersect_workload(
            args.intersection,
            &workload.left,
            &workload.decomp,
            &workload.hom,
        );
    }
    let elapsed = start.elapsed();

    println!("engine=rusty-alto");
    println!("algorithm=condensed-invhom");
    println!("decomp={decomp_mode}");
    println!("intersection={}", args.intersection.name());
    println!("grammar_states={}", args.states);
    println!("sentence_len={}", args.len);
    println!("vocab={}", args.vocab);
    println!("lexical_labels={}", args.lexical_labels);
    println!("binary_labels={}", args.binary_labels);
    println!("iterations={}", args.iterations);
    println!("warmup={}", args.warmup);
    println!("grammar_rules={}", workload.left_rules);
    println!("decomp_rules={}", workload.decomp_rules);
    println!("condensed_rules_last={}", last.condensed_rules);
    println!("output_states={}", last.states);
    println!("output_rules={}", last.rules);
    println!("elapsed_ms={:.3}", millis(elapsed));
    println!(
        "ns_per_parse={:.3}",
        elapsed.as_nanos() as f64 / args.iterations as f64
    );

    Ok(())
}

fn intersect_workload<A>(
    mode: IntersectionMode,
    left: &Explicit,
    decomp: &A,
    hom: &Homomorphism,
) -> Summary
where
    A: CondensedTa + StateUniverse + Clone,
    A::State: Clone + Eq + Hash,
{
    let right = InvHom::new(decomp.clone(), hom);
    match mode {
        IntersectionMode::Eager => intersect_condensed(left, &right),
        IntersectionMode::IndexedCondensed => {
            let (mat, _interner, stats) = materialize_indexed_condensed_intersection(left, &right);
            Summary {
                states: stats.output_states,
                rules: mat.rules().count(),
                condensed_rules: stats.right_queries(),
            }
        }
    }
}

struct Args {
    states: usize,
    len: usize,
    vocab: usize,
    lexical_labels: usize,
    binary_labels: usize,
    iterations: usize,
    warmup: usize,
    decomp: DecompMode,
    intersection: IntersectionMode,
}

impl Args {
    fn parse() -> Result<Self, String> {
        let mut states = 16;
        let mut len = 12;
        let mut vocab = 4;
        let mut lexical_labels = 4;
        let mut binary_labels = 16;
        let mut iterations = 10;
        let mut warmup = 2;
        let mut decomp = DecompMode::Explicit;
        let mut intersection = IntersectionMode::Eager;

        let mut args = env::args().skip(1);
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--states" => states = parse_usize(&mut args, "--states")?,
                "--len" => len = parse_usize(&mut args, "--len")?,
                "--vocab" => vocab = parse_usize(&mut args, "--vocab")?,
                "--lexical-labels" => lexical_labels = parse_usize(&mut args, "--lexical-labels")?,
                "--binary-labels" => binary_labels = parse_usize(&mut args, "--binary-labels")?,
                "--iterations" => iterations = parse_usize(&mut args, "--iterations")?,
                "--warmup" => warmup = parse_usize(&mut args, "--warmup")?,
                "--decomp" => decomp = parse_decomp(&mut args)?,
                "--intersection" => intersection = parse_intersection(&mut args)?,
                "-h" | "--help" => {
                    println!("{}", usage());
                    process::exit(0);
                }
                _ => return Err(format!("unknown argument {arg:?}\n{}", usage())),
            }
        }

        if states == 0
            || len == 0
            || vocab == 0
            || lexical_labels == 0
            || binary_labels == 0
            || iterations == 0
        {
            return Err(
                "states, len, vocab, lexical-labels, binary-labels, and iterations must be positive"
                    .to_owned(),
            );
        }

        Ok(Self {
            states,
            len,
            vocab,
            lexical_labels,
            binary_labels,
            iterations,
            warmup,
            decomp,
            intersection,
        })
    }
}

#[derive(Clone, Copy, Debug)]
enum DecompMode {
    Explicit,
    Implicit,
}

#[derive(Clone, Copy, Debug)]
enum IntersectionMode {
    Eager,
    IndexedCondensed,
}

impl IntersectionMode {
    fn name(self) -> &'static str {
        match self {
            Self::Eager => "eager",
            Self::IndexedCondensed => "indexed-condensed",
        }
    }
}

enum Workload {
    Explicit(TypedWorkload<Explicit>),
    Implicit(TypedWorkload<StringDecompositionAutomaton>),
}

struct TypedWorkload<A> {
    left: Explicit,
    decomp: A,
    hom: Homomorphism,
    left_rules: usize,
    decomp_rules: usize,
}

impl Workload {
    fn new(
        states: usize,
        len: usize,
        vocab: usize,
        lexical_labels: usize,
        binary_labels: usize,
        decomp_mode: DecompMode,
    ) -> Result<Self, String> {
        let left = grammar_automaton(states, vocab, lexical_labels, binary_labels);
        let hom = string_homomorphism(vocab, lexical_labels, binary_labels)?;
        let left_rules = left.rules().count();
        Ok(match decomp_mode {
            DecompMode::Explicit => {
                let decomp = string_decomposition_automaton(len, vocab);
                let decomp_rules = decomp.rules().count();
                Workload::Explicit(TypedWorkload {
                    left,
                    decomp,
                    hom,
                    left_rules,
                    decomp_rules,
                })
            }
            DecompMode::Implicit => {
                let decomp =
                    StringDecompositionAutomaton::new(CONCAT, sentence_symbols(len, vocab));
                let decomp_rules = decomp.rule_count();
                Workload::Implicit(TypedWorkload {
                    left,
                    decomp,
                    hom,
                    left_rules,
                    decomp_rules,
                })
            }
        })
    }
}

fn grammar_automaton(
    states: usize,
    vocab: usize,
    lexical_labels: usize,
    binary_labels: usize,
) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let qs: Vec<_> = (0..states).map(|_| builder.new_state()).collect();

    for (idx, &q) in qs.iter().enumerate() {
        if idx == 0 {
            builder.add_accepting(q);
        }
        for word in 0..vocab {
            for variant in 0..lexical_labels {
                builder.add_rule(lex_symbol(word, variant, lexical_labels), vec![], q);
            }
        }
    }

    for op in 0..binary_labels {
        let symbol = bin_symbol(op);
        for left in 0..states {
            for right in 0..states {
                let parent = (left * 31 + right * 17 + op * 13) % states;
                builder.add_rule(symbol, vec![qs[left], qs[right]], qs[parent]);
            }
        }
    }

    builder.build()
}

fn string_decomposition_automaton(len: usize, vocab: usize) -> Explicit {
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

fn sentence_symbols(len: usize, vocab: usize) -> Vec<Symbol> {
    (0..len).map(|i| word_symbol(i % vocab)).collect()
}

fn string_homomorphism(
    vocab: usize,
    lexical_labels: usize,
    binary_labels: usize,
) -> Result<Homomorphism, String> {
    let mut arena = TreeArena::new();
    let mut lexical_terms = Vec::new();
    for word in 0..vocab {
        lexical_terms.push(arena.add_node(HomLabel::Symbol(word_symbol(word)), vec![]));
    }

    let v0 = arena.add_node(HomLabel::Var(0), vec![]);
    let v1 = arena.add_node(HomLabel::Var(1), vec![]);
    let concat = arena.add_node(HomLabel::Symbol(CONCAT), vec![v0, v1]);

    let mut hom = Homomorphism::with_arena(arena);
    for (word, &term) in lexical_terms.iter().enumerate() {
        for variant in 0..lexical_labels {
            hom.add(lex_symbol(word, variant, lexical_labels), 0, term)
                .map_err(|e| e.to_string())?;
        }
    }
    for op in 0..binary_labels {
        hom.add(bin_symbol(op), 2, concat)
            .map_err(|e| e.to_string())?;
    }
    Ok(hom)
}

#[derive(Clone)]
struct OwnedRule {
    symbol: Symbol,
    children: Children,
    result: StateId,
}

impl From<Rule<'_>> for OwnedRule {
    fn from(rule: Rule<'_>) -> Self {
        Self {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
        }
    }
}

#[derive(Clone)]
struct OwnedCondensedRule<S> {
    children: SmallVec<[S; 2]>,
    symbols: SymbolSet,
    result: S,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Summary {
    states: usize,
    rules: usize,
    condensed_rules: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OutRule {
    symbol: Symbol,
    children: Children,
    result: StateId,
}

fn intersect_condensed<S>(left: &Explicit, right: &impl CondensedTa<State = S>) -> Summary
where
    S: Clone + Eq + Hash,
{
    let left_rules: Vec<_> = left.rules().map(OwnedRule::from).collect();
    let mut right_rules = Vec::new();
    right.condensed_rules(&mut |children, symbols, result| {
        right_rules.push(OwnedCondensedRule {
            children: children.iter().cloned().collect(),
            symbols: symbols.clone(),
            result,
        });
    });

    let left_index = LeftIndex::build(&left_rules);
    let right_index = RightIndex::build(&right_rules);
    let mut pairs = FxHashMap::<(StateId, S), StateId>::default();
    let mut queue = VecDeque::<(StateId, S)>::new();
    let mut rules = FxHashSet::<OutRule>::default();

    for right_rule in right_rules.iter().filter(|rule| rule.children.is_empty()) {
        for symbol in right_rule.symbols.iter() {
            let Some(left_rule_indexes) = left_index.nullary_by_symbol.get(&symbol) else {
                continue;
            };
            for &left_rule_idx in left_rule_indexes {
                let left_rule = &left_rules[left_rule_idx];
                let existed = pairs.contains_key(&(left_rule.result, right_rule.result.clone()));
                let parent = intern_pair(&mut pairs, left_rule.result, right_rule.result.clone());
                if !existed {
                    queue.push_back((left_rule.result, right_rule.result.clone()));
                }
                rules.insert(OutRule {
                    symbol,
                    children: SmallVec::new(),
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
            let left_rule = &left_rules[left_rule_idx];
            let Some(right_occurrences) = right_index
                .by_state_position
                .get(&(right_state.clone(), position))
            else {
                continue;
            };
            for &right_rule_idx in right_occurrences {
                let right_rule = &right_rules[right_rule_idx];
                if !right_rule.symbols.contains(symbol)
                    || left_rule.children.len() != right_rule.children.len()
                {
                    continue;
                }

                let mut children = Children::new();
                let mut ok = true;
                for (&lc, rc) in left_rule.children.iter().zip(&right_rule.children) {
                    if let Some(&child) = pairs.get(&(lc, rc.clone())) {
                        children.push(child);
                    } else {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }

                let existed = pairs.contains_key(&(left_rule.result, right_rule.result.clone()));
                let parent = intern_pair(&mut pairs, left_rule.result, right_rule.result.clone());
                if !existed {
                    queue.push_back((left_rule.result, right_rule.result.clone()));
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
        condensed_rules: right_rules.len(),
    }
}

#[derive(Default)]
struct LeftIndex {
    nullary_by_symbol: FxHashMap<Symbol, Vec<usize>>,
    by_state: FxHashMap<StateId, Vec<(Symbol, usize, usize)>>,
}

impl LeftIndex {
    fn build(rules: &[OwnedRule]) -> Self {
        let mut index = Self::default();
        for (rule_idx, rule) in rules.iter().enumerate() {
            if rule.children.is_empty() {
                index
                    .nullary_by_symbol
                    .entry(rule.symbol)
                    .or_default()
                    .push(rule_idx);
            }
            for (position, &child) in rule.children.iter().enumerate() {
                index
                    .by_state
                    .entry(child)
                    .or_default()
                    .push((rule.symbol, position, rule_idx));
            }
        }
        index
    }
}

struct RightIndex<S> {
    by_state_position: FxHashMap<(S, usize), Vec<usize>>,
}

impl<S> Default for RightIndex<S> {
    fn default() -> Self {
        Self {
            by_state_position: FxHashMap::default(),
        }
    }
}

impl<S> RightIndex<S>
where
    S: Clone + Eq + Hash,
{
    fn build(rules: &[OwnedCondensedRule<S>]) -> Self {
        let mut index = Self::default();
        for (rule_idx, rule) in rules.iter().enumerate() {
            for (position, child) in rule.children.iter().enumerate() {
                index
                    .by_state_position
                    .entry((child.clone(), position))
                    .or_default()
                    .push(rule_idx);
            }
        }
        index
    }
}

fn intern_pair<S>(pairs: &mut FxHashMap<(StateId, S), StateId>, left: StateId, right: S) -> StateId
where
    S: Clone + Eq + Hash,
{
    if let Some(&id) = pairs.get(&(left, right.clone())) {
        return id;
    }
    let id = StateId(pairs.len() as u32);
    pairs.insert((left, right), id);
    id
}

fn word_symbol(word: usize) -> Symbol {
    Symbol(WORD_BASE + word as u32)
}

fn lex_symbol(word: usize, variant: usize, lexical_labels: usize) -> Symbol {
    Symbol(LEX_BASE + (word * lexical_labels + variant) as u32)
}

fn bin_symbol(op: usize) -> Symbol {
    Symbol(BIN_BASE + op as u32)
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn parse_usize(args: &mut impl Iterator<Item = String>, name: &str) -> Result<usize, String> {
    next_arg(args, name)?
        .parse()
        .map_err(|e| format!("invalid value for {name}: {e}"))
}

fn parse_decomp(args: &mut impl Iterator<Item = String>) -> Result<DecompMode, String> {
    match next_arg(args, "--decomp")?.as_str() {
        "explicit" => Ok(DecompMode::Explicit),
        "implicit" => Ok(DecompMode::Implicit),
        other => Err(format!(
            "invalid value for --decomp: {other:?}; expected explicit or implicit"
        )),
    }
}

fn parse_intersection(args: &mut impl Iterator<Item = String>) -> Result<IntersectionMode, String> {
    match next_arg(args, "--intersection")?.as_str() {
        "eager" => Ok(IntersectionMode::Eager),
        "indexed-condensed" => Ok(IntersectionMode::IndexedCondensed),
        other => Err(format!(
            "invalid value for --intersection: {other:?}; expected eager or indexed-condensed"
        )),
    }
}

fn next_arg(args: &mut impl Iterator<Item = String>, name: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("missing value for {name}\n{}", usage()))
}

fn usage() -> &'static str {
    "usage: compare_condensed_parsing [--states N] [--len N] [--vocab N] [--lexical-labels N] [--binary-labels N] [--iterations N] [--warmup N] [--decomp explicit|implicit] [--intersection eager|indexed-condensed]"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexed_condensed_matches_eager_on_small_workload() {
        let Workload::Implicit(workload) =
            Workload::new(4, 5, 2, 2, 3, DecompMode::Implicit).unwrap()
        else {
            panic!("expected implicit workload");
        };

        let eager = intersect_workload(
            IntersectionMode::Eager,
            &workload.left,
            &workload.decomp,
            &workload.hom,
        );
        let indexed = intersect_workload(
            IntersectionMode::IndexedCondensed,
            &workload.left,
            &workload.decomp,
            &workload.hom,
        );

        assert_eq!(indexed.states, eager.states);
        assert_eq!(indexed.rules, eager.rules);
    }
}
