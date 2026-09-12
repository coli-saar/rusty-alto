//! Compare condensed parsing implementations on generated string instances.

use packed_term_arena::tree::TreeArena;
use rusty_alto::{
    CondensedTa, Explicit, ExplicitBuilder, HomLabel, Homomorphism, InvHom, Rule, StateId,
    StateUniverse, StringDecompositionAutomaton, Symbol, SymbolSet,
    materialize_indexed_condensed_intersection, materialize_sibling_intersection,
};
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
        Workload::Explicit(workload) => {
            if matches!(args.intersection, IntersectionMode::Sibling) {
                return Err("sibling intersection requires the implicit decomposition".to_owned());
            }
            run_workload(&args, "explicit", &workload)
        }
        Workload::Implicit(workload) => {
            if matches!(args.intersection, IntersectionMode::Sibling) {
                run_sibling_workload(&args, &workload)
            } else {
                run_workload(&args, "implicit", &workload)
            }
        }
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
    run_benchmark(args, decomp_mode, workload, || {
        intersect_workload(
            args.intersection,
            &workload.left,
            &workload.decomp,
            &workload.hom,
        )
    })
}

fn run_sibling_workload(
    args: &Args,
    workload: &TypedWorkload<StringDecompositionAutomaton>,
) -> Result<(), String> {
    run_benchmark(args, "implicit", workload, || {
        let result = match args.intersection {
            IntersectionMode::Sibling => {
                materialize_sibling_intersection(&workload.left, &workload.decomp, &workload.hom)
            }
            _ => unreachable!("non-sibling workloads use run_workload"),
        };
        let (chart, _, _, stats) =
            result.expect("string decomposition is sibling-keyed and binary");
        Summary {
            states: chart.num_states() as usize,
            rules: chart.num_rules(),
            condensed_rules: 0,
            term_items: stats.term_items,
        }
    })
}

fn run_benchmark<A>(
    args: &Args,
    decomp_mode: &str,
    workload: &TypedWorkload<A>,
    mut intersect: impl FnMut() -> Summary,
) -> Result<(), String> {
    let mut last = Summary::default();
    for _ in 0..args.warmup {
        last = intersect();
    }

    let start = Instant::now();
    for _ in 0..args.iterations {
        last = intersect();
    }
    let elapsed = start.elapsed();

    println!("engine=rusty-alto");
    println!("algorithm={}", args.intersection.family_name());
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
    println!("term_items_last={}", last.term_items);
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
                term_items: 0,
            }
        }
        IntersectionMode::Sibling => {
            unreachable!("sibling workloads use run_sibling_workload")
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
    Sibling,
}

impl IntersectionMode {
    fn family_name(self) -> &'static str {
        match self {
            Self::Sibling => "sibling-intersection",
            Self::Eager | Self::IndexedCondensed => "condensed-invhom",
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Eager => "eager",
            Self::IndexedCondensed => "indexed-condensed",
            Self::Sibling => "sibling",
        }
    }
}

enum Workload {
    Explicit(Box<TypedWorkload<Explicit>>),
    Implicit(Box<TypedWorkload<StringDecompositionAutomaton>>),
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
                Workload::Explicit(Box::new(TypedWorkload {
                    left,
                    decomp,
                    hom,
                    left_rules,
                    decomp_rules,
                }))
            }
            DecompMode::Implicit => {
                let decomp =
                    StringDecompositionAutomaton::new(CONCAT, sentence_symbols(len, vocab));
                let decomp_rules = decomp.rule_count();
                Workload::Implicit(Box::new(TypedWorkload {
                    left,
                    decomp,
                    hom,
                    left_rules,
                    decomp_rules,
                }))
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
    term_items: usize,
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
        term_items: 0,
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
        "sibling" => Ok(IntersectionMode::Sibling),
        other => Err(format!(
            "invalid value for --intersection: {other:?}; expected eager, indexed-condensed, or sibling"
        )),
    }
}

fn next_arg(args: &mut impl Iterator<Item = String>, name: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("missing value for {name}\n{}", usage()))
}

fn usage() -> &'static str {
    "usage: compare_condensed_parsing [--states N] [--len N] [--vocab N] [--lexical-labels N] [--binary-labels N] [--iterations N] [--warmup N] [--decomp explicit|implicit] [--intersection eager|indexed-condensed|sibling]"
}

#[cfg(test)]
mod tests {
    use super::*;
    use rusty_alto::{BottomUpTa, Interner, materialize_indexed_condensed_intersection_with_pairs};

    fn normalized_chart(
        chart: &Explicit,
        right_states: &Interner<rusty_alto::algebras::Span>,
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
    fn condensed_algorithms_match_eager_and_share_rhs_items() {
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
        let invhom = InvHom::new(workload.decomp.clone(), &workload.hom);
        let (indexed_chart, indexed_states, indexed_pairs, _) =
            materialize_indexed_condensed_intersection_with_pairs(&workload.left, &invhom);
        let (sibling_chart, sibling_states, sibling_pairs, sibling_stats) =
            materialize_sibling_intersection(&workload.left, &workload.decomp, &workload.hom)
                .unwrap();

        assert_eq!(indexed.states, eager.states);
        assert_eq!(indexed.rules, eager.rules);
        assert_eq!(sibling_chart.num_states() as usize, eager.states);
        assert_eq!(sibling_chart.num_rules(), eager.rules);
        assert_eq!(
            normalized_chart(&sibling_chart, &sibling_states, &sibling_pairs),
            normalized_chart(&indexed_chart, &indexed_states, &indexed_pairs)
        );
        assert!(sibling_stats.term_items > 0);
    }
}
