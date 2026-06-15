//! Replay benchmark for A* candidate-generation joins.
//!
//! This binary intentionally lives outside the public API.  It builds a
//! sentence-specific replay dataset from the top-down condensed intersection,
//! then replays candidate-generation strategies without heap/scoring costs.

use fixedbitset::FixedBitSet;
use rusty_alto::{
    CondensedTa, CondensedTopDownTa, Explicit, Interner, InvHom, KeySet, SetTrie, StateId,
    StringAlgebra, Symbol, SymbolSet, parse_irtg,
};
use smallvec::SmallVec;
use std::{
    collections::HashSet,
    env,
    error::Error,
    fs::File,
    hash::Hash,
    io::{BufRead, BufReader},
    time::{Duration, Instant},
};

type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Strategy {
    Singleton,
    /// Query the current singleton path but skip product lookup and child
    /// reconstruction. Use this to estimate the join/result-processing split.
    SingletonJoinOnly,
    /// Same matches as `singleton`, but resolve sibling products through a
    /// right-local partner table. This is the replay variant that motivated
    /// storing product IDs in A*'s finalized partner sets.
    SingletonLocalProduct,
    /// Counts candidates without constructing child tuples. This is useful as
    /// an upper-bound experiment only; production A* still needs child tuples
    /// for agenda backpointers.
    SingletonNoAlloc,
    Batched,
    /// Kept as a rejected hypothesis: PTB sentence 4 reduced set-trie calls by
    /// roughly 600x but did not reduce wall time because result volume stayed
    /// constant.
    ExactBinary,
    /// Kept as a rejected hypothesis for PTB-like arity <= 2 grammars: it
    /// returns too many left-rule matches before sibling products are known.
    ChildNarrow,
    /// Kept as a condensed-symbol control: iterating symbols first is
    /// catastrophically slow when symbol sets are large.
    SingletonSymbols,
}

impl Strategy {
    fn name(self) -> &'static str {
        match self {
            Strategy::Singleton => "singleton",
            Strategy::SingletonJoinOnly => "singleton-join-only",
            Strategy::SingletonLocalProduct => "singleton-local-product",
            Strategy::SingletonNoAlloc => "singleton-no-alloc",
            Strategy::Batched => "batched",
            Strategy::ExactBinary => "exact-binary",
            Strategy::ChildNarrow => "child-narrow",
            Strategy::SingletonSymbols => "singleton-symbols",
        }
    }

    fn parse(s: &str) -> Option<Self> {
        match s {
            "singleton" => Some(Self::Singleton),
            "singleton-join-only" => Some(Self::SingletonJoinOnly),
            "singleton-local-product" => Some(Self::SingletonLocalProduct),
            "singleton-no-alloc" => Some(Self::SingletonNoAlloc),
            "batched" => Some(Self::Batched),
            "exact-binary" => Some(Self::ExactBinary),
            "child-narrow" => Some(Self::ChildNarrow),
            "singleton-symbols" => Some(Self::SingletonSymbols),
            _ => None,
        }
    }
}

struct Args {
    grammar_path: String,
    sentences_path: String,
    sentence_no: usize,
    max_events: Option<usize>,
    strategies: Vec<Strategy>,
}

impl Args {
    fn parse() -> Result<Self, String> {
        let mut args = env::args().skip(1);
        let grammar_path = args.next().ok_or_else(Self::usage)?;
        let sentences_path = args.next().ok_or_else(Self::usage)?;
        let mut sentence_no = 1usize;
        let mut max_events = None;
        let mut strategies = None;

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--sentence" => {
                    sentence_no = args
                        .next()
                        .ok_or_else(|| "--sentence requires a value".to_owned())?
                        .parse()
                        .map_err(|_| "--sentence must be an integer".to_owned())?;
                }
                "--max-events" => {
                    max_events = Some(
                        args.next()
                            .ok_or_else(|| "--max-events requires a value".to_owned())?
                            .parse()
                            .map_err(|_| "--max-events must be an integer".to_owned())?,
                    );
                }
                "--strategies" => {
                    let parsed = args
                        .next()
                        .ok_or_else(|| "--strategies requires a value".to_owned())?
                        .split(',')
                        .map(|s| {
                            Strategy::parse(s.trim()).ok_or_else(|| {
                                format!(
                                    "unknown strategy {:?}; valid: singleton,singleton-join-only,singleton-local-product,singleton-no-alloc,batched,exact-binary,child-narrow,singleton-symbols",
                                    s.trim()
                                )
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    strategies = Some(parsed);
                }
                _ if arg.starts_with("--") => return Err(format!("unknown flag {arg:?}")),
                _ => return Err(Self::usage()),
            }
        }

        Ok(Self {
            grammar_path,
            sentences_path,
            sentence_no,
            max_events,
            strategies: strategies.unwrap_or_else(|| {
                vec![
                    Strategy::Singleton,
                    Strategy::SingletonJoinOnly,
                    Strategy::SingletonLocalProduct,
                    Strategy::SingletonNoAlloc,
                    Strategy::Batched,
                    Strategy::ExactBinary,
                    Strategy::ChildNarrow,
                    Strategy::SingletonSymbols,
                ]
            }),
        })
    }

    fn usage() -> String {
        "usage: astar-join-replay <grammar.irtg> <sentences.txt> [--sentence N] [--max-events N] [--strategies singleton,singleton-join-only,singleton-local-product,singleton-no-alloc,batched,exact-binary,child-narrow,singleton-symbols]".to_owned()
    }
}

#[derive(Clone)]
struct LeftRule {
    symbol: Symbol,
    children: SmallVec<[StateId; 2]>,
    result: StateId,
}

#[derive(Clone)]
struct RightRule {
    children: SmallVec<[StateId; 2]>,
    symbols: SymbolSet,
    result: StateId,
}

#[derive(Clone, Copy)]
struct Event {
    product: StateId,
    left: StateId,
    right: StateId,
}

#[derive(Clone, Default)]
struct PartnerSet {
    states: Vec<StateId>,
    bits: FixedBitSet,
}

impl PartnerSet {
    fn insert(&mut self, state: StateId) -> bool {
        if self.bits.len() <= state.index() {
            self.bits.grow(state.index() + 1);
        }
        if self.bits.contains(state.index()) {
            return false;
        }
        self.bits.set(state.index(), true);
        self.states.push(state);
        true
    }

    fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    fn contains(&self, state: &StateId) -> bool {
        state.index() < self.bits.len() && self.bits.contains(state.index())
    }
}

impl KeySet<StateId> for PartnerSet {
    fn len(&self) -> usize {
        self.states.len()
    }

    fn contains(&self, key: &StateId) -> bool {
        self.contains(key)
    }

    fn for_each(&self, out: &mut dyn FnMut(&StateId)) {
        for state in &self.states {
            out(state);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ChildRuleKey {
    arity: usize,
    position: usize,
    child: StateId,
}

struct LeftIndex {
    by_state: FxHashMap<StateId, Vec<usize>>,
    by_children: SetTrie<StateId, FxHashMap<Symbol, Vec<usize>>>,
    by_rotated_children: Vec<SetTrie<StateId, FxHashMap<Symbol, Vec<usize>>>>,
    by_child: FxHashMap<ChildRuleKey, FxHashMap<Symbol, Vec<usize>>>,
}

impl LeftIndex {
    fn build(rules: &[LeftRule]) -> Self {
        let mut index = Self {
            by_state: FxHashMap::default(),
            by_children: SetTrie::new(),
            by_rotated_children: Vec::new(),
            by_child: FxHashMap::default(),
        };

        for (rule_idx, rule) in rules.iter().enumerate() {
            index
                .by_children
                .get_or_insert_with(&rule.children, FxHashMap::default)
                .entry(rule.symbol)
                .or_default()
                .push(rule_idx);
            for (position, &child) in rule.children.iter().enumerate() {
                index.by_state.entry(child).or_default().push(position);
                index
                    .by_child
                    .entry(ChildRuleKey {
                        arity: rule.children.len(),
                        position,
                        child,
                    })
                    .or_default()
                    .entry(rule.symbol)
                    .or_default()
                    .push(rule_idx);

                if index.by_rotated_children.len() <= position {
                    index
                        .by_rotated_children
                        .resize_with(position + 1, SetTrie::new);
                }
                let mut rotated = SmallVec::<[StateId; 4]>::new();
                rotated.push(child);
                rotated.extend(rule.children[..position].iter().copied());
                rotated.extend(rule.children[position + 1..].iter().copied());
                index.by_rotated_children[position]
                    .get_or_insert_with(&rotated, FxHashMap::default)
                    .entry(rule.symbol)
                    .or_default()
                    .push(rule_idx);
            }
        }

        for positions in index.by_state.values_mut() {
            positions.sort_unstable();
            positions.dedup();
        }

        index
    }

    fn extend_symbol_matches(
        symbols: &SymbolSet,
        rules_by_symbol: &FxHashMap<Symbol, Vec<usize>>,
        out: &mut Vec<usize>,
    ) {
        if symbols.len() < rules_by_symbol.len() {
            for symbol in symbols.iter() {
                if let Some(rule_indexes) = rules_by_symbol.get(&symbol) {
                    out.extend(rule_indexes.iter().copied());
                }
            }
        } else {
            for (&symbol, rule_indexes) in rules_by_symbol {
                if symbols.contains(symbol) {
                    out.extend(rule_indexes.iter().copied());
                }
            }
        }
    }

    fn extend_symbol_matches_symbol_first(
        symbols: &SymbolSet,
        rules_by_symbol: &FxHashMap<Symbol, Vec<usize>>,
        out: &mut Vec<usize>,
    ) {
        for symbol in symbols.iter() {
            if let Some(rule_indexes) = rules_by_symbol.get(&symbol) {
                out.extend(rule_indexes.iter().copied());
            }
        }
    }

    fn rule_indexes_for_sets_into<S: KeySet<StateId>>(
        &self,
        symbols: &SymbolSet,
        child_sets: &[S],
        out: &mut Vec<usize>,
    ) {
        out.clear();
        self.by_children
            .for_each_value_for_key_sets(child_sets, |rules_by_symbol| {
                Self::extend_symbol_matches(symbols, rules_by_symbol, out);
            });
    }

    fn rule_indexes_for_rotated_trigger_sets_into<S: KeySet<StateId>>(
        &self,
        trigger_position: usize,
        trigger_left: StateId,
        symbols: &SymbolSet,
        sibling_sets: &[S],
        symbol_first: bool,
        out: &mut Vec<usize>,
    ) {
        out.clear();
        let Some(trie) = self.by_rotated_children.get(trigger_position) else {
            return;
        };
        trie.for_each_value_for_prefix_and_key_sets(
            &[trigger_left],
            sibling_sets,
            |rules_by_symbol| {
                if symbol_first {
                    Self::extend_symbol_matches_symbol_first(symbols, rules_by_symbol, out);
                } else {
                    Self::extend_symbol_matches(symbols, rules_by_symbol, out);
                }
            },
        );
    }

    fn rule_indexes_for_rotated_sets_into<S: KeySet<StateId>>(
        &self,
        trigger_position: usize,
        symbols: &SymbolSet,
        rotated_sets: &[S],
        out: &mut Vec<usize>,
    ) {
        out.clear();
        let Some(trie) = self.by_rotated_children.get(trigger_position) else {
            return;
        };
        trie.for_each_value_for_key_sets(rotated_sets, |rules_by_symbol| {
            Self::extend_symbol_matches(symbols, rules_by_symbol, out);
        });
    }

    fn rule_indexes_for_exact_children_into(
        &self,
        symbols: &SymbolSet,
        children: &[StateId],
        out: &mut Vec<usize>,
    ) {
        out.clear();
        if let Some(rules_by_symbol) = self.by_children.get(children) {
            Self::extend_symbol_matches(symbols, rules_by_symbol, out);
        }
    }

    fn rule_indexes_for_child_into(
        &self,
        arity: usize,
        symbols: &SymbolSet,
        position: usize,
        child: StateId,
        out: &mut Vec<usize>,
    ) {
        out.clear();
        if let Some(rules_by_symbol) = self.by_child.get(&ChildRuleKey {
            arity,
            position,
            child,
        }) {
            Self::extend_symbol_matches(symbols, rules_by_symbol, out);
        }
        if out.len() > 1 {
            out.sort_unstable();
        }
    }
}

#[derive(Default)]
struct ProductMap {
    map: FxHashMap<(StateId, StateId), StateId>,
    by_right: Vec<FxHashMap<StateId, StateId>>,
    pairs: Vec<(StateId, StateId)>,
}

impl ProductMap {
    fn get(&self, left: StateId, right: StateId) -> Option<StateId> {
        self.map.get(&(left, right)).copied()
    }

    fn get_right_local(&self, left: StateId, right: StateId) -> Option<StateId> {
        self.by_right
            .get(right.index())
            .and_then(|partners| partners.get(&left).copied())
    }

    fn get_or_insert(&mut self, left: StateId, right: StateId) -> (StateId, bool) {
        if let Some(&id) = self.map.get(&(left, right)) {
            return (id, false);
        }
        let id = StateId(self.pairs.len() as u32);
        self.map.insert((left, right), id);
        if self.by_right.len() <= right.index() {
            self.by_right
                .resize_with(right.index() + 1, FxHashMap::default);
        }
        self.by_right[right.index()].insert(left, id);
        self.pairs.push((left, right));
        (id, true)
    }
}

struct TopdownCollector<'a, R>
where
    R: CondensedTopDownTa,
    R::State: Clone + Eq + Hash,
{
    right: &'a R,
    left_rules: &'a [LeftRule],
    left_index: &'a LeftIndex,
    right_interner: Interner<R::State>,
    products: ProductMap,
    partners: Vec<PartnerSet>,
    visited: FixedBitSet,
    matches: Vec<usize>,
}

impl<'a, R> TopdownCollector<'a, R>
where
    R: CondensedTopDownTa,
    R::State: Clone + Eq + Hash,
{
    fn new(
        _left: &'a Explicit,
        right: &'a R,
        left_rules: &'a [LeftRule],
        left_index: &'a LeftIndex,
    ) -> Self {
        Self {
            right,
            left_rules,
            left_index,
            right_interner: Interner::new(),
            products: ProductMap::default(),
            partners: Vec::new(),
            visited: FixedBitSet::new(),
            matches: Vec::new(),
        }
    }

    fn intern_right(&mut self, state: R::State) -> StateId {
        let id = self.right_interner.intern(state);
        if self.partners.len() <= id.index() {
            self.partners
                .resize_with(id.index() + 1, PartnerSet::default);
        }
        if self.visited.len() <= id.index() {
            self.visited.grow(id.index() + 1);
        }
        id
    }

    fn collect(mut self) -> ReplayData<R::State> {
        self.right.condensed_initial_states(&mut |q| {
            let q = self.intern_right(q);
            self.visit(q);
        });
        ReplayData {
            right_interner: self.right_interner,
            products: self.products,
            partners: self.partners,
        }
    }

    fn visit(&mut self, q: StateId) {
        if self.visited.contains(q.index()) {
            return;
        }
        self.visited.set(q.index(), true);

        let raw_parent = self.right_interner.resolve(q).clone();
        let mut rules = SmallVec::<[RightRule; 4]>::new();
        self.right
            .condensed_rules_by_parent(&raw_parent, &mut |symbols, children| {
                let children = children
                    .iter()
                    .cloned()
                    .map(|child| self.intern_right(child))
                    .collect();
                rules.push(RightRule {
                    children,
                    symbols: symbols.clone(),
                    result: q,
                });
            });

        for rule in &rules {
            for &child in &rule.children {
                self.visit(child);
            }
            self.process_rule(rule);
        }
    }

    fn process_rule(&mut self, right_rule: &RightRule) {
        if !right_rule.children.iter().all(|&child| {
            self.partners
                .get(child.index())
                .is_some_and(|p| !p.is_empty())
        }) && !right_rule.children.is_empty()
        {
            return;
        }

        let child_sets = right_rule
            .children
            .iter()
            .map(|&child| &self.partners[child.index()])
            .collect::<SmallVec<[&PartnerSet; 4]>>();
        self.left_index.rule_indexes_for_sets_into(
            &right_rule.symbols,
            child_sets.as_slice(),
            &mut self.matches,
        );
        drop(child_sets);
        let matches = std::mem::take(&mut self.matches);
        for &rule_idx in &matches {
            let left_rule = &self.left_rules[rule_idx];
            let mut ok = true;
            for (&left_child, &right_child) in left_rule.children.iter().zip(&right_rule.children) {
                if self.products.get(left_child, right_child).is_none() {
                    ok = false;
                    break;
                }
            }
            if ok {
                let (_, is_new) = self
                    .products
                    .get_or_insert(left_rule.result, right_rule.result);
                if is_new {
                    self.partners[right_rule.result.index()].insert(left_rule.result);
                }
            }
        }
        self.matches = matches;
    }
}

struct ReplayData<S: Clone + Eq + Hash> {
    right_interner: Interner<S>,
    products: ProductMap,
    partners: Vec<PartnerSet>,
}

struct ReplayContext<'a, R>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    right: &'a R,
    right_interner: Interner<R::State>,
    right_rules: Vec<RightRule>,
    right_by_child: FxHashMap<(usize, StateId), Vec<usize>>,
}

impl<'a, R> ReplayContext<'a, R>
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    fn new(right: &'a R, right_interner: Interner<R::State>) -> Self {
        Self {
            right,
            right_interner,
            right_rules: Vec::new(),
            right_by_child: FxHashMap::default(),
        }
    }

    fn right_rules_by_child(&mut self, position: usize, right_state: StateId) -> &[usize] {
        let key = (position, right_state);
        if !self.right_by_child.contains_key(&key) {
            let raw = self.right_interner.resolve(right_state).clone();
            let mut collected = Vec::new();
            self.right.condensed_rules_by_child(
                position,
                &raw,
                &mut |children, symbols, result| {
                    let rule_id = self.right_rules.len();
                    let children = children
                        .iter()
                        .cloned()
                        .map(|child| self.right_interner.intern(child))
                        .collect();
                    let result = self.right_interner.intern(result);
                    self.right_rules.push(RightRule {
                        children,
                        symbols: symbols.clone(),
                        result,
                    });
                    collected.push(rule_id);
                },
            );
            self.right_by_child.insert(key, collected);
        }
        self.right_by_child.get(&key).unwrap()
    }
}

#[derive(Clone, Default)]
struct ReplayStats {
    elapsed: Duration,
    events: usize,
    set_trie_calls: usize,
    right_rules_scanned: usize,
    left_rule_matches: usize,
    product_lookups: usize,
    candidate_edges: usize,
    rejected_missing: usize,
    peak_matches: usize,
}

impl ReplayStats {
    fn print(&self, strategy: Strategy, baseline: Option<&ReplayStats>) {
        let ms = self.elapsed.as_secs_f64() * 1000.0;
        let time_ratio = baseline
            .map(|b| self.elapsed.as_secs_f64() / b.elapsed.as_secs_f64().max(1e-12))
            .unwrap_or(1.0);
        let joins_per_candidate = self.set_trie_calls as f64 / self.candidate_edges.max(1) as f64;
        let matches_per_candidate =
            self.left_rule_matches as f64 / self.candidate_edges.max(1) as f64;
        let lookups_per_candidate =
            self.product_lookups as f64 / self.candidate_edges.max(1) as f64;
        println!(
            "{},{:.4},{:.3},{},{},{},{},{},{},{},{:.6},{:.6},{:.6},{}",
            strategy.name(),
            ms,
            time_ratio,
            self.events,
            self.set_trie_calls,
            self.right_rules_scanned,
            self.left_rule_matches,
            self.product_lookups,
            self.candidate_edges,
            self.rejected_missing,
            joins_per_candidate,
            matches_per_candidate,
            lookups_per_candidate,
            self.peak_matches,
        );
    }
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let args = Args::parse().map_err(|e| -> Box<dyn Error> { e.into() })?;
    let irtg = parse_irtg(File::open(&args.grammar_path)?)?;
    let interp_name = choose_string_interpretation(&irtg)
        .ok_or("IRTG does not contain a StringAlgebra interpretation")?;
    let interpretation = irtg.interpretation::<StringAlgebra>(&interp_name)?;
    let sentence = read_sentence(&args.sentences_path, args.sentence_no)?;
    let value = interpretation.parse_object(&sentence)?;

    let algebra = StringAlgebra::with_signature(interpretation.algebra_signature().clone());
    let decomp = algebra.decompose(value);
    let invhom = InvHom::new(decomp, interpretation.homomorphism());

    let left_rules = irtg
        .grammar()
        .rules()
        .map(|rule| LeftRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
        })
        .collect::<Vec<_>>();
    let left_index = LeftIndex::build(&left_rules);

    let collect_start = Instant::now();
    let replay = TopdownCollector::new(irtg.grammar(), &invhom, &left_rules, &left_index).collect();
    let collect_ms = collect_start.elapsed().as_secs_f64() * 1000.0;
    let mut events = replay
        .products
        .pairs
        .iter()
        .enumerate()
        .map(|(idx, &(left, right))| Event {
            product: StateId(idx as u32),
            left,
            right,
        })
        .collect::<Vec<_>>();
    if let Some(max_events) = args.max_events {
        events.truncate(max_events);
    }

    eprintln!(
        "dataset=topdown-full sentence={} words={} collect_ms={:.2} products={} replay_events={} right_states={}",
        args.sentence_no,
        sentence.split_whitespace().count(),
        collect_ms,
        replay.products.pairs.len(),
        events.len(),
        replay.partners.len(),
    );
    println!(
        "strategy,ms,time_ratio,events,set_trie_calls,right_rules,left_matches,product_lookups,candidates,rejected_missing,joins_per_candidate,matches_per_candidate,lookups_per_candidate,peak_matches"
    );

    let mut baseline = None;
    let mut printed = HashSet::new();
    for strategy in args.strategies {
        if !printed.insert(strategy) {
            continue;
        }
        let mut ctx = ReplayContext::new(&invhom, replay.right_interner.clone());
        let stats = run_strategy(
            strategy,
            &events,
            &replay.partners,
            &replay.products,
            &left_rules,
            &left_index,
            &mut ctx,
        );
        if strategy == Strategy::Singleton {
            baseline = Some(stats.clone());
        }
        stats.print(strategy, baseline.as_ref());
    }

    Ok(())
}

fn run_strategy<R>(
    strategy: Strategy,
    events: &[Event],
    partners: &[PartnerSet],
    products: &ProductMap,
    left_rules: &[LeftRule],
    left_index: &LeftIndex,
    ctx: &mut ReplayContext<'_, R>,
) -> ReplayStats
where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let start = Instant::now();
    let mut stats = ReplayStats {
        events: events.len(),
        ..ReplayStats::default()
    };
    match strategy {
        Strategy::Singleton => replay_singleton(
            events,
            partners,
            products,
            left_rules,
            left_index,
            ctx,
            false,
            CountMode::Standard,
            &mut stats,
        ),
        Strategy::SingletonJoinOnly => replay_singleton(
            events,
            partners,
            products,
            left_rules,
            left_index,
            ctx,
            false,
            CountMode::JoinOnly,
            &mut stats,
        ),
        Strategy::SingletonLocalProduct => replay_singleton(
            events,
            partners,
            products,
            left_rules,
            left_index,
            ctx,
            false,
            CountMode::RightLocalProduct,
            &mut stats,
        ),
        Strategy::SingletonNoAlloc => replay_singleton(
            events,
            partners,
            products,
            left_rules,
            left_index,
            ctx,
            false,
            CountMode::NoAlloc,
            &mut stats,
        ),
        Strategy::SingletonSymbols => replay_singleton(
            events,
            partners,
            products,
            left_rules,
            left_index,
            ctx,
            true,
            CountMode::Standard,
            &mut stats,
        ),
        Strategy::Batched => replay_batched(
            events, partners, products, left_rules, left_index, ctx, &mut stats,
        ),
        Strategy::ExactBinary => replay_exact_binary(
            events, partners, products, left_rules, left_index, ctx, &mut stats,
        ),
        Strategy::ChildNarrow => {
            replay_child_narrow(events, products, left_rules, left_index, ctx, &mut stats)
        }
    }
    stats.elapsed = start.elapsed();
    stats
}

#[derive(Clone, Copy)]
enum CountMode {
    Standard,
    JoinOnly,
    RightLocalProduct,
    NoAlloc,
}

fn positions_for(left_index: &LeftIndex, left: StateId) -> SmallVec<[usize; 4]> {
    left_index
        .by_state
        .get(&left)
        .map(|v| v.iter().copied().collect())
        .unwrap_or_default()
}

fn first_trigger(children: &[StateId], position: usize, product: StateId) -> bool {
    children.get(position) == Some(&product) && children[..position].iter().all(|&c| c != product)
}

fn replay_singleton<R>(
    events: &[Event],
    partners: &[PartnerSet],
    products: &ProductMap,
    left_rules: &[LeftRule],
    left_index: &LeftIndex,
    ctx: &mut ReplayContext<'_, R>,
    symbol_first: bool,
    mode: CountMode,
    stats: &mut ReplayStats,
) where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let mut matches = Vec::new();
    for event in events {
        for position in positions_for(left_index, event.left) {
            let right_rule_ids = ctx.right_rules_by_child(position, event.right).to_vec();
            for right_rule_id in right_rule_ids {
                stats.right_rules_scanned += 1;
                let right_rule = &ctx.right_rules[right_rule_id];
                if right_rule.children.is_empty() {
                    continue;
                }
                let mut sibling_sets = SmallVec::<[&PartnerSet; 4]>::new();
                let mut missing = false;
                for (child_position, &right_child) in right_rule.children.iter().enumerate() {
                    if child_position == position {
                        continue;
                    }
                    if let Some(set) = partners.get(right_child.index()).filter(|p| !p.is_empty()) {
                        sibling_sets.push(set);
                    } else {
                        missing = true;
                        break;
                    }
                }
                if missing {
                    continue;
                }
                stats.set_trie_calls += 1;
                left_index.rule_indexes_for_rotated_trigger_sets_into(
                    position,
                    event.left,
                    &right_rule.symbols,
                    sibling_sets.as_slice(),
                    symbol_first,
                    &mut matches,
                );
                stats.left_rule_matches += matches.len();
                stats.peak_matches = stats.peak_matches.max(matches.len());
                if !matches!(mode, CountMode::JoinOnly) {
                    count_candidates(
                        event, position, right_rule, &matches, products, left_rules, mode, stats,
                    );
                }
            }
        }
    }
}

fn replay_batched<R>(
    events: &[Event],
    partners: &[PartnerSet],
    products: &ProductMap,
    left_rules: &[LeftRule],
    left_index: &LeftIndex,
    ctx: &mut ReplayContext<'_, R>,
    stats: &mut ReplayStats,
) where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let mut groups = FxHashMap::<(usize, usize), PartnerSet>::default();
    let mut group_events = FxHashMap::<(usize, usize), Vec<Event>>::default();
    for event in events {
        for position in positions_for(left_index, event.left) {
            let right_rule_ids = ctx.right_rules_by_child(position, event.right).to_vec();
            for right_rule_id in right_rule_ids {
                stats.right_rules_scanned += 1;
                let key = (position, right_rule_id);
                groups.entry(key).or_default().insert(event.left);
                group_events.entry(key).or_default().push(*event);
            }
        }
    }

    let mut matches = Vec::new();
    for ((position, right_rule_id), trigger_lefts) in groups {
        let right_rule = &ctx.right_rules[right_rule_id];
        let mut rotated_sets = SmallVec::<[&PartnerSet; 4]>::new();
        rotated_sets.push(&trigger_lefts);
        let mut missing = false;
        for (child_position, &right_child) in right_rule.children.iter().enumerate() {
            if child_position == position {
                continue;
            }
            if let Some(set) = partners.get(right_child.index()).filter(|p| !p.is_empty()) {
                rotated_sets.push(set);
            } else {
                missing = true;
                break;
            }
        }
        if missing {
            continue;
        }
        stats.set_trie_calls += 1;
        left_index.rule_indexes_for_rotated_sets_into(
            position,
            &right_rule.symbols,
            rotated_sets.as_slice(),
            &mut matches,
        );
        stats.left_rule_matches += matches.len();
        stats.peak_matches = stats.peak_matches.max(matches.len());
        if let Some(events_for_group) = group_events.get(&(position, right_rule_id)) {
            let event_products = events_for_group
                .iter()
                .map(|e| ((e.left, e.right), e.product))
                .collect::<FxHashMap<_, _>>();
            for &rule_idx in &matches {
                let left_rule = &left_rules[rule_idx];
                let Some(&trigger_product) = event_products
                    .get(&(left_rule.children[position], right_rule.children[position]))
                else {
                    continue;
                };
                let event = Event {
                    product: trigger_product,
                    left: left_rule.children[position],
                    right: right_rule.children[position],
                };
                count_one_candidate(
                    &event,
                    position,
                    right_rule,
                    left_rule,
                    products,
                    CountMode::Standard,
                    stats,
                );
            }
        }
    }
}

fn replay_exact_binary<R>(
    events: &[Event],
    partners: &[PartnerSet],
    products: &ProductMap,
    left_rules: &[LeftRule],
    left_index: &LeftIndex,
    ctx: &mut ReplayContext<'_, R>,
    stats: &mut ReplayStats,
) where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let mut matches = Vec::new();
    for event in events {
        for position in positions_for(left_index, event.left) {
            let right_rule_ids = ctx.right_rules_by_child(position, event.right).to_vec();
            for right_rule_id in right_rule_ids {
                stats.right_rules_scanned += 1;
                let right_rule = &ctx.right_rules[right_rule_id];
                if right_rule.children.len() != 2 {
                    continue;
                }
                let sibling_position = 1 - position;
                let sibling_right = right_rule.children[sibling_position];
                let Some(siblings) = partners.get(sibling_right.index()) else {
                    continue;
                };
                for &sibling_left in &siblings.states {
                    let mut tuple = SmallVec::<[StateId; 2]>::new();
                    tuple.resize(2, StateId(0));
                    tuple[position] = event.left;
                    tuple[sibling_position] = sibling_left;
                    stats.set_trie_calls += 1;
                    left_index.rule_indexes_for_exact_children_into(
                        &right_rule.symbols,
                        &tuple,
                        &mut matches,
                    );
                    stats.left_rule_matches += matches.len();
                    stats.peak_matches = stats.peak_matches.max(matches.len());
                    count_candidates(
                        event,
                        position,
                        right_rule,
                        &matches,
                        products,
                        left_rules,
                        CountMode::Standard,
                        stats,
                    );
                }
            }
        }
    }
}

fn replay_child_narrow<R>(
    events: &[Event],
    products: &ProductMap,
    left_rules: &[LeftRule],
    left_index: &LeftIndex,
    ctx: &mut ReplayContext<'_, R>,
    stats: &mut ReplayStats,
) where
    R: CondensedTa,
    R::State: Clone + Eq + Hash,
{
    let mut matches = Vec::new();
    for event in events {
        for position in positions_for(left_index, event.left) {
            let right_rule_ids = ctx.right_rules_by_child(position, event.right).to_vec();
            for right_rule_id in right_rule_ids {
                stats.right_rules_scanned += 1;
                let right_rule = &ctx.right_rules[right_rule_id];
                if right_rule.children.is_empty() {
                    continue;
                }
                stats.set_trie_calls += 1;
                left_index.rule_indexes_for_child_into(
                    right_rule.children.len(),
                    &right_rule.symbols,
                    position,
                    event.left,
                    &mut matches,
                );
                stats.left_rule_matches += matches.len();
                stats.peak_matches = stats.peak_matches.max(matches.len());
                count_candidates(
                    event,
                    position,
                    right_rule,
                    &matches,
                    products,
                    left_rules,
                    CountMode::Standard,
                    stats,
                );
            }
        }
    }
}

fn count_candidates(
    event: &Event,
    position: usize,
    right_rule: &RightRule,
    matches: &[usize],
    products: &ProductMap,
    left_rules: &[LeftRule],
    mode: CountMode,
    stats: &mut ReplayStats,
) {
    for &rule_idx in matches {
        let left_rule = &left_rules[rule_idx];
        count_one_candidate(
            event, position, right_rule, left_rule, products, mode, stats,
        );
    }
}

fn count_one_candidate(
    event: &Event,
    position: usize,
    right_rule: &RightRule,
    left_rule: &LeftRule,
    products: &ProductMap,
    mode: CountMode,
    stats: &mut ReplayStats,
) {
    if matches!(mode, CountMode::NoAlloc) {
        count_one_candidate_no_alloc(event, position, right_rule, left_rule, products, stats);
        return;
    }

    let mut children = SmallVec::<[StateId; 2]>::new();
    let mut ok = true;
    for (child_position, (&left_child, &right_child)) in left_rule
        .children
        .iter()
        .zip(&right_rule.children)
        .enumerate()
    {
        if child_position == position && left_child == event.left && right_child == event.right {
            children.push(event.product);
        } else {
            stats.product_lookups += 1;
            let product = match mode {
                CountMode::RightLocalProduct => products.get_right_local(left_child, right_child),
                _ => products.get(left_child, right_child),
            };
            if let Some(product) = product {
                children.push(product);
            } else {
                ok = false;
                break;
            }
        }
    }
    if ok && first_trigger(&children, position, event.product) {
        stats.candidate_edges += 1;
    } else {
        stats.rejected_missing += 1;
    }
}

fn count_one_candidate_no_alloc(
    event: &Event,
    position: usize,
    right_rule: &RightRule,
    left_rule: &LeftRule,
    products: &ProductMap,
    stats: &mut ReplayStats,
) {
    let mut ok = true;
    let mut earlier_same_trigger_product = false;
    for (child_position, (&left_child, &right_child)) in left_rule
        .children
        .iter()
        .zip(&right_rule.children)
        .enumerate()
    {
        let product =
            if child_position == position && left_child == event.left && right_child == event.right
            {
                Some(event.product)
            } else {
                stats.product_lookups += 1;
                products.get(left_child, right_child)
            };

        let Some(product) = product else {
            ok = false;
            break;
        };
        if child_position < position && product == event.product {
            earlier_same_trigger_product = true;
        }
    }

    if ok && !earlier_same_trigger_product {
        stats.candidate_edges += 1;
    } else {
        stats.rejected_missing += 1;
    }
}

fn choose_string_interpretation(irtg: &rusty_alto::Irtg) -> Option<String> {
    let names = irtg.string_interpretation_names();
    names
        .iter()
        .copied()
        .find(|&name| name == "english")
        .or_else(|| names.iter().copied().find(|&name| name == "i"))
        .or_else(|| names.first().copied())
        .map(str::to_owned)
}

fn read_sentence(path: &str, wanted: usize) -> Result<String, Box<dyn Error>> {
    for (idx, line) in BufReader::new(File::open(path)?).lines().enumerate() {
        let line = line?;
        if idx + 1 == wanted {
            return Ok(line);
        }
    }
    Err(format!("sentence {wanted} not found in {path}").into())
}
