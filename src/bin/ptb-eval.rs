//! Comparative evaluation binary for parsing strategies.
//!
//! Loads an IRTG once, then runs multiple materialization strategies on each
//! input sentence, recording timing and quality metrics in CSV format.

use rusty_alto::{
    AstarHeuristic, AstarOptions, InvHom, Irtg, LogProbabilityScorer, MaterializationStrategy,
    MinHeuristic, ObligatoryLeafTables, OutsideHeuristic, PreparedAstarGrammar, ScoredZeroHeuristic,
    StringAlgebra, StringDecompositionAutomaton, UniversalSxHeuristic,
    astar_string_one_best_with_stats_prepared, parse_irtg,
};
use std::{
    collections::HashMap,
    env,
    error::Error,
    f64,
    fs::{self, File},
    io::{self, BufRead, BufReader, Write},
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

// ---------------------------------------------------------------------------
// Strategy enum
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Strategy {
    /// Top-down condensed intersection — same algorithm as the interactive main binary.
    TopDown,
    AstarZero,
    AstarOutside,
    AstarSx,
    AstarSxF,
}

impl Strategy {
    fn name(self) -> &'static str {
        match self {
            Strategy::TopDown => "topdown",
            Strategy::AstarZero => "astar-zero",
            Strategy::AstarOutside => "astar-outside",
            Strategy::AstarSx => "astar-sx",
            Strategy::AstarSxF => "astar-sxf",
        }
    }

    fn parse(s: &str) -> Option<Self> {
        match s {
            "topdown" => Some(Strategy::TopDown),
            "astar-zero" => Some(Strategy::AstarZero),
            "astar-outside" => Some(Strategy::AstarOutside),
            "astar-sx" => Some(Strategy::AstarSx),
            "astar-sxf" => Some(Strategy::AstarSxF),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Per-sentence per-strategy record
// ---------------------------------------------------------------------------

struct Record {
    sentence_no: usize,
    strategy: Strategy,
    weight: f64,
    parse_ms: f64,
    top_ms: f64,
    total_ms: f64,
    finalized_states: usize,
    output_rules: usize,
    heap_pushes: usize,
    heap_updates: usize,
    pops: usize,
    stale_pops: usize,
    reopen_attempts: usize,
    right_indexed_queries: usize,
    right_rules_scanned: usize,
    rotated_left_join_queries: usize,
    left_rule_matches: usize,
    candidate_edges: usize,
    dominated_candidates: usize,
    finalized_candidate_discards: usize,
    f_filtered_candidates: usize,
    sibling_tuple_queries: usize,
    sibling_tuples_returned: usize,
    right_step_calls: usize,
    right_step_results: usize,
    right_step_evals: usize,
    right_step_memo_hits: usize,
    sibling_fallback_expansions: usize,
}

struct ParsedSentence {
    sentence_no: usize,
    value: Vec<rusty_alto::Symbol>,
}

impl Record {
    fn print_csv(&self) {
        println!(
            "{},{},{},{:.4},{:.4},{:.4},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
            self.sentence_no,
            self.strategy.name(),
            if self.weight.is_nan() {
                "NaN".to_owned()
            } else {
                format!("{:.10}", self.weight)
            },
            self.parse_ms,
            self.top_ms,
            self.total_ms,
            self.finalized_states,
            self.output_rules,
            self.heap_pushes,
            self.heap_updates,
            self.pops,
            self.stale_pops,
            self.reopen_attempts,
            self.right_indexed_queries,
            self.right_rules_scanned,
            self.rotated_left_join_queries,
            self.left_rule_matches,
            self.candidate_edges,
            self.dominated_candidates,
            self.finalized_candidate_discards,
            self.f_filtered_candidates,
            self.sibling_tuple_queries,
            self.sibling_tuples_returned,
            self.right_step_calls,
            self.right_step_results,
            self.sibling_fallback_expansions,
        );
    }
}

// ---------------------------------------------------------------------------
// CLI args
// ---------------------------------------------------------------------------

struct Args {
    grammar_path: String,
    sentences_path: Option<String>,
    strategies: Vec<Strategy>,
}

impl Args {
    fn parse() -> Result<Self, String> {
        let mut args = env::args().skip(1);
        let mut positional = Vec::new();
        let mut strategies: Option<Vec<Strategy>> = None;

        while let Some(arg) = args.next() {
            if arg == "--strategies" {
                let val = args
                    .next()
                    .ok_or_else(|| "--strategies requires a value".to_owned())?;
                let parsed = val
                    .split(',')
                    .map(|s| {
                        Strategy::parse(s.trim()).ok_or_else(|| {
                            format!(
                                "unknown strategy {:?}; valid: topdown,astar-zero,astar-outside,astar-sx,astar-sxf",
                                s.trim()
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                strategies = Some(parsed);
            } else if arg.starts_with("--") {
                return Err(format!("unknown flag {arg:?}"));
            } else {
                positional.push(arg);
            }
        }

        let grammar_path = positional.first().cloned().ok_or_else(|| {
            "usage: ptb-eval <grammar.irtg> [sentences.txt] [--strategies ...]".to_owned()
        })?;
        let sentences_path = positional.get(1).cloned();

        let strategies = strategies.unwrap_or_else(|| {
            vec![
                Strategy::TopDown,
                Strategy::AstarZero,
                Strategy::AstarOutside,
                Strategy::AstarSx,
            ]
        });

        Ok(Args {
            grammar_path,
            sentences_path,
            strategies,
        })
    }
}

// ---------------------------------------------------------------------------
// Per-strategy accumulator (for summary)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct StrategyAccum {
    parse_ms_values: Vec<f64>,
    total_finalized_states: usize,
    total_output_rules: usize,
    total_heap_pushes: usize,
    total_heap_updates: usize,
    total_pops: usize,
    total_stale_pops: usize,
    total_reopen_attempts: usize,
    total_right_indexed_queries: usize,
    total_right_rules_scanned: usize,
    total_rotated_left_join_queries: usize,
    total_left_rule_matches: usize,
    total_candidate_edges: usize,
    total_dominated_candidates: usize,
    total_finalized_candidate_discards: usize,
    total_f_filtered_candidates: usize,
    total_sibling_tuple_queries: usize,
    total_sibling_tuples_returned: usize,
    total_right_step_calls: usize,
    total_right_step_results: usize,
    total_right_step_evals: usize,
    total_right_step_memo_hits: usize,
    total_sibling_fallback_expansions: usize,
}

impl StrategyAccum {
    fn record(&mut self, r: &Record) {
        self.parse_ms_values.push(r.parse_ms);
        self.total_finalized_states += r.finalized_states;
        self.total_output_rules += r.output_rules;
        self.total_heap_pushes += r.heap_pushes;
        self.total_heap_updates += r.heap_updates;
        self.total_pops += r.pops;
        self.total_stale_pops += r.stale_pops;
        self.total_reopen_attempts += r.reopen_attempts;
        self.total_right_indexed_queries += r.right_indexed_queries;
        self.total_right_rules_scanned += r.right_rules_scanned;
        self.total_rotated_left_join_queries += r.rotated_left_join_queries;
        self.total_left_rule_matches += r.left_rule_matches;
        self.total_candidate_edges += r.candidate_edges;
        self.total_dominated_candidates += r.dominated_candidates;
        self.total_finalized_candidate_discards += r.finalized_candidate_discards;
        self.total_f_filtered_candidates += r.f_filtered_candidates;
        self.total_sibling_tuple_queries += r.sibling_tuple_queries;
        self.total_sibling_tuples_returned += r.sibling_tuples_returned;
        self.total_right_step_calls += r.right_step_calls;
        self.total_right_step_results += r.right_step_results;
        self.total_right_step_evals += r.right_step_evals;
        self.total_right_step_memo_hits += r.right_step_memo_hits;
        self.total_sibling_fallback_expansions += r.sibling_fallback_expansions;
    }

    fn total_parse_ms(&self) -> f64 {
        self.parse_ms_values.iter().sum()
    }

    fn median_parse_ms(&self) -> f64 {
        if self.parse_ms_values.is_empty() {
            return f64::NAN;
        }
        let mut sorted = self.parse_ms_values.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let n = sorted.len();
        if n % 2 == 1 {
            sorted[n / 2]
        } else {
            (sorted[n / 2 - 1] + sorted[n / 2]) / 2.0
        }
    }
}

// ---------------------------------------------------------------------------
// Timing helper
// ---------------------------------------------------------------------------

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

// ---------------------------------------------------------------------------
// Disk cache for UniversalSxHeuristic
// ---------------------------------------------------------------------------

/// Return the cache file path for a given grammar path and max sentence length.
/// File lives at `<grammar>.sxcache/nmax<N>.bin` next to the grammar.
fn sx_cache_path(grammar_path: &str, n_max: usize) -> PathBuf {
    let dir = PathBuf::from(format!("{grammar_path}.sxcache"));
    dir.join(format!("nmax{n_max}.bin"))
}

fn sx_cache_dir(grammar_path: &str) -> PathBuf {
    PathBuf::from(format!("{grammar_path}.sxcache"))
}

fn parse_sx_cache_nmax(path: &Path) -> Option<usize> {
    let stem = path.file_stem()?.to_str()?;
    stem.strip_prefix("nmax")?.parse().ok()
}

/// Try to load a `UniversalSxHeuristic` from disk. Returns `None` on any I/O or format error.
fn sx_load(path: &Path) -> Option<UniversalSxHeuristic> {
    let bytes = fs::read(path).ok()?;
    UniversalSxHeuristic::from_bytes(&bytes)
}

fn sx_load_covering(
    grammar_path: &str,
    n_needed: usize,
) -> Option<(UniversalSxHeuristic, PathBuf)> {
    let exact_path = sx_cache_path(grammar_path, n_needed);
    if let Some(h) = sx_load(&exact_path).filter(|h| h.n_max() >= n_needed) {
        return Some((h, exact_path));
    }

    let mut candidates = Vec::<(usize, PathBuf)>::new();
    let entries = fs::read_dir(sx_cache_dir(grammar_path)).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("bin") {
            continue;
        }
        let Some(n_max) = parse_sx_cache_nmax(&path) else {
            continue;
        };
        if n_max >= n_needed {
            candidates.push((n_max, path));
        }
    }
    candidates.sort_by_key(|(n_max, _)| *n_max);

    for (_, path) in candidates {
        if let Some(h) = sx_load(&path).filter(|h| h.n_max() >= n_needed) {
            return Some((h, path));
        }
    }
    None
}

/// Save a `UniversalSxHeuristic` to disk, creating the cache directory as needed.
fn sx_save(path: &Path, h: &UniversalSxHeuristic) {
    if let Some(dir) = path.parent() {
        if fs::create_dir_all(dir).is_err() {
            return;
        }
    }
    let _ = fs::write(path, h.to_bytes());
}

fn render_progress(strategy: Strategy, done: usize, total: usize) {
    const WIDTH: usize = 32;
    let filled = if total == 0 {
        WIDTH
    } else {
        WIDTH * done / total
    };
    let empty = WIDTH.saturating_sub(filled);
    let percent = if total == 0 { 100 } else { 100 * done / total };
    eprint!(
        "\r{:<16} [{}{}] {:>3}% ({done}/{total})",
        strategy.name(),
        "#".repeat(filled),
        ".".repeat(empty),
        percent,
    );
    let _ = io::stderr().flush();
}

// ---------------------------------------------------------------------------
// Helper: choose interpretation name (same logic as main.rs)
// ---------------------------------------------------------------------------

fn choose_string_interpretation(irtg: &Irtg) -> Option<String> {
    let names = irtg.string_interpretation_names();
    if names.is_empty() {
        return None;
    }
    names
        .iter()
        .copied()
        .find(|&name| name == "english")
        .or_else(|| names.iter().copied().find(|&name| name == "i"))
        .or_else(|| names.first().copied())
        .map(str::to_owned)
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let args = Args::parse().map_err(|e| -> Box<dyn Error> { e.into() })?;

    // --- Load grammar ---
    let load_start = Instant::now();
    let file = File::open(&args.grammar_path)?;
    let irtg = parse_irtg(file)?;
    let load_time = load_start.elapsed();
    eprintln!(
        "loaded {} in {:.2} ms",
        args.grammar_path,
        millis(load_time)
    );

    // --- Choose string interpretation ---
    let interpretation_name = choose_string_interpretation(&irtg)
        .ok_or("IRTG does not contain a supported StringAlgebra interpretation")?;
    eprintln!("using interpretation {interpretation_name:?}");

    let interpretation = irtg.interpretation::<StringAlgebra>(&interpretation_name)?;

    // --- Read all sentences up front ---
    let raw_sentences: Vec<String> = match &args.sentences_path {
        Some(path) => BufReader::new(File::open(path)?)
            .lines()
            .collect::<io::Result<_>>()?,
        None => io::stdin().lock().lines().collect::<io::Result<_>>()?,
    };

    let mut parsed_sentences = Vec::<ParsedSentence>::new();
    let mut sentence_no = 0usize;
    for line in &raw_sentences {
        let sentence = line.trim();
        if sentence.is_empty() {
            continue;
        }
        sentence_no += 1;
        match interpretation.parse_object(sentence) {
            Ok(value) => parsed_sentences.push(ParsedSentence { sentence_no, value }),
            Err(err) => eprintln!("sentence {sentence_no}: input-error={err}"),
        }
    }

    // --- CSV header ---
    println!(
        "sentence_no,strategy,score,parse_ms,top_ms,total_ms,finalized_states,output_rules,heap_pushes,heap_updates,pops,stale_pops,reopen_attempts,right_indexed_queries,right_rules_scanned,rotated_left_join_queries,left_rule_matches,candidate_edges,dominated_candidates,finalized_candidate_discards,f_filtered_candidates,sibling_tuple_queries,sibling_tuples_returned,right_step_calls,right_step_results,sibling_fallback_expansions"
    );

    let mut accums: HashMap<Strategy, StrategyAccum> = HashMap::new();
    for &s in &args.strategies {
        accums.insert(s, StrategyAccum::default());
    }
    let mut weights_by_sentence: HashMap<usize, Vec<(Strategy, f64)>> = HashMap::new();

    for &strategy in &args.strategies {
        let records = run_strategy(
            strategy,
            &irtg,
            &interpretation,
            &args.grammar_path,
            &parsed_sentences,
        );
        for record in &records {
            record.print_csv();
            let _ = io::stdout().flush();
            if let Some(accum) = accums.get_mut(&record.strategy) {
                accum.record(record);
            }
            if !record.weight.is_nan() {
                weights_by_sentence
                    .entry(record.sentence_no)
                    .or_default()
                    .push((record.strategy, record.weight));
            }
        }
    }

    check_weight_agreement(&weights_by_sentence);

    // --- Summary ---
    eprintln!();
    eprintln!("=== Summary ({} sentences) ===", parsed_sentences.len());
    eprintln!(
        "{:<16} {:>14} {:>14} {:>20} {:>14} {:>14} {:>14} {:>10}",
        "strategy",
        "total_parse_ms",
        "median_parse_ms",
        "total_finalized_states",
        "total_output_rules",
        "heap_pushes",
        "pops",
        "reopens"
    );
    for &strategy in &args.strategies {
        if let Some(accum) = accums.get(&strategy) {
            eprintln!(
                "{:<16} {:>14.2} {:>14.2} {:>20} {:>14} {:>14} {:>14} {:>10}",
                strategy.name(),
                accum.total_parse_ms(),
                accum.median_parse_ms(),
                accum.total_finalized_states,
                accum.total_output_rules,
                accum.total_heap_pushes,
                accum.total_pops,
                accum.total_reopen_attempts,
            );
            if accum.total_right_indexed_queries > 0
                || accum.total_right_rules_scanned > 0
                || accum.total_rotated_left_join_queries > 0
                || accum.total_left_rule_matches > 0
                || accum.total_candidate_edges > 0
                || accum.total_heap_updates > 0
                || accum.total_stale_pops > 0
                || accum.total_dominated_candidates > 0
                || accum.total_finalized_candidate_discards > 0
                || accum.total_f_filtered_candidates > 0
                || accum.total_sibling_tuple_queries > 0
                || accum.total_sibling_tuples_returned > 0
                || accum.total_right_step_calls > 0
                || accum.total_right_step_results > 0
                || accum.total_sibling_fallback_expansions > 0
            {
                eprintln!(
                    "{:<16} A* internals: right_queries={} right_rules={} left_joins={} left_matches={} candidates={} heap_updates={} stale_pops={} dominated={} finalized_discards={} f_filtered={} sibling_queries={} sibling_tuples={} right_steps={} right_step_evals={} right_step_memo_hits={} right_step_results={} sibling_fallbacks={}",
                    "",
                    accum.total_right_indexed_queries,
                    accum.total_right_rules_scanned,
                    accum.total_rotated_left_join_queries,
                    accum.total_left_rule_matches,
                    accum.total_candidate_edges,
                    accum.total_heap_updates,
                    accum.total_stale_pops,
                    accum.total_dominated_candidates,
                    accum.total_finalized_candidate_discards,
                    accum.total_f_filtered_candidates,
                    accum.total_sibling_tuple_queries,
                    accum.total_sibling_tuples_returned,
                    accum.total_right_step_calls,
                    accum.total_right_step_evals,
                    accum.total_right_step_memo_hits,
                    accum.total_right_step_results,
                    accum.total_sibling_fallback_expansions,
                );
            }
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Strategy runners
// ---------------------------------------------------------------------------

fn run_strategy(
    strategy: Strategy,
    irtg: &Irtg,
    interpretation: &rusty_alto::TypedInterpretation<StringAlgebra>,
    grammar_path: &str,
    sentences: &[ParsedSentence],
) -> Vec<Record> {
    let scorer = LogProbabilityScorer;
    eprintln!();
    eprintln!("=== {} ===", strategy.name());

    let total = sentences.len();
    let mut records = Vec::with_capacity(total);
    render_progress(strategy, 0, total);
    let prepared_astar = matches!(
        strategy,
        Strategy::AstarZero | Strategy::AstarOutside | Strategy::AstarSx | Strategy::AstarSxF
    )
    .then(|| PreparedAstarGrammar::new(irtg.grammar()));

    match strategy {
        Strategy::TopDown => {
            for (idx, sentence) in sentences.iter().enumerate() {
                records.push(run_chart_strategy(
                    irtg,
                    interpretation,
                    sentence.value.clone(),
                    sentence.sentence_no,
                    strategy,
                    &MaterializationStrategy::TopDownCondensed,
                    &scorer,
                ));
                render_progress(strategy, idx + 1, total);
            }
        }
        Strategy::AstarZero => {
            for (idx, sentence) in sentences.iter().enumerate() {
                records.push(run_astar_strategy(
                    irtg,
                    interpretation,
                    sentence.value.clone(),
                    sentence.sentence_no,
                    strategy,
                    prepared_astar.as_ref().expect("A* grammar was prepared"),
                    &MaterializationStrategy::Astar {
                        heuristic: AstarHeuristic::Zero,
                        options: AstarOptions {
                            stop_at_first_goal: true,
                            beam: None,
                        },
                    },
                    &scorer,
                ));
                render_progress(strategy, idx + 1, total);
            }
        }
        Strategy::AstarOutside => {
            eprint!("\r{:<16} building outside heuristic... ", strategy.name());
            let _ = io::stderr().flush();
            let setup_start = Instant::now();
            let outside = OutsideHeuristic::from_grammar_with(irtg.grammar(), &scorer);
            eprintln!("done in {:.2} ms", millis(setup_start.elapsed()));
            render_progress(strategy, 0, total);

            for (idx, sentence) in sentences.iter().enumerate() {
                records.push(run_astar_strategy(
                    irtg,
                    interpretation,
                    sentence.value.clone(),
                    sentence.sentence_no,
                    strategy,
                    prepared_astar.as_ref().expect("A* grammar was prepared"),
                    &MaterializationStrategy::Astar {
                        heuristic: AstarHeuristic::Outside(&outside),
                        options: AstarOptions {
                            stop_at_first_goal: true,
                            beam: None,
                        },
                    },
                    &scorer,
                ));
                render_progress(strategy, idx + 1, total);
            }
        }
        Strategy::AstarSx => {
            let n_max = sentences.iter().map(|s| s.value.len()).max().unwrap_or(0);
            if n_max == 0 {
                eprintln!();
                return records;
            }

            let table = if let Some((h, path)) = sx_load_covering(grammar_path, n_max) {
                eprintln!(
                    "\r{:<16} loaded SX cache n_max={} from {}",
                    strategy.name(),
                    h.n_max(),
                    path.display()
                );
                h
            } else {
                let hom = interpretation.homomorphism();
                let concat = interpretation
                    .algebra_signature()
                    .get("*")
                    .unwrap_or(rusty_alto::Symbol(0));
                eprint!("\r{:<16} SX precompute n_max={n_max}... ", strategy.name());
                let _ = io::stderr().flush();
                let setup_start = Instant::now();
                let h = UniversalSxHeuristic::new_with(irtg.grammar(), hom, concat, n_max, &scorer);
                eprintln!("done in {:.2} ms", millis(setup_start.elapsed()));
                sx_save(&sx_cache_path(grammar_path, n_max), &h);
                h
            };
            render_progress(strategy, 0, total);

            for (idx, sentence) in sentences.iter().enumerate() {
                let n = sentence.value.len();
                records.push(run_astar_strategy(
                    irtg,
                    interpretation,
                    sentence.value.clone(),
                    sentence.sentence_no,
                    strategy,
                    prepared_astar.as_ref().expect("A* grammar was prepared"),
                    &MaterializationStrategy::Astar {
                        heuristic: AstarHeuristic::UniversalSx { table: &table, n },
                        options: AstarOptions {
                            stop_at_first_goal: true,
                            beam: None,
                        },
                    },
                    &scorer,
                ));
                render_progress(strategy, idx + 1, total);
            }
        }
        Strategy::AstarSxF => {
            let n_max = sentences.iter().map(|s| s.value.len()).max().unwrap_or(0);
            if n_max == 0 {
                eprintln!();
                return records;
            }

            // SX table (reuse the on-disk cache, like astar-sx).
            let table = if let Some((h, path)) = sx_load_covering(grammar_path, n_max) {
                eprintln!(
                    "\r{:<16} loaded SX cache n_max={} from {}",
                    strategy.name(),
                    h.n_max(),
                    path.display()
                );
                h
            } else {
                let hom = interpretation.homomorphism();
                let concat = interpretation
                    .algebra_signature()
                    .get("*")
                    .unwrap_or(rusty_alto::Symbol(0));
                eprint!("\r{:<16} SX precompute n_max={n_max}... ", strategy.name());
                let _ = io::stderr().flush();
                let setup_start = Instant::now();
                let h = UniversalSxHeuristic::new_with(irtg.grammar(), hom, concat, n_max, &scorer);
                eprintln!("done in {:.2} ms", millis(setup_start.elapsed()));
                sx_save(&sx_cache_path(grammar_path, n_max), &h);
                h
            };

            // Obligatory-leaf F tables (grammar-only; this is F's whole precompute).
            eprint!("\r{:<16} building obligatory-leaf tables... ", strategy.name());
            let _ = io::stderr().flush();
            let setup_start = Instant::now();
            let oblig =
                ObligatoryLeafTables::from_grammar(irtg.grammar(), interpretation.homomorphism());
            eprintln!("done in {:.2} ms", millis(setup_start.elapsed()));
            render_progress(strategy, 0, total);

            for (idx, sentence) in sentences.iter().enumerate() {
                let n = sentence.value.len();
                records.push(run_astar_strategy(
                    irtg,
                    interpretation,
                    sentence.value.clone(),
                    sentence.sentence_no,
                    strategy,
                    prepared_astar.as_ref().expect("A* grammar was prepared"),
                    &MaterializationStrategy::Astar {
                        heuristic: AstarHeuristic::UniversalSxF {
                            table: &table,
                            oblig: &oblig,
                            n,
                        },
                        options: AstarOptions {
                            stop_at_first_goal: true,
                            beam: None,
                        },
                    },
                    &scorer,
                ));
                render_progress(strategy, idx + 1, total);
            }
        }
    }

    eprintln!();
    records
}

fn check_weight_agreement(weights_by_sentence: &HashMap<usize, Vec<(Strategy, f64)>>) {
    let mut sentence_numbers: Vec<_> = weights_by_sentence.keys().copied().collect();
    sentence_numbers.sort_unstable();

    for sentence_no in sentence_numbers {
        let weights = &weights_by_sentence[&sentence_no];
        if weights.len() <= 1 {
            continue;
        }
        let max_weight = weights
            .iter()
            .map(|(_, w)| *w)
            .fold(f64::NEG_INFINITY, f64::max);
        let min_weight = weights
            .iter()
            .map(|(_, w)| *w)
            .fold(f64::INFINITY, f64::min);
        if (max_weight - min_weight).abs() > 1e-7 {
            let details: Vec<String> = weights
                .iter()
                .map(|(strategy, weight)| format!("{}={}", strategy.name(), weight))
                .collect();
            eprintln!(
                "WARNING: sentence {sentence_no} strategies disagree on weight: {}",
                details.join(", ")
            );
        }
    }
}

fn run_chart_strategy(
    irtg: &Irtg,
    interpretation: &rusty_alto::TypedInterpretation<StringAlgebra>,
    value: Vec<rusty_alto::Symbol>,
    sentence_no: usize,
    strategy: Strategy,
    mat_strategy: &MaterializationStrategy<'_>,
    scorer: &LogProbabilityScorer,
) -> Record {
    let input = interpretation.input(value);

    let parse_start = Instant::now();
    let chart = match irtg.parse_with([input], mat_strategy) {
        Ok(c) => c,
        Err(err) => {
            eprintln!(
                "sentence {sentence_no} {}: parse-error={err}",
                strategy.name()
            );
            return Record {
                sentence_no,
                strategy,
                weight: f64::NAN,
                parse_ms: 0.0,
                top_ms: 0.0,
                total_ms: 0.0,
                finalized_states: 0,
                output_rules: 0,
                heap_pushes: 0,
                heap_updates: 0,
                pops: 0,
                stale_pops: 0,
                reopen_attempts: 0,
                right_indexed_queries: 0,
                right_rules_scanned: 0,
                rotated_left_join_queries: 0,
                left_rule_matches: 0,
                candidate_edges: 0,
                dominated_candidates: 0,
                finalized_candidate_discards: 0,
                f_filtered_candidates: 0,
                sibling_tuple_queries: 0,
                sibling_tuples_returned: 0,
                right_step_calls: 0,
                right_step_results: 0,
                right_step_evals: 0,
                right_step_memo_hits: 0,
                sibling_fallback_expansions: 0,
            };
        }
    };
    let parse_time = parse_start.elapsed();

    // Extract stats (first intersection stats, if any).
    let (finalized_states, output_rules) = chart
        .stats
        .first()
        .map(|s| (s.output_states, s.output_rules))
        .unwrap_or((0, 0));

    let top_start = Instant::now();
    let top = chart.automaton.viterbi_with(scorer);
    let top_time = top_start.elapsed();

    let weight = top.as_ref().map_or(f64::NAN, |t| t.score());

    let parse_ms = millis(parse_time);
    let top_ms = millis(top_time);
    Record {
        sentence_no,
        strategy,
        weight,
        parse_ms,
        top_ms,
        total_ms: parse_ms + top_ms,
        finalized_states,
        output_rules,
        heap_pushes: 0,
        heap_updates: 0,
        pops: 0,
        stale_pops: 0,
        reopen_attempts: 0,
        right_indexed_queries: 0,
        right_rules_scanned: 0,
        rotated_left_join_queries: 0,
        left_rule_matches: 0,
        candidate_edges: 0,
        dominated_candidates: 0,
        finalized_candidate_discards: 0,
        f_filtered_candidates: 0,
        sibling_tuple_queries: 0,
        sibling_tuples_returned: 0,
        right_step_calls: 0,
        right_step_results: 0,
        right_step_evals: 0,
        right_step_memo_hits: 0,
        sibling_fallback_expansions: 0,
    }
}

fn run_astar_strategy(
    irtg: &Irtg,
    interpretation: &rusty_alto::TypedInterpretation<StringAlgebra>,
    value: Vec<rusty_alto::Symbol>,
    sentence_no: usize,
    strategy: Strategy,
    prepared: &PreparedAstarGrammar,
    mat_strategy: &MaterializationStrategy<'_>,
    scorer: &LogProbabilityScorer,
) -> Record {
    let concat = interpretation
        .algebra_signature()
        .get("*")
        .unwrap_or(rusty_alto::Symbol(0));
    let n = value.len();
    let decomp = StringDecompositionAutomaton::new(concat, value);
    let invhom = InvHom::new(decomp, interpretation.homomorphism());
    let options = match mat_strategy {
        MaterializationStrategy::Astar { options, .. } => AstarOptions {
            stop_at_first_goal: options.stop_at_first_goal,
            beam: options.beam,
        },
        _ => unreachable!(),
    };

    let parse_start = Instant::now();
    let (result, stats) = match mat_strategy {
        MaterializationStrategy::Astar {
            heuristic: AstarHeuristic::Zero,
            ..
        } => {
            let h = ScoredZeroHeuristic::new(scorer);
            astar_string_one_best_with_stats_prepared(irtg.grammar(), prepared, &invhom, &h, scorer)
        }
        MaterializationStrategy::Astar {
            heuristic: AstarHeuristic::Outside(h),
            ..
        } => {
            astar_string_one_best_with_stats_prepared(irtg.grammar(), prepared, &invhom, *h, scorer)
        }
        MaterializationStrategy::Astar {
            heuristic: AstarHeuristic::UniversalSx { table, n: sx_n },
            ..
        } => {
            debug_assert_eq!(*sx_n, n);
            let h = table.for_sentence(*sx_n);
            astar_string_one_best_with_stats_prepared(irtg.grammar(), prepared, &invhom, &h, scorer)
        }
        MaterializationStrategy::Astar {
            heuristic: AstarHeuristic::UniversalSxF { table, oblig, n: sx_n },
            ..
        } => {
            debug_assert_eq!(*sx_n, n);
            let sx = table.for_sentence(*sx_n);
            let f = oblig.for_sentence(invhom.inner().sentence(), scorer);
            let h = MinHeuristic::new(sx, f);
            astar_string_one_best_with_stats_prepared(irtg.grammar(), prepared, &invhom, &h, scorer)
        }
        _ => unreachable!(),
    };
    let parse_time = parse_start.elapsed();

    let weight = result.as_ref().map_or(f64::NAN, |t| t.score());
    let parse_ms = millis(parse_time);
    let _ = options;

    Record {
        sentence_no,
        strategy,
        weight,
        parse_ms,
        top_ms: 0.0,
        total_ms: parse_ms,
        finalized_states: stats.finalized_states,
        output_rules: 0,
        heap_pushes: stats.heap_pushes,
        heap_updates: stats.heap_updates,
        pops: stats.pops,
        stale_pops: stats.stale_pops,
        reopen_attempts: stats.reopen_attempts,
        right_indexed_queries: stats.right_indexed_queries,
        right_rules_scanned: stats.right_rules_scanned,
        rotated_left_join_queries: stats.rotated_left_join_queries,
        left_rule_matches: stats.left_rule_matches,
        candidate_edges: stats.candidate_edges,
        dominated_candidates: stats.dominated_candidates,
        finalized_candidate_discards: stats.finalized_candidate_discards,
        f_filtered_candidates: stats.f_filtered_candidates,
        sibling_tuple_queries: stats.sibling_tuple_queries,
        sibling_tuples_returned: stats.sibling_tuples_returned,
        right_step_calls: stats.right_step_calls,
        right_step_results: stats.right_step_results,
        right_step_evals: stats.right_step_evals,
        right_step_memo_hits: stats.right_step_memo_hits,
        sibling_fallback_expansions: stats.sibling_fallback_expansions,
    }
}
