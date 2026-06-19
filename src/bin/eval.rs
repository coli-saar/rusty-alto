//! Evaluation frontend: parse an Alto corpus with an IRTG and write the derivation tree and
//! interpreted values to a new corpus.
//!
//! Usage:
//!   eval <grammar.irtg> <corpus|-> [-o out.corpus] [--limit N]
//!        [--algorithm exhaustive|astar] [--heuristic zero|outside|sx|sxf]
//!        [--jobs N] [--times times.csv] [--input INTERP]
//!        [--parseval INTERP] [--parseval-output FILE] [--evalb-param FILE]

use rusty_alto::{
    AstarHeuristic, AstarOptions, AstarStats, Binarizing, CorpusWriter, EvalbParams, Instance,
    Irtg, LogProbabilityScorer, MaterializationStrategy, ObligatoryLeafTables, OutsideHeuristic,
    ParsevalCounts, ParsevalSkip, PreparedAstarGrammar, Symbol, TreeAlgebra, TreeValue,
    UniversalSxHeuristic, ViterbiTree, compare_trees, count_gold, parse_irtg, read_corpus,
};
use rusty_tree::{parser::parse_tree, tree::TreeArena};
use std::{
    env,
    error::Error,
    fs::{self, File},
    io::{self, Write},
    path::{Path, PathBuf},
    process,
    sync::{Mutex, mpsc},
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use indicatif::{ProgressBar, ProgressStyle};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Algorithm {
    Exhaustive,
    Astar,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Heuristic {
    Zero,
    Outside,
    Sx,
    Sxf,
}

struct Args {
    grammar: String,
    corpus: String,
    output: Option<String>,
    limit: Option<usize>,
    algorithm: Algorithm,
    heuristic: Heuristic,
    times: Option<String>,
    astar_stats: Option<String>,
    input: Option<String>,
    parseval: Option<String>,
    parseval_output: Option<String>,
    evalb_param: Option<String>,
    jobs: usize,
}

#[derive(Clone, Copy)]
enum TreeInterpretationKind {
    Plain,
    Binarizing,
}

struct ParsedInstance {
    sentence_no: usize,
    length: usize,
    instance: Instance,
    best: Option<ViterbiTree>,
    stats: Option<AstarStats>,
    parse_ms: f64,
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let args = parse_args()?;

    let irtg = parse_irtg(File::open(&args.grammar)?)?;
    let parseval = prepare_parseval(&args, &irtg)?;

    // Read + parse all objects (respecting --limit).
    let mut corpus = if args.corpus == "-" {
        read_corpus(io::stdin().lock(), &irtg, args.limit)?
    } else {
        read_corpus(File::open(&args.corpus)?, &irtg, args.limit)?
    };
    if let Some(config) = parseval.as_ref()
        && !corpus.interpretation_order.contains(&config.interpretation)
    {
        return Err(format!(
            "corpus does not declare Parseval interpretation {:?}",
            config.interpretation
        )
        .into());
    }

    if corpus.interpretation_order.is_empty() {
        return Err("corpus declares no interpretations".into());
    }

    // Interpretations we parse from (intersect). Output-only interpretations (e.g. tree algebras)
    // are evaluated into but not used as parse inputs.
    let inputable: Vec<String> = corpus
        .interpretation_order
        .iter()
        .filter(|name| {
            irtg.interpretation_ref(name)
                .is_some_and(|interp| interp.is_inputable())
        })
        .cloned()
        .collect();
    if inputable.is_empty() {
        return Err("corpus has no inputable (string) interpretation to parse from".into());
    }

    // Primary interpretation parameterizes the SX/SXF heuristics (sentence length n).
    let primary = match &args.input {
        Some(name) => name.clone(),
        None => choose_primary(&inputable),
    };
    if (args.heuristic == Heuristic::Sx || args.heuristic == Heuristic::Sxf)
        && args.algorithm == Algorithm::Astar
        && !inputable.contains(&primary)
    {
        return Err(
            format!("input interpretation {primary:?} is not an inputable interpretation").into(),
        );
    }

    let scorer = LogProbabilityScorer;
    let prepared_astar =
        (args.algorithm == Algorithm::Astar).then(|| PreparedAstarGrammar::new(irtg.grammar()));

    // Build heuristic resources once, before the loop.
    let n_max = corpus
        .instances
        .iter()
        .map(|inst| word_count(inst.text(&primary)))
        .max()
        .unwrap_or(0);
    let outside = matches!(
        (args.algorithm, args.heuristic),
        (Algorithm::Astar, Heuristic::Outside)
    )
    .then(|| OutsideHeuristic::from_grammar_with(irtg.grammar(), &scorer));
    let sx_table = matches!(
        (args.algorithm, args.heuristic),
        (Algorithm::Astar, Heuristic::Sx) | (Algorithm::Astar, Heuristic::Sxf)
    )
    .then(|| {
        if let Some((table, path)) = sx_load_covering(&args.grammar, n_max) {
            eprintln!(
                "loaded SX cache n_max={} from {}",
                table.n_max(),
                path.display()
            );
            table
        } else {
            let interp = irtg.interpretation_ref(&primary).expect("primary present");
            let concat = interp.algebra_signature().get("*").unwrap_or(Symbol(0));
            eprintln!("building SX heuristic table (n_max={n_max})...");
            let table = UniversalSxHeuristic::new_with(
                irtg.grammar(),
                interp.homomorphism(),
                concat,
                n_max,
                &scorer,
            );
            sx_save(&sx_cache_path(&args.grammar, n_max), &table);
            table
        }
    });
    let oblig = matches!(
        (args.algorithm, args.heuristic),
        (Algorithm::Astar, Heuristic::Sxf)
    )
    .then(|| {
        let interp = irtg.interpretation_ref(&primary).expect("primary present");
        ObligatoryLeafTables::from_grammar(irtg.grammar(), interp.homomorphism())
    });

    // Output corpus writer (unbuffered; flushes per instance).
    let interpretations: Vec<(String, String)> = corpus
        .interpretation_order
        .iter()
        .map(|name| {
            let class = irtg
                .interpretation_ref(name)
                .expect("present")
                .class_name()
                .to_string();
            (name.clone(), class)
        })
        .collect();
    let comment_lines = header_comments(&args, primary.as_str());
    let output: Box<dyn Write> = match &args.output {
        Some(path) => Box::new(File::create(path)?),
        None => Box::new(io::stdout()),
    };
    let mut writer = CorpusWriter::new(output, &comment_lines, "# ", &interpretations, true)?;

    // Optional per-sentence timing CSV.
    let mut times = match &args.times {
        Some(path) => {
            let mut f = File::create(path)?;
            writeln!(
                f,
                "sentence_no,length,parsed,score,parse_ms,output_ms,total_ms"
            )?;
            f.flush()?;
            Some(f)
        }
        None => None,
    };
    let mut astar_stats = match &args.astar_stats {
        Some(path) => {
            let mut f = File::create(path)?;
            writeln!(
                f,
                "sentence_no,length,products,finalized,expanded,reopens,candidates,filtered,heuristic_cache_hits,heuristic_cache_misses,dominated,finalized_discards,heap_pushes,heap_updates,max_heap_len,heap_position_capacity,string_sibling_tuples,generic_fallback_expansions,right_step_calls,right_step_evals,right_step_memo_hits"
            )?;
            f.flush()?;
            Some(f)
        }
        None => None,
    };
    let mut parseval_report = match parseval.as_ref() {
        Some(config) => {
            let path = args.parseval_output.as_deref().unwrap_or("parseval.txt");
            let mut file = File::create(path)?;
            write_parseval_header(&mut file, &args, config)?;
            Some(file)
        }
        None => None,
    };

    // Parse progress; output and reports are written later in corpus order.
    let total = corpus.instances.len() as u64;
    let pb = ProgressBar::new(total);
    pb.set_style(
        ProgressStyle::with_template("{spinner} [{pos}/{len}] {wide_bar} {elapsed_precise} {msg}")
            .unwrap()
            .tick_chars("|/-\\ "),
    );

    let run_start = Instant::now();
    let mut parsed_count = 0usize;
    let mut parseval_total = ParsevalCounts::default();
    let mut parseval_scored = 0usize;
    let mut parseval_skipped = 0usize;

    let interp_order = corpus.interpretation_order.clone();
    let parsed_instances = parse_instances(
        std::mem::take(&mut corpus.instances),
        &irtg,
        args.algorithm,
        args.heuristic,
        outside.as_ref(),
        sx_table.as_ref(),
        oblig.as_ref(),
        prepared_astar.as_ref(),
        &scorer,
        &primary,
        args.jobs,
        &pb,
    )?;
    pb.finish_and_clear();

    let result: Result<(), Box<dyn Error>> = (|| {
        for parsed in parsed_instances {
            let ParsedInstance {
                sentence_no,
                length,
                instance,
                best,
                stats,
                parse_ms,
            } = parsed;

            let derivation = best.as_ref().map(|tree| (tree.arena(), tree.root()));
            if derivation.is_some() {
                parsed_count += 1;
            }

            if let Some(config) = parseval.as_ref() {
                let gold_text = instance.text(&config.interpretation).ok_or_else(|| {
                    format!(
                        "instance {sentence_no} has no {:?} interpretation",
                        config.interpretation
                    )
                })?;
                let mut gold_arena = TreeArena::new();
                let gold_root = parse_tree(&mut gold_arena, gold_text).map_err(|err| {
                    format!(
                        "instance {sentence_no}: cannot parse gold tree for interpretation {:?}: {err}",
                        config.interpretation
                    )
                })?;

                let score = match derivation {
                    Some((arena, root)) => {
                        let predicted =
                            evaluate_tree(&irtg, &config.interpretation, config.kind, arena, root)?;
                        compare_trees(
                            predicted.arena(),
                            predicted.root(),
                            &gold_arena,
                            gold_root,
                            &config.params,
                        )
                    }
                    None => count_gold(&gold_arena, gold_root, &config.params),
                };

                match score {
                    Ok(counts) => {
                        parseval_total.add_assign(counts);
                        parseval_scored += 1;
                        write_parseval_row(
                            parseval_report.as_mut().expect("report created"),
                            sentence_no,
                            length,
                            derivation.is_some(),
                            counts,
                        )?;
                    }
                    Err(skip) => {
                        parseval_skipped += 1;
                        write_parseval_skip(
                            parseval_report.as_mut().expect("report created"),
                            sentence_no,
                            length,
                            skip,
                        )?;
                    }
                }
            }

            let output_start = Instant::now();
            writer.write_instance(&irtg, &interp_order, derivation, &instance)?;
            let output_ms = millis(output_start.elapsed());

            if let Some(f) = times.as_mut() {
                let parsed = derivation.is_some();
                let score = best.as_ref().map(|t| t.score());
                writeln!(
                    f,
                    "{sentence_no},{length},{parsed},{},{parse_ms:.4},{output_ms:.4},{:.4}",
                    score.map(|s| s.to_string()).unwrap_or_default(),
                    parse_ms + output_ms,
                )?;
                f.flush()?;
            }
            if let (Some(f), Some(stats)) = (astar_stats.as_mut(), stats.as_ref()) {
                writeln!(
                    f,
                    "{sentence_no},{length},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
                    stats.output_states,
                    stats.finalized_states,
                    stats.expanded_states,
                    stats.reopen_attempts,
                    stats.candidate_edges,
                    stats.f_filtered_candidates,
                    stats.heuristic_cache_hits,
                    stats.heuristic_cache_misses,
                    stats.dominated_candidates,
                    stats.finalized_candidate_discards,
                    stats.heap_pushes,
                    stats.heap_updates,
                    stats.max_heap_len,
                    stats.max_heap_position_capacity,
                    stats.sibling_tuples_returned,
                    stats.sibling_fallback_expansions,
                    stats.right_step_calls,
                    stats.right_step_evals,
                    stats.right_step_memo_hits,
                )?;
                f.flush()?;
            }
        }
        Ok(())
    })();

    result?;

    eprintln!(
        "parsed {}/{} instances in {:.2}s",
        parsed_count,
        total,
        run_start.elapsed().as_secs_f64()
    );
    if let Some(report) = parseval_report.as_mut() {
        write_parseval_summary(report, parseval_total, parseval_scored, parseval_skipped)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn parse_instances(
    instances: Vec<Instance>,
    irtg: &Irtg,
    algorithm: Algorithm,
    heuristic: Heuristic,
    outside: Option<&OutsideHeuristic>,
    sx_table: Option<&UniversalSxHeuristic>,
    oblig: Option<&ObligatoryLeafTables>,
    prepared_astar: Option<&PreparedAstarGrammar>,
    scorer: &LogProbabilityScorer,
    primary: &str,
    jobs: usize,
    pb: &ProgressBar,
) -> Result<Vec<ParsedInstance>, Box<dyn Error>> {
    let count = instances.len();
    if count == 0 {
        return Ok(Vec::new());
    }

    let jobs = jobs.min(count);
    pb.set_message(format!("{jobs} worker{}", if jobs == 1 { "" } else { "s" }));

    let tasks = Mutex::new(instances.into_iter().enumerate());
    let (tx, rx) = mpsc::channel::<Result<ParsedInstance, String>>();
    let mut ordered: Vec<Option<ParsedInstance>> =
        std::iter::repeat_with(|| None).take(count).collect();
    let mut first_error = None;

    thread::scope(|scope| {
        for _ in 0..jobs {
            let tx = tx.clone();
            let tasks = &tasks;
            scope.spawn(move || {
                loop {
                    let Some((i, mut instance)) = tasks.lock().unwrap().next() else {
                        break;
                    };
                    let sentence_no = i + 1;
                    let result = (|| {
                        let length = word_count(instance.text(primary));
                        let strategy =
                            build_strategy(algorithm, heuristic, outside, sx_table, oblig, length);
                        let mut inputs = Vec::new();
                        for obj in &mut instance.objects {
                            if let Some(value) = obj.value.take() {
                                inputs.push(
                                    irtg.interpretation_ref(&obj.name)
                                        .expect("present")
                                        .input_erased(value),
                                );
                            }
                        }

                        let parse_start = Instant::now();
                        let (best, stats) = if let Some(prepared) = prepared_astar {
                            irtg.best_with_scorer_and_stats_prepared(
                                inputs, &strategy, scorer, prepared,
                            )
                        } else {
                            irtg.best_with_scorer_and_stats(inputs, &strategy, scorer)
                        }
                        .map_err(|err| format!("instance {sentence_no}: {err}"))?;

                        Ok(ParsedInstance {
                            sentence_no,
                            length,
                            instance,
                            best,
                            stats,
                            parse_ms: millis(parse_start.elapsed()),
                        })
                    })();
                    if tx.send(result).is_err() {
                        break;
                    }
                }
            });
        }
        drop(tx);

        for result in rx {
            match result {
                Ok(parsed) => {
                    let i = parsed.sentence_no - 1;
                    ordered[i] = Some(parsed);
                }
                Err(err) if first_error.is_none() => first_error = Some(err),
                Err(_) => {}
            }
            pb.inc(1);
        }
    });

    if let Some(err) = first_error {
        return Err(err.into());
    }
    Ok(ordered
        .into_iter()
        .map(|parsed| parsed.expect("every parse worker returned a result"))
        .collect())
}

struct ParsevalConfig {
    interpretation: String,
    kind: TreeInterpretationKind,
    params: EvalbParams,
}

fn prepare_parseval(args: &Args, irtg: &Irtg) -> Result<Option<ParsevalConfig>, Box<dyn Error>> {
    let Some(name) = args.parseval.as_ref() else {
        if args.evalb_param.is_some() || args.parseval_output.is_some() {
            return Err("--evalb-param and --parseval-output require --parseval INTERP".into());
        }
        return Ok(None);
    };

    let interpretation = irtg
        .interpretation_ref(name)
        .ok_or_else(|| format!("unknown Parseval interpretation {name:?}"))?;
    let kind = if irtg.interpretation::<TreeAlgebra>(name).is_ok() {
        TreeInterpretationKind::Plain
    } else if irtg.interpretation::<Binarizing<TreeAlgebra>>(name).is_ok() {
        TreeInterpretationKind::Binarizing
    } else {
        return Err(format!(
            "Parseval interpretation {name:?} uses {}, not a supported constituency-tree algebra",
            interpretation.class_name()
        )
        .into());
    };
    let params = match args.evalb_param.as_ref() {
        Some(path) => EvalbParams::parse(&std::fs::read_to_string(path)?)
            .map_err(|err| format!("cannot parse EVALB parameter file {path:?}: {err}"))?,
        None => EvalbParams::collins_ptb(),
    };
    Ok(Some(ParsevalConfig {
        interpretation: name.clone(),
        kind,
        params,
    }))
}

fn evaluate_tree(
    irtg: &Irtg,
    name: &str,
    kind: TreeInterpretationKind,
    arena: &TreeArena<Symbol>,
    root: rusty_tree::tree::Tree,
) -> Result<TreeValue, Box<dyn Error>> {
    Ok(match kind {
        TreeInterpretationKind::Plain => irtg
            .interpretation::<TreeAlgebra>(name)?
            .interpret_derivation(arena, root)?,
        TreeInterpretationKind::Binarizing => irtg
            .interpretation::<Binarizing<TreeAlgebra>>(name)?
            .interpret_derivation(arena, root)?,
    })
}

fn write_parseval_header(out: &mut File, args: &Args, config: &ParsevalConfig) -> io::Result<()> {
    writeln!(out, "rusty-alto Parseval evaluation")?;
    writeln!(out, "Grammar:        {}", args.grammar)?;
    writeln!(out, "Corpus:         {}", args.corpus)?;
    writeln!(out, "Interpretation: {}", config.interpretation)?;
    writeln!(
        out,
        "Parameters:     {}",
        args.evalb_param
            .as_deref()
            .unwrap_or("built-in Collins/PTB")
    )?;
    writeln!(out)?;
    writeln!(
        out,
        " Sent  Len Status       Gold  Pred  LMatch     LP     LR    LF1  UMatch     UP     UR    UF1"
    )?;
    writeln!(
        out,
        "----- ---- ----------- ----- ----- ------- ------ ------ ------ ------- ------ ------ ------"
    )
}

fn write_parseval_row(
    out: &mut File,
    sentence_no: usize,
    length: usize,
    parsed: bool,
    counts: ParsevalCounts,
) -> io::Result<()> {
    writeln!(
        out,
        "{sentence_no:>5} {length:>4} {:<11} {:>5} {:>5} {:>7} {:>6.2} {:>6.2} {:>6.2} {:>7} {:>6.2} {:>6.2} {:>6.2}",
        if parsed { "scored" } else { "no-parse" },
        counts.gold,
        counts.predicted,
        counts.matched_labeled,
        100.0 * counts.labeled_precision(),
        100.0 * counts.labeled_recall(),
        100.0 * counts.labeled_f1(),
        counts.matched_unlabeled,
        100.0 * counts.unlabeled_precision(),
        100.0 * counts.unlabeled_recall(),
        100.0 * counts.unlabeled_f1(),
    )?;
    out.flush()
}

fn write_parseval_skip(
    out: &mut File,
    sentence_no: usize,
    length: usize,
    skip: ParsevalSkip,
) -> io::Result<()> {
    let reason = match skip {
        ParsevalSkip::LengthMismatch { predicted, gold } => {
            format!("length-mismatch predicted={predicted} gold={gold}")
        }
        ParsevalSkip::Cutoff { length, cutoff } => {
            format!("cutoff normalized-length={length} limit={cutoff}")
        }
    };
    writeln!(out, "{sentence_no:>5} {length:>4} skipped     {reason}")?;
    out.flush()
}

fn write_parseval_summary(
    out: &mut File,
    counts: ParsevalCounts,
    scored: usize,
    skipped: usize,
) -> io::Result<()> {
    writeln!(out)?;
    writeln!(
        out,
        "==============================================================================="
    )?;
    writeln!(out, "Corpus summary ({scored} scored, {skipped} skipped)")?;
    writeln!(
        out,
        "                         Gold  Pred   Match  Precision  Recall      F1"
    )?;
    writeln!(
        out,
        "Labeled constituents    {:>5} {:>5} {:>7} {:>9.2} {:>7.2} {:>7.2}",
        counts.gold,
        counts.predicted,
        counts.matched_labeled,
        100.0 * counts.labeled_precision(),
        100.0 * counts.labeled_recall(),
        100.0 * counts.labeled_f1(),
    )?;
    writeln!(
        out,
        "Unlabeled constituents  {:>5} {:>5} {:>7} {:>9.2} {:>7.2} {:>7.2}",
        counts.gold,
        counts.predicted,
        counts.matched_unlabeled,
        100.0 * counts.unlabeled_precision(),
        100.0 * counts.unlabeled_recall(),
        100.0 * counts.unlabeled_f1(),
    )?;
    out.flush()
}

/// Return the cache path `<grammar>.sxcache/nmax<N>.bin`, shared with `ptb-eval`.
fn sx_cache_path(grammar_path: &str, n_max: usize) -> PathBuf {
    sx_cache_dir(grammar_path).join(format!("nmax{n_max}.bin"))
}

fn sx_cache_dir(grammar_path: &str) -> PathBuf {
    PathBuf::from(format!("{grammar_path}.sxcache"))
}

fn parse_sx_cache_nmax(path: &Path) -> Option<usize> {
    let stem = path.file_stem()?.to_str()?;
    stem.strip_prefix("nmax")?.parse().ok()
}

fn sx_load(path: &Path) -> Option<UniversalSxHeuristic> {
    let bytes = fs::read(path).ok()?;
    UniversalSxHeuristic::from_bytes(&bytes)
}

/// Load the exact cache entry, or the smallest valid cached table covering `n_needed`.
fn sx_load_covering(
    grammar_path: &str,
    n_needed: usize,
) -> Option<(UniversalSxHeuristic, PathBuf)> {
    let exact_path = sx_cache_path(grammar_path, n_needed);
    if let Some(table) = sx_load(&exact_path).filter(|table| table.n_max() >= n_needed) {
        return Some((table, exact_path));
    }

    let entries = fs::read_dir(sx_cache_dir(grammar_path)).ok()?;
    let mut candidates = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|extension| extension.to_str()) != Some("bin") {
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
        if let Some(table) = sx_load(&path).filter(|table| table.n_max() >= n_needed) {
            return Some((table, path));
        }
    }
    None
}

fn sx_save(path: &Path, table: &UniversalSxHeuristic) {
    let Some(dir) = path.parent() else {
        return;
    };
    if fs::create_dir_all(dir).is_ok() {
        let _ = fs::write(path, table.to_bytes());
    }
}

/// Build the per-sentence materialization strategy.
fn build_strategy<'h>(
    algorithm: Algorithm,
    heuristic: Heuristic,
    outside: Option<&'h OutsideHeuristic>,
    sx_table: Option<&'h UniversalSxHeuristic>,
    oblig: Option<&'h ObligatoryLeafTables>,
    n: usize,
) -> MaterializationStrategy<'h> {
    let options = || AstarOptions {
        stop_at_first_goal: true,
        beam: None,
    };
    match algorithm {
        Algorithm::Exhaustive => MaterializationStrategy::TopDownCondensed,
        Algorithm::Astar => {
            let heuristic = match heuristic {
                Heuristic::Zero => AstarHeuristic::Zero,
                Heuristic::Outside => AstarHeuristic::Outside(outside.expect("outside built")),
                Heuristic::Sx => AstarHeuristic::UniversalSx {
                    table: sx_table.expect("sx table built"),
                    n,
                },
                Heuristic::Sxf => AstarHeuristic::UniversalSxF {
                    table: sx_table.expect("sx table built"),
                    oblig: oblig.expect("oblig built"),
                    n,
                },
            };
            MaterializationStrategy::Astar {
                heuristic,
                options: options(),
            }
        }
    }
}

fn header_comments(args: &Args, primary: &str) -> Vec<String> {
    let mut lines = vec![
        format!("Parsed by rusty-alto eval on {}", utc_timestamp()),
        format!("grammar = {}", args.grammar),
        format!("corpus = {}", args.corpus),
        format!("algorithm = {}", algorithm_label(args.algorithm)),
    ];
    if args.algorithm == Algorithm::Astar {
        lines.push(format!("heuristic = {}", heuristic_label(args.heuristic)));
        lines.push(format!("input interpretation = {primary}"));
    }
    lines.push(format!("jobs = {}", args.jobs));
    lines
}

fn algorithm_label(a: Algorithm) -> &'static str {
    match a {
        Algorithm::Exhaustive => "exhaustive",
        Algorithm::Astar => "astar",
    }
}

fn heuristic_label(h: Heuristic) -> &'static str {
    match h {
        Heuristic::Zero => "zero",
        Heuristic::Outside => "outside",
        Heuristic::Sx => "sx",
        Heuristic::Sxf => "sxf",
    }
}

fn choose_primary(names: &[String]) -> String {
    names
        .iter()
        .find(|n| *n == "english")
        .or_else(|| names.iter().find(|n| *n == "i"))
        .or_else(|| names.first())
        .cloned()
        .unwrap_or_default()
}

fn word_count(text: Option<&str>) -> usize {
    text.map_or(0, |t| t.split_whitespace().count())
}

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

/// Format the current time as `YYYY-MM-DD HH:MM:SS UTC`.
fn utc_timestamp() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (hh, mm, ss) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    let (y, m, d) = civil_from_days(days);
    format!("{y:04}-{m:02}-{d:02} {hh:02}:{mm:02}:{ss:02} UTC")
}

/// Convert days since the Unix epoch to a (year, month, day) civil date (Hinnant's algorithm).
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = (if z >= 0 { z } else { z - 146_096 }) / 146_097;
    let doe = (z - era * 146_097) as u64; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32; // [1, 12]
    (if m <= 2 { y + 1 } else { y }, m, d)
}

fn parse_args() -> Result<Args, Box<dyn Error>> {
    let mut grammar = None;
    let mut corpus = None;
    let mut output = None;
    let mut limit = None;
    let mut algorithm = Algorithm::Exhaustive;
    let mut heuristic = Heuristic::Zero;
    let mut times = None;
    let mut astar_stats = None;
    let mut input = None;
    let mut parseval = None;
    let mut parseval_output = None;
    let mut evalb_param = None;
    let mut jobs = thread::available_parallelism().map_or(1, usize::from);

    let mut it = env::args().skip(1);
    while let Some(arg) = it.next() {
        let mut next = || it.next().ok_or_else(|| format!("missing value for {arg}"));
        match arg.as_str() {
            "-h" | "--help" => {
                print_usage();
                process::exit(0);
            }
            "-o" | "--output" => output = Some(next()?),
            "--limit" => limit = Some(next()?.parse()?),
            "--algorithm" => {
                algorithm = match next()?.as_str() {
                    "exhaustive" => Algorithm::Exhaustive,
                    "astar" => Algorithm::Astar,
                    other => return Err(format!("unknown algorithm {other:?}").into()),
                }
            }
            "--heuristic" => {
                heuristic = match next()?.as_str() {
                    "zero" => Heuristic::Zero,
                    "outside" => Heuristic::Outside,
                    "sx" => Heuristic::Sx,
                    "sxf" => Heuristic::Sxf,
                    other => return Err(format!("unknown heuristic {other:?}").into()),
                }
            }
            "--times" => times = Some(next()?),
            "--astar-stats" => astar_stats = Some(next()?),
            "--jobs" => {
                jobs = next()?.parse()?;
                if jobs == 0 {
                    return Err("--jobs must be at least 1".into());
                }
            }
            "--input" => input = Some(next()?),
            "--parseval" => parseval = Some(next()?),
            "--parseval-output" => parseval_output = Some(next()?),
            "--evalb-param" => evalb_param = Some(next()?),
            other if other.starts_with('-') && other != "-" => {
                return Err(format!("unknown option {other:?}").into());
            }
            _ => {
                if grammar.is_none() {
                    grammar = Some(arg);
                } else if corpus.is_none() {
                    corpus = Some(arg);
                } else {
                    return Err(format!("unexpected argument {arg:?}").into());
                }
            }
        }
    }

    Ok(Args {
        grammar: grammar.ok_or("missing <grammar.irtg> argument")?,
        corpus: corpus.ok_or("missing <corpus> argument")?,
        output,
        limit,
        algorithm,
        heuristic,
        times,
        astar_stats,
        input,
        parseval,
        parseval_output,
        evalb_param,
        jobs,
    })
}

fn print_usage() {
    eprintln!(
        "usage: eval <grammar.irtg> <corpus|-> [options]\n\
         \n\
         options:\n\
         \x20 -o, --output <file>            write output corpus to <file> (default: stdout)\n\
         \x20 --limit <n>                    parse only the first n instances\n\
         \x20 --algorithm <exhaustive|astar> intersection algorithm (default: exhaustive)\n\
         \x20 --heuristic <zero|outside|sx|sxf> A* heuristic (default: zero)\n\
         \x20 --jobs <n>                     parse up to n sentences concurrently (default: CPUs)\n\
         \x20 --times <file.csv>             write per-sentence timing as CSV\n\
         \x20 --astar-stats <file.csv>       write per-sentence A* internal counters\n\
         \x20 --input <interp>               interpretation parameterizing sx/sxf (default: auto)\n\
         \x20 --parseval <interp>            score this constituency-tree interpretation\n\
         \x20 --parseval-output <file>       write Parseval table (default: parseval.txt)\n\
         \x20 --evalb-param <file.prm>       EVALB parameters (default: built-in Collins/PTB)"
    );
}
