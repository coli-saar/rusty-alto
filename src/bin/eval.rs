//! Evaluation frontend: parse an Alto corpus with an IRTG and write the derivation tree and
//! interpreted values to a new corpus.
//!
//! Usage:
//!   eval <grammar.irtg> <corpus|-> [-o out.corpus] [--limit N]
//!        [--algorithm exhaustive|astar] [--heuristic zero|outside|sx|sxf]
//!        [--times times.csv] [--input INTERP]

use rusty_alto::{
    AstarHeuristic, AstarOptions, CorpusWriter, LogProbabilityScorer, MaterializationStrategy,
    ObligatoryLeafTables, OutsideHeuristic, Symbol, UniversalSxHeuristic, parse_irtg, read_corpus,
};
use std::{
    env,
    error::Error,
    fs::File,
    io::{self, Write},
    process,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
    },
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
    input: Option<String>,
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

    // Read + parse all objects (respecting --limit).
    let mut corpus = if args.corpus == "-" {
        read_corpus(io::stdin().lock(), &irtg, args.limit)?
    } else {
        read_corpus(File::open(&args.corpus)?, &irtg, args.limit)?
    };

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
        return Err(format!("input interpretation {primary:?} is not an inputable interpretation").into());
    }

    let scorer = LogProbabilityScorer;

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
        let interp = irtg.interpretation_ref(&primary).expect("primary present");
        let concat = interp
            .algebra_signature()
            .get("*")
            .unwrap_or(Symbol(0));
        eprintln!("building SX heuristic table (n_max={n_max})...");
        UniversalSxHeuristic::new_with(irtg.grammar(), interp.homomorphism(), concat, n_max, &scorer)
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
            writeln!(f, "sentence_no,length,parsed,score,parse_ms,output_ms,total_ms")?;
            f.flush()?;
            Some(f)
        }
        None => None,
    };

    // Progress bar with a live per-sentence timer driven by a monitor thread.
    let total = corpus.instances.len() as u64;
    let pb = ProgressBar::new(total);
    pb.set_style(
        ProgressStyle::with_template("{spinner} [{pos}/{len}] {wide_bar} {msg}")
            .unwrap()
            .tick_chars("|/-\\ "),
    );
    let current = Arc::new(Mutex::new((0usize, Instant::now())));
    let done = Arc::new(AtomicBool::new(false));
    let monitor = {
        let pb = pb.clone();
        let current = Arc::clone(&current);
        let done = Arc::clone(&done);
        thread::spawn(move || {
            while !done.load(Ordering::Relaxed) {
                let (idx, start) = *current.lock().unwrap();
                pb.set_message(format!("#{idx} {:.2}s", start.elapsed().as_secs_f64()));
                thread::sleep(Duration::from_millis(100));
            }
        })
    };

    let run_start = Instant::now();
    let mut parsed_count = 0usize;

    let interp_order = corpus.interpretation_order.clone();
    let result: Result<(), Box<dyn Error>> = (|| {
        for (i, instance) in corpus.instances.iter_mut().enumerate() {
            let sentence_no = i + 1;
            let length = word_count(instance.text(&primary));

            // Per-sentence strategy.
            let strategy = build_strategy(
                args.algorithm,
                args.heuristic,
                outside.as_ref(),
                sx_table.as_ref(),
                oblig.as_ref(),
                length,
            );

            // Inputs: intersect all inputable interpretations (consume their parsed values).
            // Output-only interpretations have no value and are skipped here.
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

            *current.lock().unwrap() = (sentence_no, Instant::now());
            let parse_start = Instant::now();
            let best = irtg.best_with_scorer(inputs, &strategy, &scorer)?;
            let parse_ms = millis(parse_start.elapsed());

            let derivation = best.as_ref().map(|tree| (tree.arena(), tree.root()));
            if derivation.is_some() {
                parsed_count += 1;
            }

            let output_start = Instant::now();
            writer.write_instance(&irtg, &interp_order, derivation, instance)?;
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

            pb.inc(1);
        }
        Ok(())
    })();

    done.store(true, Ordering::Relaxed);
    let _ = monitor.join();
    pb.finish_and_clear();

    result?;

    eprintln!(
        "parsed {}/{} instances in {:.2}s",
        parsed_count,
        total,
        run_start.elapsed().as_secs_f64()
    );
    Ok(())
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
    let mut input = None;

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
            "--input" => input = Some(next()?),
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
        input,
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
         \x20 --times <file.csv>             write per-sentence timing as CSV\n\
         \x20 --input <interp>               interpretation parameterizing sx/sxf (default: auto)"
    );
}
