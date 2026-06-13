use rusty_alto::{Irtg, StringAlgebra, parse_irtg};
use std::{
    env,
    error::Error,
    fs::File,
    io::{self, BufRead, IsTerminal, Write},
    time::{Duration, Instant},
};

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let Some(path) = env::args().nth(1) else {
        eprintln!("usage: rusty-alto <grammar.irtg>");
        std::process::exit(2);
    };

    let load_start = Instant::now();
    let file = File::open(&path)?;
    let irtg = parse_irtg(file)?;
    let load_time = load_start.elapsed();

    let interpretation_name = choose_string_interpretation(&irtg)
        .ok_or("IRTG does not contain a supported StringAlgebra interpretation")?;
    let interpretation = irtg.interpretation::<StringAlgebra>(&interpretation_name)?;

    eprintln!("loaded {path} in {}", format_duration(load_time));
    eprintln!("using interpretation {interpretation_name:?}");

    let stdin = io::stdin();
    let interactive = stdin.is_terminal();
    let mut stdin = stdin.lock();
    let mut line = String::new();
    let mut sentence_number = 0usize;

    if interactive {
        eprintln!("enter sentences; Ctrl-D exits");
    }

    loop {
        if interactive {
            eprint!("> ");
            io::stderr().flush()?;
        }

        line.clear();
        if stdin.read_line(&mut line)? == 0 {
            if interactive {
                eprintln!();
            }
            break;
        }

        let sentence = line.trim();
        if sentence.is_empty() {
            continue;
        }
        sentence_number += 1;

        let object_start = Instant::now();
        let value = match interpretation.parse_object(sentence) {
            Ok(value) => value,
            Err(err) => {
                println!("{sentence_number:05} [{sentence}] input-error={err}");
                continue;
            }
        };
        let object_time = object_start.elapsed();

        let parse_start = Instant::now();
        let chart = match irtg.parse([interpretation.input(value)]) {
            Ok(chart) => chart,
            Err(err) => {
                println!("{sentence_number:05} [{sentence}] parse-error={err}");
                continue;
            }
        };
        let parse_time = parse_start.elapsed();

        let top_start = Instant::now();
        let mut language = chart.automaton.sorted_language();
        let _top = language.next();
        let top_time = top_start.elapsed();
        let total_time = object_time + parse_time + top_time;

        println!(
            "{sentence_number:05} [{sentence}] {} parse={} top={} input={}",
            format_duration_compact(total_time),
            format_duration_compact(parse_time),
            format_duration_compact(top_time),
            format_duration_compact(object_time),
        );
    }

    Ok(())
}

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

fn format_duration_compact(duration: Duration) -> String {
    let nanos = duration.as_nanos();
    if nanos < 1_000 {
        format!("{nanos}ns")
    } else if nanos < 1_000_000 {
        format!("{:.2}us", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2}ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.3}s", duration.as_secs_f64())
    }
}

fn format_duration(duration: Duration) -> String {
    let nanos = duration.as_nanos();
    if nanos < 1_000 {
        format!("{nanos} ns")
    } else if nanos < 1_000_000 {
        format!("{:.2} us", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2} ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.3} s", duration.as_secs_f64())
    }
}
