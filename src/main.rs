use rusty_alto::{InputCodecRegistry, Irtg, RenderedValue};
use std::{
    env,
    error::Error,
    io::{self, BufRead, IsTerminal, Write},
    path::Path,
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
        eprintln!("usage: rusty-alto <grammar.irtg|grammar.tag>");
        std::process::exit(2);
    };

    let load_start = Instant::now();
    let registry = InputCodecRegistry::standard();
    let codec = registry.codec_for_path::<Irtg>(Path::new(&path))?;
    let is_tulipac = codec.metadata().name == "tulipac";
    let irtg = codec.read_path(Path::new(&path))?;
    let load_time = load_start.elapsed();

    let interpretation_name = choose_input_interpretation(&irtg)
        .ok_or("grammar does not contain a supported input interpretation")?;
    let interpretation = irtg.interpretation_ref(&interpretation_name).unwrap();

    eprintln!("loaded {path} in {}", format_duration(load_time));
    eprintln!("using interpretation {interpretation_name:?}");

    let stdin = io::stdin();
    let interactive = stdin.is_terminal();
    let mut stdin = stdin.lock();
    let mut line = String::new();
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
        let object_start = Instant::now();
        let value = match interpretation.parse_object_erased(sentence) {
            Ok(value) => value,
            Err(err) => {
                println!("Input error: {err}");
                continue;
            }
        };
        let object_time = object_start.elapsed();

        let parse_start = Instant::now();
        let mut chart = match irtg.parse([interpretation.input_erased(value)]) {
            Ok(chart) => chart,
            Err(err) => {
                println!("Parse error: {err}");
                continue;
            }
        };
        if is_tulipac && irtg.interpretation_ref("ft").is_some() {
            chart.automaton = irtg.filter_non_null(&chart.automaton, "ft")?;
        }
        let parse_time = parse_start.elapsed();

        let top_start = Instant::now();
        let top = chart.automaton.viterbi();
        let top_time = top_start.elapsed();
        let total_time = object_time + parse_time + top_time;

        println!(
            "Timing: total={} parse={} viterbi={} input={}",
            format_duration_compact(total_time),
            format_duration_compact(parse_time),
            format_duration_compact(top_time),
            format_duration_compact(object_time),
        );

        let Some(top) = top else {
            println!("No parse.");
            continue;
        };

        println!(
            "Derivation: {}",
            irtg.resolve_derivation(top.arena(), top.root())
        );
        for rendered in irtg.render_derivation(top.arena(), top.root())? {
            match rendered.value {
                RenderedValue::Text(value) => println!("{}: {value}", rendered.name),
                RenderedValue::Tree(value) => println!("{}: {value}", rendered.name),
            }
        }
    }

    Ok(())
}

fn choose_input_interpretation(irtg: &Irtg) -> Option<String> {
    let names = irtg.input_interpretation_names();
    if names.is_empty() {
        return None;
    }
    names
        .iter()
        .copied()
        .find(|&name| name == "string")
        .or_else(|| names.iter().copied().find(|&name| name == "english"))
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
