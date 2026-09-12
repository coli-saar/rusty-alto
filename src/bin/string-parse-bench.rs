//! Compare complete-chart parsing strategies on an Alto IRTG string interpretation.

#[path = "support/parse_bench.rs"]
mod parse_bench;

use rusty_alto::{InputCodecRegistry, Irtg, StringAlgebra};
use std::{collections::HashMap, env, error::Error, path::Path};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 4 {
        eprintln!(
            "usage: string-parse-bench GRAMMAR INTERPRETATION SENTENCE [ITERATIONS] [WARMUP] [topdown|indexed|sibling]"
        );
        std::process::exit(2);
    }
    let grammar = Path::new(&args[1]);
    let interpretation_name = &args[2];
    let sentence = &args[3];
    let iterations = args.get(4).map_or(Ok(100usize), |s| s.parse())?;
    let warmup = args.get(5).map_or(Ok(20usize), |s| s.parse())?;
    let requested = args.get(6).map(String::as_str);
    parse_bench::validate(iterations, requested)?;

    let registry = InputCodecRegistry::standard();
    let codec = registry.codec_for_path::<Irtg>(grammar)?;
    let irtg = codec.read_path(grammar)?;
    let interpretation = irtg.interpretation::<StringAlgebra>(interpretation_name)?;
    let value = interpretation.parse_object(sentence)?;
    let mut rhs_groups = HashMap::<usize, usize>::new();
    for rule in irtg.grammar().rules() {
        if let Some(term) = interpretation.homomorphism().term_id(rule.symbol) {
            *rhs_groups.entry(term).or_default() += 1;
        }
    }
    println!("rhs_groups={}", rhs_groups.len());
    println!(
        "largest_rhs_group={}",
        rhs_groups.values().max().unwrap_or(&0)
    );

    parse_bench::run(sentence, iterations, warmup, requested, |strategy| {
        irtg.parse_with([interpretation.input(value.clone())], strategy)
    })?;
    Ok(())
}
