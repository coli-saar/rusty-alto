//! Compare complete-chart parsing strategies on an Alto/Tulipac TAG grammar.

use rusty_alto::{InputCodecRegistry, Irtg, MaterializationStrategy, TagStringAlgebra};
use std::{collections::HashMap, env, error::Error, path::Path, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "usage: tag-parse-bench GRAMMAR SENTENCE [ITERATIONS] [WARMUP] [topdown|indexed|sibling]"
        );
        std::process::exit(2);
    }
    let grammar = Path::new(&args[1]);
    let sentence = &args[2];
    let iterations = args.get(3).map_or(Ok(100usize), |s| s.parse())?;
    let warmup = args.get(4).map_or(Ok(20usize), |s| s.parse())?;
    let requested = args.get(5).map(String::as_str);

    let registry = InputCodecRegistry::standard();
    let codec = registry.codec_for_path::<Irtg>(grammar)?;
    let irtg = codec.read_path(grammar)?;
    let interpretation = irtg.interpretation::<TagStringAlgebra>("string")?;
    let value = interpretation.parse_object(sentence)?;
    let mut rhs_groups = HashMap::<usize, usize>::new();
    let mut max_rule_arity = 0;
    for rule in irtg.grammar().rules() {
        max_rule_arity = max_rule_arity.max(rule.children.len());
        if let Some(term) = interpretation.homomorphism().term_id(rule.symbol) {
            *rhs_groups.entry(term).or_default() += 1;
        }
    }
    println!("rhs_groups={}", rhs_groups.len());
    println!("max_rule_arity={max_rule_arity}");
    println!(
        "largest_rhs_group={}",
        rhs_groups.values().max().unwrap_or(&0)
    );

    for (name, strategy) in [
        ("topdown", MaterializationStrategy::TopDownCondensed),
        ("indexed", MaterializationStrategy::IndexedCondensed),
        ("sibling", MaterializationStrategy::SiblingFinder),
    ] {
        if requested.is_some_and(|wanted| wanted != name) {
            continue;
        }
        for _ in 0..warmup {
            let chart = irtg.parse_with([interpretation.input(value.clone())], &strategy)?;
            std::hint::black_box(chart);
        }

        let mut nanos = Vec::with_capacity(iterations);
        let mut last = None;
        for _ in 0..iterations {
            let start = Instant::now();
            let chart = irtg.parse_with([interpretation.input(value.clone())], &strategy)?;
            nanos.push(start.elapsed().as_nanos() as u64);
            last = Some(chart);
        }
        nanos.sort_unstable();
        let chart = last.expect("at least one iteration is required");
        println!("strategy={name}");
        println!("sentence={sentence}");
        println!("iterations={iterations}");
        println!("states={}", chart.automaton.num_states());
        println!("rules={}", chart.automaton.num_rules());
        println!("cardinality={:?}", chart.automaton.language_cardinality());
        println!("median_us={:.3}", nanos[iterations / 2] as f64 / 1_000.0);
        println!(
            "p95_us={:.3}",
            nanos[(iterations * 95 / 100).min(iterations - 1)] as f64 / 1_000.0
        );
    }
    Ok(())
}
