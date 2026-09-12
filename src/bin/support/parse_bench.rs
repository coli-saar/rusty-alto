use rusty_alto::{IrtgError, MaterializationStrategy, ParseChart};
use std::time::Instant;

pub fn validate(iterations: usize, requested: Option<&str>) -> Result<(), &'static str> {
    if iterations == 0 {
        return Err("ITERATIONS must be greater than zero");
    }
    if requested.is_some_and(|name| !matches!(name, "topdown" | "indexed" | "sibling")) {
        return Err("strategy must be topdown, indexed, or sibling");
    }
    Ok(())
}

pub fn run(
    sentence: &str,
    iterations: usize,
    warmup: usize,
    requested: Option<&str>,
    mut parse: impl FnMut(&MaterializationStrategy<'_>) -> Result<ParseChart, IrtgError>,
) -> Result<(), IrtgError> {
    for (name, strategy) in [
        ("topdown", MaterializationStrategy::TopDownCondensed),
        ("indexed", MaterializationStrategy::IndexedCondensed),
        ("sibling", MaterializationStrategy::SiblingFinder),
    ] {
        if requested.is_some_and(|wanted| wanted != name) {
            continue;
        }
        for _ in 0..warmup {
            std::hint::black_box(parse(&strategy)?);
        }

        let mut nanos = Vec::with_capacity(iterations);
        let mut last = None;
        for _ in 0..iterations {
            let start = Instant::now();
            last = Some(parse(&strategy)?);
            nanos.push(start.elapsed().as_nanos() as u64);
        }
        nanos.sort_unstable();
        let chart = last.expect("iterations were validated as nonzero");
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

#[cfg(test)]
mod tests {
    use super::validate;

    #[test]
    fn rejects_zero_iterations_and_unknown_strategies() {
        assert!(validate(0, None).is_err());
        assert!(validate(1, Some("unknown")).is_err());
        assert!(validate(1, Some("sibling")).is_ok());
    }
}
