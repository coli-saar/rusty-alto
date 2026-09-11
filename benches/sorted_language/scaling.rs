use std::hint::black_box;
use std::time::{Duration, Instant};

use rusty_alto::{Explicit, ExplicitBuilder, Symbol, parse_alto};

const SAMPLE_TARGET: Duration = Duration::from_millis(120);

fn family_filter() -> Option<String> {
    std::env::args()
        .skip(1)
        .find(|argument| !argument.starts_with('-'))
}

fn consume(automaton: &Explicit, count: usize) -> f64 {
    automaton
        .sorted_language()
        .take(count)
        .map(|tree| black_box(tree.weight()))
        .sum()
}

fn measure(mut operation: impl FnMut() -> f64) -> f64 {
    black_box(operation());
    let mut iterations = 1usize;
    loop {
        let start = Instant::now();
        for _ in 0..iterations {
            black_box(operation());
        }
        if start.elapsed() >= SAMPLE_TARGET || iterations >= (1 << 20) {
            break;
        }
        iterations *= 2;
    }

    let mut samples = Vec::with_capacity(7);
    for _ in 0..7 {
        let start = Instant::now();
        for _ in 0..iterations {
            black_box(operation());
        }
        samples.push(start.elapsed().as_nanos() as f64 / iterations as f64);
    }
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn measure_cold(automaton: &Explicit, outputs: usize) -> f64 {
    let warm = automaton.clone();
    black_box(consume(&warm, outputs));

    let probe = automaton.clone();
    let start = Instant::now();
    black_box(consume(&probe, outputs));
    let probe_time = start.elapsed().max(Duration::from_nanos(1));
    let iterations = (SAMPLE_TARGET.as_nanos() / probe_time.as_nanos()).clamp(1, 128) as usize;

    let mut samples = Vec::with_capacity(7);
    for _ in 0..7 {
        let batch = (0..iterations)
            .map(|_| automaton.clone())
            .collect::<Vec<_>>();
        let start = Instant::now();
        for instance in &batch {
            black_box(consume(instance, outputs));
        }
        samples.push(start.elapsed().as_nanos() as f64 / iterations as f64);
    }
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn initialize(automaton: &Explicit) -> f64 {
    black_box(automaton.sorted_language());
    0.0
}

fn measure_cold_initialization(automaton: &Explicit) -> f64 {
    let probe = automaton.clone();
    let start = Instant::now();
    black_box(initialize(&probe));
    let probe_time = start.elapsed().max(Duration::from_nanos(1));
    let iterations = (SAMPLE_TARGET.as_nanos() / probe_time.as_nanos()).clamp(1, 128) as usize;

    let mut samples = Vec::with_capacity(7);
    for _ in 0..7 {
        let batch = (0..iterations)
            .map(|_| automaton.clone())
            .collect::<Vec<_>>();
        let start = Instant::now();
        for instance in &batch {
            black_box(initialize(instance));
        }
        samples.push(start.elapsed().as_nanos() as f64 / iterations as f64);
    }
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn measure_binary_advances(automaton: &Explicit, advances: usize) -> f64 {
    let mut samples = Vec::with_capacity(7);
    for _ in 0..7 {
        let mut iterator = automaton.sorted_language();
        black_box(iterator.next());
        let start = Instant::now();
        for _ in 0..advances {
            black_box(iterator.next());
        }
        samples.push(start.elapsed().as_nanos() as f64 / advances as f64);
    }
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn report_initialization(family: &str, size: usize, automaton: &Explicit) {
    if let Some(filter) = family_filter()
        && filter != family
    {
        return;
    }
    let nanos = measure_cold_initialization(automaton);
    println!("RESULT,{family},{size},0,{nanos:.3}");
}

fn report_binary_advances(family: &str, size: usize, advances: usize, automaton: &Explicit) {
    if let Some(filter) = family_filter()
        && filter != family
    {
        return;
    }
    let nanos = measure_binary_advances(automaton, advances);
    println!("RESULT,{family},{size},{advances},{nanos:.3}");
}

fn report_cold(family: &str, size: usize, outputs: usize, automaton: &Explicit) {
    if let Some(filter) = family_filter()
        && filter != family
    {
        return;
    }
    let nanos = measure_cold(automaton, outputs);
    println!("RESULT,{family},{size},{outputs},{nanos:.3}");
}

fn report(family: &str, size: usize, outputs: usize, automaton: &Explicit) {
    if let Some(filter) = family_filter()
        && filter != family
    {
        return;
    }
    let nanos = measure(|| consume(automaton, outputs));
    println!("RESULT,{family},{size},{outputs},{nanos:.3}");
}

fn wide_nullary(rules: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let state = builder.new_state();
    for rule in 0..rules {
        builder.add_weighted_rule(
            Symbol(rule as u32),
            vec![],
            state,
            1.0 - rule as f64 / (rules + 1) as f64,
        );
    }
    builder.add_accepting(state);
    builder.build()
}

fn many_accepting(states: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    for state_index in 0..states {
        let state = builder.new_state();
        builder.add_weighted_rule(
            Symbol(state_index as u32),
            vec![],
            state,
            1.0 - state_index as f64 / (states + 1) as f64,
        );
        builder.add_accepting(state);
    }
    builder.build()
}

fn deep_chain(depth: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let mut state = builder.new_state();
    builder.add_weighted_rule(Symbol(0), vec![], state, 0.999);
    for level in 0..depth {
        let parent = builder.new_state();
        builder.add_weighted_rule(Symbol((level + 1) as u32), vec![state], parent, 0.999);
        state = parent;
    }
    builder.add_accepting(state);
    builder.build()
}

fn binary_product(leaves: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let child = builder.new_state();
    for leaf in 0..leaves {
        let x = (leaf + 1) as f64;
        builder.add_weighted_rule(
            Symbol(leaf as u32),
            vec![],
            child,
            (-x / leaves as f64).exp(),
        );
    }
    let root = builder.new_state();
    builder.add_weighted_rule(Symbol(leaves as u32), vec![child, child], root, 0.99);
    builder.add_accepting(root);
    builder.build()
}

fn unary_recursive() -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let state = builder.new_state();
    builder.add_weighted_rule(Symbol(0), vec![], state, 0.99);
    builder.add_weighted_rule(Symbol(1), vec![state], state, 0.999);
    builder.add_accepting(state);
    builder.build()
}

fn blocked_competitors(rules: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let productive = builder.new_state();
    let dead = builder.new_state();
    builder.add_weighted_rule(Symbol(0), vec![], productive, 0.99);
    builder.add_weighted_rule(Symbol(1), vec![productive], productive, 0.999);
    builder.add_weighted_rule(Symbol(2), vec![dead], dead, 0.5);
    for rule in 0..rules {
        builder.add_weighted_rule(Symbol((rule + 3) as u32), vec![dead], productive, 0.5);
    }
    builder.add_accepting(productive);
    builder.build()
}

fn high_arity(arity: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let child = builder.new_state();
    builder.add_weighted_rule(Symbol(0), vec![], child, 0.9);
    builder.add_weighted_rule(Symbol(1), vec![], child, 0.8);
    let root = builder.new_state();
    builder.add_weighted_rule(Symbol(2), vec![child; arity], root, 0.99);
    builder.add_accepting(root);
    builder.build()
}

fn unique_high_arity(arity: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let mut children = Vec::with_capacity(arity);
    for index in 0..arity {
        let child = builder.new_state();
        builder.add_weighted_rule(Symbol(index as u32), vec![], child, 0.9);
        children.push(child);
    }
    let root = builder.new_state();
    builder.add_weighted_rule(Symbol(arity as u32), children, root, 0.99);
    builder.add_accepting(root);
    builder.build()
}

fn balanced_binary_tree(height: usize, alternate_leaves: bool) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let leaf_count = 1usize << height;
    let mut symbol = 0u32;
    let mut level = Vec::with_capacity(leaf_count);
    for _ in 0..leaf_count {
        let state = builder.new_state();
        builder.add_weighted_rule(Symbol(symbol), vec![], state, 0.99);
        symbol += 1;
        if alternate_leaves {
            builder.add_weighted_rule(Symbol(symbol), vec![], state, 0.98);
            symbol += 1;
        }
        level.push(state);
    }
    while level.len() > 1 {
        let mut parents = Vec::with_capacity(level.len() / 2);
        for children in level.chunks_exact(2) {
            let parent = builder.new_state();
            builder.add_weighted_rule(Symbol(symbol), children.to_vec(), parent, 1.0);
            symbol += 1;
            parents.push(parent);
        }
        level = parents;
    }
    builder.add_accepting(level[0]);
    builder.build()
}

fn mostly_irrelevant(rules: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let accepting = builder.new_state();
    builder.add_weighted_rule(Symbol(0), vec![], accepting, 0.99);
    builder.add_accepting(accepting);
    for rule in 0..rules {
        let state = builder.new_state();
        builder.add_weighted_rule(Symbol((rule + 1) as u32), vec![], state, 0.5);
    }
    builder.build()
}

fn main() {
    println!("family,size,outputs,median_ns");

    for size in [256, 512, 1_024, 2_048, 4_096, 8_192, 16_384] {
        report_initialization("init_wide", size, &wide_nullary(size));
        report_initialization("init_unique_arity", size, &unique_high_arity(size));
    }

    for size in [128, 256, 512, 1_024, 2_048, 4_096] {
        let automaton = wide_nullary(size);
        report("wide_first", size, 1, &automaton);
        report("wide_all", size, size, &automaton);
    }

    for size in [64, 128, 256, 512, 1_024, 2_048] {
        let automaton = many_accepting(size);
        report("accepting_first", size, 1, &automaton);
        report("accepting_all", size, size, &automaton);
    }

    for depth in [16, 32, 64, 128, 256, 512, 1_024] {
        report("deep_first", depth, 1, &deep_chain(depth));
    }

    for leaves in [16, 32, 64, 128, 256] {
        let outputs = leaves * 4;
        report("binary_product", leaves, outputs, &binary_product(leaves));
    }

    for height in [7, 9, 11, 13, 15] {
        let nodes = (1usize << (height + 1)) - 1;
        let deterministic = balanced_binary_tree(height, false);
        report_cold("cold_binary_tree_first", nodes, 1, &deterministic);
        report("binary_tree_first", nodes, 1, &deterministic);
        report_binary_advances(
            "binary_tree_second",
            nodes,
            1,
            &balanced_binary_tree(height, true),
        );
        report_binary_advances(
            "binary_tree_advance",
            nodes,
            128,
            &balanced_binary_tree(height, true),
        );
    }

    let recursive = unary_recursive();
    for outputs in [32, 64, 128, 256, 512, 1_024] {
        report("unary_recursive", outputs, outputs, &recursive);
    }

    for size in [16, 32, 64, 128, 256, 512] {
        report(
            "blocked_competitors",
            size,
            size,
            &blocked_competitors(size),
        );
    }

    for arity in [4, 8, 16, 32, 64, 128, 256, 512] {
        let automaton = high_arity(arity);
        report("high_arity_first", arity, 1, &automaton);
        report("high_arity_two", arity, 2, &automaton);
    }

    for size in [128, 256, 512, 1_024, 2_048, 4_096, 8_192] {
        report_cold("cold_wide_first", size, 1, &wide_nullary(size));
        report_cold("cold_irrelevant_first", size, 1, &mostly_irrelevant(size));
    }

    if let Ok(path) = std::env::var("RUSTY_ALTO_BENCH_AUTOMATON") {
        let input = std::fs::read_to_string(path).expect("failed to read benchmark automaton");
        let parsed = parse_alto(&input).expect("failed to parse benchmark automaton");
        let states = parsed.automaton.num_states() as usize;
        report("realistic_first", states, 1, &parsed.automaton);
        report("realistic_128", states, 128, &parsed.automaton);
    }
}
