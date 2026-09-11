use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};
use rusty_alto::{Explicit, ExplicitBuilder, Symbol};

#[derive(Clone, Debug)]
struct BenchRng(u64);

impl BenchRng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, limit: usize) -> usize {
        (self.next() as usize) % limit
    }

    fn weight(&mut self) -> f64 {
        0.1 + (self.next() >> 11) as f64 * (0.89 / ((1u64 << 53) as f64))
    }
}

fn random_acyclic_automaton(seed: u64, states: usize, rules_per_state: usize) -> Explicit {
    let mut rng = BenchRng(seed);
    let mut builder = ExplicitBuilder::new();
    let state_ids = (0..states).map(|_| builder.new_state()).collect::<Vec<_>>();
    let mut symbol = 0u32;

    for state_index in 0..states {
        for rule_index in 0..rules_per_state {
            // A nullary rule per state guarantees productivity. Other rules
            // point strictly backwards, so each generated language is finite.
            let arity = if state_index == 0 || rule_index == 0 {
                0
            } else {
                rng.below(3)
            };
            let children = (0..arity)
                .map(|_| state_ids[rng.below(state_index)])
                .collect();
            builder.add_weighted_rule(
                Symbol(symbol),
                children,
                state_ids[state_index],
                rng.weight(),
            );
            symbol += 1;
        }
    }
    builder.add_accepting(state_ids[states - 1]);
    builder.build()
}

fn wide_nullary_automaton(rules: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let state = builder.new_state();
    for rule in 0..rules {
        let weight = 1.0 - rule as f64 / (rules + 1) as f64;
        builder.add_weighted_rule(Symbol(rule as u32), vec![], state, weight);
    }
    builder.add_accepting(state);
    builder.build()
}

fn consume(automaton: &Explicit, count: usize) -> f64 {
    automaton
        .sorted_language()
        .take(count)
        .map(|tree| black_box(tree.weight()))
        .sum()
}

fn wide_nullary(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorted_language/wide_nullary");
    for rules in [256usize, 1_024, 4_096] {
        let automaton = wide_nullary_automaton(rules);
        group.throughput(Throughput::Elements(rules as u64));
        group.bench_with_input(BenchmarkId::from_parameter(rules), &rules, |b, &count| {
            b.iter(|| black_box(consume(black_box(&automaton), count)))
        });
    }
    group.finish();
}

fn random_automata(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorted_language/random_acyclic");
    for (states, rules_per_state, outputs) in
        [(32usize, 6usize, 100usize), (128, 8, 200), (512, 6, 200)]
    {
        let automata = (0..8)
            .map(|seed| random_acyclic_automaton(seed, states, rules_per_state))
            .collect::<Vec<_>>();
        let id = format!("{states}x{rules_per_state}/k{outputs}");
        group.throughput(Throughput::Elements((automata.len() * outputs) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(&id), &outputs, |b, &count| {
            b.iter(|| {
                let total = automata
                    .iter()
                    .map(|automaton| consume(black_box(automaton), count))
                    .sum::<f64>();
                black_box(total)
            })
        });
    }
    group.finish();
}

criterion_group!(benches, wide_nullary, random_automata);
criterion_main!(benches);
