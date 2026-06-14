use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main,
};
use rusty_alto::{
    BottomUpTa, CondensedTa, DetBottomUpTa, Determinized, Explicit, ExplicitBuilder, HomLabel,
    Homomorphism, IndexedBottomUpTa, InvHom, Memo, Product, Span, StateId, StringAlgebra,
    StringDecompositionAutomaton, Symbol, TopDownTa, materialize,
    materialize_indexed_condensed_intersection, parse_irtg, run_det, run_nondet,
};
use rusty_tree::tree::{Tree, TreeArena};

const A: Symbol = Symbol(0);
const U: Symbol = Symbol(1);
const F: Symbol = Symbol(2);
const H: Symbol = Symbol(3);

fn explicit_chain() -> (Explicit, StateId, StateId) {
    let mut builder = ExplicitBuilder::new();
    let leaf = builder.new_state();
    let node = builder.new_state();
    builder.add_rule(A, vec![], leaf);
    builder.add_rule(U, vec![leaf], node);
    builder.add_rule(U, vec![node], node);
    builder.add_rule(F, vec![leaf, leaf], node);
    builder.add_rule(F, vec![node, node], node);
    builder.add_rule(H, vec![node, node, node], node);
    builder.add_accepting(node);
    (builder.build(), leaf, node)
}

fn balanced_tree(depth: usize) -> (TreeArena<Symbol>, Tree) {
    fn build(arena: &mut TreeArena<Symbol>, depth: usize) -> Tree {
        if depth == 0 {
            arena.add_node(A, vec![])
        } else {
            let left = build(arena, depth - 1);
            let right = build(arena, depth - 1);
            arena.add_node(F, vec![left, right])
        }
    }

    let mut arena = TreeArena::new();
    let root = build(&mut arena, depth);
    (arena, root)
}

fn unary_chain(len: usize) -> (TreeArena<Symbol>, Tree) {
    let mut arena = TreeArena::new();
    let mut node = arena.add_node(A, vec![]);
    for _ in 0..len {
        node = arena.add_node(U, vec![node]);
    }
    (arena, node)
}

fn nondet_explicit() -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let even = builder.new_state();
    let odd = builder.new_state();
    builder.add_rule(A, vec![], even);
    builder.add_rule(A, vec![], odd);
    builder.add_rule(F, vec![even, even], even);
    builder.add_rule(F, vec![even, odd], odd);
    builder.add_rule(F, vec![odd, even], odd);
    builder.add_rule(F, vec![odd, odd], even);
    builder.add_accepting(even);
    builder.build()
}

#[derive(Clone, Copy)]
struct DepthCap {
    cap: u8,
}

impl BottomUpTa for DepthCap {
    type State = u8;

    fn step(&self, f: Symbol, children: &[Self::State], out: &mut dyn FnMut(Self::State)) {
        match (f, children) {
            (A, []) => out(0),
            (U, [q]) => out(q.saturating_add(1).min(self.cap)),
            (F, [left, right]) => out(left.max(right).saturating_add(1).min(self.cap)),
            (H, [a, b, c]) => out(a.max(b).max(c).saturating_add(1).min(self.cap)),
            _ => {}
        }
    }

    fn is_accepting(&self, q: &Self::State) -> bool {
        *q == self.cap
    }
}

impl DetBottomUpTa for DepthCap {
    fn step_det(&self, f: Symbol, children: &[Self::State]) -> Option<Self::State> {
        let mut out = None;
        self.step(f, children, &mut |q| out = Some(q));
        out
    }
}

fn explicit_lookup(c: &mut Criterion) {
    let (automaton, leaf, node) = explicit_chain();
    let mut group = c.benchmark_group("explicit_lookup");

    group.bench_function("nullary_step_det", |b| {
        b.iter(|| black_box(&automaton).step_det(black_box(A), black_box(&[])))
    });
    group.bench_function("unary_step_det", |b| {
        b.iter(|| black_box(&automaton).step_det(black_box(U), black_box(&[leaf])))
    });
    group.bench_function("binary_step_det", |b| {
        b.iter(|| black_box(&automaton).step_det(black_box(F), black_box(&[node, node])))
    });
    group.bench_function("higher_step_det", |b| {
        b.iter(|| black_box(&automaton).step_det(black_box(H), black_box(&[node, node, node])))
    });
    group.bench_function("binary_step_partial", |b| {
        b.iter(|| {
            let mut count = 0usize;
            black_box(&automaton)
                .step_partial(black_box(F), 0, black_box(&node), &mut |_, _| count += 1);
            black_box(count)
        })
    });
    group.bench_function("topdown_by_parent", |b| {
        b.iter(|| {
            let mut count = 0usize;
            black_box(&automaton).step_topdown(black_box(&node), &mut |_, _| count += 1);
            black_box(count)
        })
    });

    group.finish();
}

fn tree_runs(c: &mut Criterion) {
    let (automaton, _, _) = explicit_chain();
    let mut group = c.benchmark_group("tree_runs");

    for depth in [8, 10, 12] {
        let (arena, root) = balanced_tree(depth);
        group.throughput(Throughput::Elements(arena.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("run_det_balanced", depth),
            &depth,
            |b, _| b.iter(|| run_det(black_box(&automaton), black_box(&arena), black_box(root))),
        );
    }

    let nondet = nondet_explicit();
    let (arena, root) = balanced_tree(9);
    group.throughput(Throughput::Elements(arena.len() as u64));
    group.bench_function("run_nondet_balanced_depth_9", |b| {
        b.iter(|| run_nondet(black_box(&nondet), black_box(&arena), black_box(root)))
    });

    group.finish();
}

fn memo_behavior(c: &mut Criterion) {
    let mut group = c.benchmark_group("memo");

    group.bench_function("cold_run_det_implicit_depth_10", |b| {
        let (arena, root) = balanced_tree(10);
        b.iter_batched(
            || Memo::new(DepthCap { cap: 16 }),
            |memo| run_det(black_box(&memo), black_box(&arena), black_box(root)),
            BatchSize::SmallInput,
        )
    });

    let (arena, root) = balanced_tree(10);
    let memo = Memo::new(DepthCap { cap: 16 });
    let _ = run_det(&memo, &arena, root);
    group.bench_function("warm_run_det_implicit_depth_10", |b| {
        b.iter(|| run_det(black_box(&memo), black_box(&arena), black_box(root)))
    });

    group.finish();
}

fn combinators(c: &mut Criterion) {
    let (left, _, node_l) = explicit_chain();
    let (right, _, node_r) = explicit_chain();
    let product = Product(left, right);
    let child = (node_l, node_r);

    let mut group = c.benchmark_group("combinators");
    group.bench_function("product_binary_step", |b| {
        b.iter(|| {
            let mut count = 0usize;
            product.step(black_box(F), black_box(&[child, child]), &mut |_| {
                count += 1
            });
            black_box(count)
        })
    });
    group.bench_function("product_binary_step_det", |b| {
        b.iter(|| product.step_det(black_box(F), black_box(&[child, child])))
    });
    group.bench_function("product_binary_step_partial", |b| {
        b.iter(|| {
            let mut count = 0usize;
            product.step_partial(black_box(F), 0, black_box(&child), &mut |_, _| count += 1);
            black_box(count)
        })
    });

    let det = Determinized(nondet_explicit());
    let mut child_set = std::collections::BTreeSet::new();
    child_set.insert(StateId(0));
    child_set.insert(StateId(1));
    group.bench_function("determinized_binary_step_det", |b| {
        b.iter(|| {
            det.step_det(
                black_box(F),
                black_box(&[child_set.clone(), child_set.clone()]),
            )
        })
    });

    group.finish();
}

fn materialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("materialize");
    for cap in [4, 8, 12] {
        group.bench_with_input(
            BenchmarkId::new("depth_cap_arity_le_2", cap),
            &cap,
            |b, &cap| {
                b.iter(|| {
                    materialize(
                        black_box(&DepthCap { cap }),
                        black_box(&[(A, 0), (U, 1), (F, 2)]),
                    )
                })
            },
        );
    }
    group.finish();
}

fn reachability(c: &mut Criterion) {
    let mut group = c.benchmark_group("explicit_reachability");
    for len in [128, 1024, 8192] {
        let (arena, _root) = unary_chain(len);
        let mut builder = ExplicitBuilder::new();
        let mut previous = builder.new_state();
        builder.add_rule(A, vec![], previous);
        for _ in 0..len {
            let next = builder.new_state();
            builder.add_rule(U, vec![previous], next);
            previous = next;
        }
        builder.add_accepting(previous);
        let automaton = builder.build();
        group.throughput(Throughput::Elements(arena.len() as u64));
        group.bench_with_input(BenchmarkId::new("unary_chain", len), &len, |b, _| {
            b.iter(|| black_box(&automaton).reachable_states())
        });
    }
    group.finish();
}

fn string_decomposition(c: &mut Criterion) {
    let mut algebra = StringAlgebra::new();
    let words: Vec<_> = (0..8)
        .map(|i| algebra.intern_word(format!("w{i}")))
        .collect();
    let sentence: Vec<_> = (0..32).map(|i| words[i % words.len()]).collect();
    let decomp = algebra.decompose(sentence);
    let concat = algebra.concat_symbol();
    let repeated_word = words[0];

    let mut group = c.benchmark_group("string_decomposition");
    group.throughput(Throughput::Elements(decomp.len() as u64));

    group.bench_function("lexical_lookup_repeated_word", |b| {
        b.iter(|| {
            let mut count = 0usize;
            decomp.step(black_box(repeated_word), black_box(&[]), &mut |_| {
                count += 1
            });
            black_box(count)
        })
    });

    group.bench_function("concat_adjacency", |b| {
        b.iter(|| {
            let mut count = 0usize;
            decomp.step(
                black_box(concat),
                black_box(&[Span::new(3, 11), Span::new(11, 19)]),
                &mut |_| count += 1,
            );
            black_box(count)
        })
    });

    group.bench_function("indexed_partial_concat_left", |b| {
        b.iter(|| {
            let mut count = 0usize;
            decomp.step_partial(
                black_box(concat),
                0,
                black_box(&Span::new(3, 11)),
                &mut |_, _| count += 1,
            );
            black_box(count)
        })
    });

    group.bench_function("condensed_rules", |b| {
        b.iter(|| {
            let mut count = 0usize;
            decomp.condensed_rules(&mut |_, _, _| count += 1);
            black_box(count)
        })
    });

    let mut arena = TreeArena::new();
    let v0 = arena.add_node(HomLabel::Var(0), vec![]);
    let v1 = arena.add_node(HomLabel::Var(1), vec![]);
    let concat_term = arena.add_node(HomLabel::Symbol(concat), vec![v0, v1]);
    let mut hom = Homomorphism::with_arena(arena);
    hom.add(Symbol(1_000), 2, concat_term).unwrap();
    let inv = InvHom::new(decomp, &hom);

    group.bench_function("condensed_invhom_concat", |b| {
        b.iter(|| {
            let mut count = 0usize;
            inv.condensed_rules(&mut |_, _, _| count += 1);
            black_box(count)
        })
    });

    group.finish();
}

fn irtg_condensed_parsing(c: &mut Criterion) {
    let states = 8;
    let len = 12;
    let vocab = 8;
    let lexical_labels = 2;
    let binary_labels = 4;
    let irtg_text = synthetic_string_irtg(states, vocab, lexical_labels, binary_labels);
    let irtg = parse_irtg(irtg_text.as_bytes()).unwrap();
    let interpretation = irtg.interpretation::<StringAlgebra>("i").unwrap();
    let sentence_text = synthetic_sentence_text(len, vocab);
    let sentence = interpretation.parse_object(&sentence_text).unwrap();
    let concat = interpretation.algebra_signature().get("*").unwrap();

    let mut group = c.benchmark_group("irtg_condensed_parsing");
    group.throughput(Throughput::Elements(len as u64));

    group.bench_function("direct_indexed_condensed", |b| {
        b.iter(|| {
            let decomp = StringDecompositionAutomaton::new(concat, sentence.clone());
            let invhom = InvHom::new(decomp, interpretation.homomorphism());
            let (chart, _, stats) =
                materialize_indexed_condensed_intersection(black_box(irtg.grammar()), &invhom);
            black_box((chart.rules().count(), stats.output_states))
        })
    });

    group.bench_function("irtg_parse", |b| {
        b.iter(|| {
            let chart = irtg
                .parse([interpretation.input(sentence.clone())])
                .unwrap();
            black_box((
                chart.automaton.rules().count(),
                chart.stats[0].output_states,
            ))
        })
    });

    group.finish();
}

fn synthetic_string_irtg(
    states: usize,
    vocab: usize,
    lexical_labels: usize,
    binary_labels: usize,
) -> String {
    let mut out = String::from("interpretation i: de.up.ling.irtg.algebra.StringAlgebra\n\n");

    for state in 0..states {
        let final_mark = if state == 0 { "!" } else { "" };
        for word in 0..vocab {
            for variant in 0..lexical_labels {
                out.push_str(&format!(
                    "q{state}{final_mark} -> lex_{word}_{variant}\n  [i] w{word}\n\n"
                ));
            }
        }
    }

    for op in 0..binary_labels {
        for left in 0..states {
            for right in 0..states {
                let parent = (left * 31 + right * 17 + op * 13) % states;
                let final_mark = if parent == 0 { "!" } else { "" };
                out.push_str(&format!(
                    "q{parent}{final_mark} -> bin_{op}(q{left},q{right})\n  [i] *(?1,?2)\n\n"
                ));
            }
        }
    }

    out
}

fn synthetic_sentence_text(len: usize, vocab: usize) -> String {
    (0..len)
        .map(|i| format!("w{}", i % vocab))
        .collect::<Vec<_>>()
        .join(" ")
}

criterion_group!(
    benches,
    explicit_lookup,
    tree_runs,
    memo_behavior,
    combinators,
    materialization,
    reachability,
    string_decomposition,
    irtg_condensed_parsing
);
criterion_main!(benches);
