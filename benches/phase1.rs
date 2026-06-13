use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main,
};
use rusty_alto::{
    Arena, BottomUpTa, DetBottomUpTa, Determinized, Explicit, ExplicitBuilder, IndexedBottomUpTa,
    Memo, Product, StateId, Symbol, TestArena, TestNode, TopDownTa, materialize, run_det,
    run_nondet,
};

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

fn balanced_tree(depth: usize) -> (TestArena, TestNode) {
    fn build(arena: &mut TestArena, depth: usize) -> TestNode {
        if depth == 0 {
            arena.add_node(A, vec![])
        } else {
            let left = build(arena, depth - 1);
            let right = build(arena, depth - 1);
            arena.add_node(F, vec![left, right])
        }
    }

    let mut arena = TestArena::new();
    let root = build(&mut arena, depth);
    (arena, root)
}

fn unary_chain(len: usize) -> (TestArena, TestNode) {
    let mut arena = TestArena::new();
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

criterion_group!(
    benches,
    explicit_lookup,
    tree_runs,
    memo_behavior,
    combinators,
    materialization,
    reachability
);
criterion_main!(benches);
