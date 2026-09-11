use rusty_alto::{Explicit, ExplicitBuilder, StateId, Symbol, parse_alto};
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering};

struct TrackingAllocator;

static TRACKING: AtomicBool = AtomicBool::new(false);
static LIVE: AtomicIsize = AtomicIsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn record_growth(bytes: usize) {
    let live = LIVE.fetch_add(bytes as isize, Ordering::Relaxed) + bytes as isize;
    let live = usize::try_from(live).unwrap_or(0);
    PEAK.fetch_max(live, Ordering::Relaxed);
}

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() && TRACKING.load(Ordering::Relaxed) {
            record_growth(layout.size());
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        if TRACKING.load(Ordering::Relaxed) {
            LIVE.fetch_sub(layout.size() as isize, Ordering::Relaxed);
        }
        unsafe { System.dealloc(pointer, layout) };
    }

    unsafe fn realloc(&self, pointer: *mut u8, old: Layout, new_size: usize) -> *mut u8 {
        let new_pointer = unsafe { System.realloc(pointer, old, new_size) };
        if !new_pointer.is_null() && TRACKING.load(Ordering::Relaxed) {
            if new_size >= old.size() {
                record_growth(new_size - old.size());
            } else {
                LIVE.fetch_sub((old.size() - new_size) as isize, Ordering::Relaxed);
            }
        }
        new_pointer
    }
}

#[global_allocator]
static ALLOCATOR: TrackingAllocator = TrackingAllocator;

fn start_tracking() {
    LIVE.store(0, Ordering::Relaxed);
    PEAK.store(0, Ordering::Relaxed);
    TRACKING.store(true, Ordering::Relaxed);
}

fn stop_tracking() -> (isize, usize) {
    TRACKING.store(false, Ordering::Relaxed);
    (LIVE.load(Ordering::Relaxed), PEAK.load(Ordering::Relaxed))
}

fn balanced_binary_tree(height: usize, alternate_leaves: bool) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let mut symbol = 0u32;
    let mut level = Vec::with_capacity(1usize << height);
    for _ in 0..1usize << height {
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

fn mostly_irrelevant(state_count: usize) -> Explicit {
    let mut builder = ExplicitBuilder::new();
    let accepting = builder.new_state();
    builder.add_weighted_rule(Symbol(0), vec![], accepting, 0.99);
    builder.add_accepting(accepting);
    for index in 1..state_count {
        let state = builder.new_state();
        builder.add_weighted_rule(Symbol(index as u32), vec![], state, 0.5);
    }
    builder.build()
}

fn measure(name: &str, automaton: &Explicit, outputs: usize) {
    start_tracking();
    let indexed_rules = (0..automaton.num_states())
        .map(StateId)
        .map(|state| automaton.rules_topdown(state).count())
        .sum::<usize>();
    let (index_live, index_peak) = stop_tracking();
    black_box(indexed_rules);

    start_tracking();
    let mut iterator = automaton.sorted_language();
    for _ in 0..outputs {
        black_box(iterator.next());
    }
    let (iterator_live, iterator_peak) = stop_tracking();
    black_box(&iterator);

    println!("MEMORY,{name},{outputs},{index_live},{index_peak},{iterator_live},{iterator_peak}");
}

fn main() {
    println!("kind,workload,outputs,index_live,index_peak,iterator_live,iterator_peak");
    measure("binary_65535_first", &balanced_binary_tree(15, false), 1);
    measure(
        "binary_65535_advance128",
        &balanced_binary_tree(15, true),
        129,
    );
    measure("irrelevant_500000_first", &mostly_irrelevant(500_000), 1);
    if let Ok(path) = std::env::var("RUSTY_ALTO_BENCH_AUTOMATON") {
        let input = std::fs::read_to_string(path).expect("failed to read benchmark automaton");
        let parsed = parse_alto(&input).expect("failed to parse benchmark automaton");
        measure("realistic_first", &parsed.automaton, 1);
        measure("realistic_128", &parsed.automaton, 128);
    }
}
