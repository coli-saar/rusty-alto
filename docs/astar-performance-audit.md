# A* Parser Performance Audit

## Context

`src/astar.rs` implements an A* intersection materializer for weighted tree
automata. It finalizes product states `(left_state, right_state)` in best-first
(merit) order and either emits a chart (`materialize_astar_intersection*`) or
reconstructs a single best tree (`astar_one_best*`). The dominant production
workload is PTB string parsing, where the right automaton is
`InvHom<StringDecompositionAutomaton>` (state = `Span`) and the specialized
product-aware span path (`run_with_span_product_sibling_finder` /
`expand_from_finalized_with_span_product_siblings`) drives candidate generation.

`docs/astar-design-decisions.md` records that on PTB20 `astar-zero` the run
generates roughly **108M sibling tuples** and **334M candidate edges**, of which
about **222M are discarded as dominated**, at a total time of ~103s. The design
doc names candidate dominance as the largest remaining waste and identifies
per-candidate cost (sibling lookup, `right.step`, child-tuple construction,
scoring) as the surrounding overhead.

This audit was produced by reading `src/astar.rs`, `src/astar/span.rs`,
`src/materialize.rs`, `src/algebras/string.rs`, `src/heuristic.rs`,
`src/interner.rs`, `src/set_trie.rs`, `src/combinators/invhom.rs`, the
performance docs, and the two A* benchmark binaries (`src/bin/ptb-eval.rs`,
`src/bin/astar-join-replay.rs`). It lists concrete optimization opportunities,
each with code location, rationale, expected leverage, a proposed fix, risk, and
how to verify.

---

## Findings (prioritized)

### P1 — `InvHom::step` allocates a fresh `FxHashSet` on every call (highest confidence)

**Location:** `src/combinators/invhom.rs:101-112` (the `seen` set at line 106),
driven from `src/astar.rs:682` (`binary_right_parents`) and `src/astar.rs:735`
(unary expansion).

**What happens.** Every `right.step(symbol, children, out)` call builds a new
`FxHashSet` to deduplicate results:

```rust
fn step(&self, f_src, children, out) {
    let Some(term) = self.hom.get(f_src) else { return; };
    let mut seen = FxHashSet::default();          // allocates on first insert
    eval_term(self.hom.arena(), term, children, &self.inner, &mut |q| {
        if seen.insert(q.clone()) { out(q); }
    });
}
```

On the A* span path `right.step` is called once per *(sibling × symbol group)*
inside `binary_right_parents`, and once per unary rule per finalized state. That
is on the order of the 108M sibling tuples / 334M candidates reported in the
design doc. For the `concat` operation of `StringDecompositionAutomaton`, the
homomorphic image is `concat(?0, ?1)`: `eval_term` evaluates the two variable
children to one span each, takes a single cartesian combination, and calls
`inner.step(concat, [left, right])`, which returns **exactly one** span when the
spans are adjacent (and the sibling finder only ever supplies adjacent spans).
So the dedup set sees a single insert, allocates its initial table on that
insert, and is then dropped. The deduplication is pure overhead on this path.

**Leverage.** Removes on the order of 10^8 small heap allocate/insert/free
cycles for the PTB workload. This path is *not* exercised by the
`astar-join-replay` benchmark (which replays the generic set-trie join and never
calls `right.step`), so it appears to be an unexplored cost center distinct from
the dominance work already studied.

**Proposed fix (general, recommended).** In `InvHom::step`, collect results into
a stack `SmallVec<[A::State; N]>` and dedup linearly while small, escalating to
an `FxHashSet` only past a threshold. This preserves the no-duplicate
`BottomUpTa` contract for images that genuinely can produce duplicates (nested or
repeated structure) while making the common 0/1/small-result case allocation-free.
Benefits every `step` caller, not just A*.

**Proposed fix (alternative, narrower).** Add a deterministic binary-step fast
path used only by the A* span expansion (`binary_right_parents` calls
`step_det`-style logic), bounding the span path with `R: DetBottomUpTa`. This
leaves `InvHom::step` untouched but duplicates logic and only helps the binary
concat case. `InvHom` already has an allocation-free deterministic path
(`eval_term_det`, `invhom.rs:80-96`).

**Risk.** Low for the general fix; the only correctness concern is preserving
dedup for duplicate-producing images, handled by threshold escalation.

---

### P2 — Backpointer maintenance is dead work in chart mode

**Location:** written at `src/astar.rs:919` (in `pop_next_finalized`), resized at
`src/astar.rs:434-436` (`grow_to`); read **only** at `src/astar.rs:1298` and
`src/astar.rs:1347`, both inside the one-best entry points
(`astar_one_best_with_stats_and_span_sibling` / `_and_index`).

**What happens.** Every finalized product writes

```rust
self.back[product.index()] = Some(Backpointer {
    symbol: item.edge.symbol,
    children: item.edge.children.clone(),
    weight: item.inside,
});
```

`pop_next_finalized` is shared by both the chart materializers and the one-best
extractors. The chart entry points
(`materialize_astar_intersection_with_index` / `_with_span_sibling`) never call
`build_tree`, so `back` is written for every finalized product and never read.
On a full PTB chart that is one wasted `Option<Backpointer>` write (plus a
`children` clone) per finalized product state.

**Leverage.** Saves one struct write + `SmallVec` clone per finalized product in
chart mode. The clone is inline for arity ≤ 2 (no heap), so this is a smaller win
than P1, but it is trivially safe dead-work removal scaling with the number of
output states.

**Proposed fix.** Thread a `track_backpointers: bool` into `AstarContext` (true
only for one-best entry points; equivalently gate on `self.builder.is_none()`)
and skip the `back` write in `pop_next_finalized` and the `back` resize in
`grow_to` when false.

**Risk.** Trivial; behavior-preserving for both modes.

---

### P3 — Redundant per-candidate work in the span binary inner loop

**Location:** `src/astar.rs:486-546` (`push_candidate`), called from
`src/astar.rs:796-822`; `binary_right_parents` at `src/astar.rs:668-692`.

**What happens.**

1. For a fixed sibling, the child tuple `(trigger_product, sibling.product)` is
   constant, so the child-inside product
   `best_inside[child0] * best_inside[child1]` is constant across all symbol
   groups and all rules in a group. But `push_candidate` recomputes `inside` from
   scratch by looping over `children` (lines 496-499) for **every** rule, and the
   `children` SmallVec is `.clone()`d per rule (line 812). With many rules per
   group over 334M candidates this is repeated multiply/clone traffic.
2. `binary_right_parents` builds **two** SmallVecs — `raw_parents:
   SmallVec<[Span; 4]>` then `parents: SmallVec<[StateId; 4]>` — and re-loops to
   intern each parent span. It can intern directly into a single output buffer.

**Leverage.** Shaves a constant per-candidate cost off all 334M candidates
(P1/P5 reduce the *count* of expensive sub-operations; this reduces the
*per-candidate* fixed cost). Modest individually but broad.

**Proposed fix.** Compute the child-inside product once per sibling and pass it
to a lighter `push_candidate` variant that does `inside = rule_score(weight) *
child_product`. Fold `binary_right_parents` into a single interning pass and let
it write into a reusable scratch buffer (matching the existing
`span_product_siblings_scratch` / `matches_scratch` pattern).

**Risk.** Low; arithmetic and buffering only.

---

### P4 — Agenda heap is rebuilt from scratch on every growth

**Location:** `src/astar.rs:201-205` (default `index_bound = 1024`),
`src/astar.rs:215-230` (`ensure_index`).

**What happens.** `AstarAgenda` wraps `QuaternaryHeapOfIndices` whose index bound
is fixed at construction. When a product index reaches the bound, `ensure_index`
copies all live entries to a `Vec`, builds a fresh heap at double the bound, and
re-pushes every entry:

```rust
let entries: Vec<_> = self.heap.as_slice().to_vec();
let mut new_heap = QuaternaryHeapOfIndices::with_index_bound(new_bound);
for (node, key) in entries { new_heap.push(node, key); }
```

Starting at 1024 and doubling means a PTB chart with millions of product states
triggers ~11+ full rebuilds, each O(live heap size) (and each re-push is
O(log n)), late rebuilds dominating.

**Leverage.** Removes most of the geometric rebuild cost. Low-to-medium; depends
on how large the live heap grows.

**Proposed fix.** Seed a larger initial `index_bound` and/or grow it
proportionally to `product_pairs.len()` (product IDs are dense, so the count is a
direct upper bound on indices). The orx heap bound is fixed at construction, so
the rebuild itself is unavoidable on growth — the goal is to minimize rebuild
*frequency*.

**Risk.** Low; the only tradeoff is a larger index array (memory). Validate that
a larger initial bound does not regress small inputs.

---

### P5 — Candidate dominance (highest ceiling, profiling-dependent)

**Location:** dominance check at `src/astar.rs:522-526`; product-id resolution at
`src/astar.rs:501-514` → `get_or_create_product_id` (`materialize.rs:981-1004`)
and `get_or_create_product_id_direct` (`materialize.rs:1006-1020`);
`ProductStateMap` lookup at `materialize.rs:195-199`.

**What happens.** ~222M of 334M candidates are discarded because their `inside`
does not beat `best_seen_inside[parent]`. The dominance check itself is cheap
(one array read + compare) and already short-circuits *before* scoring, pending
writes, and heap updates. The remaining cost paid by every dominated candidate
is (a) the `inside` computation and (b) the **product-id resolution**, which is a
`by_right[right.index()]` vector index plus an `FxHashMap<StateId, StateId>`
lookup. Over 334M candidates the product-id hash lookup is the dominant
per-candidate cost.

**Why it is subtle.** The design doc suggests aggregating the best candidate per
parent *before* `push_candidate`. But identifying the parent requires the
product-id lookup, so aggregation cannot avoid the dominant cost unless it
aggregates on the raw `(parent_left, parent_right)` pair. Moreover, most
dominance is *cross-expansion*: the same parent span is reached from many
split points that finalize at different times (classic CKY ambiguity). Those
cannot be collapsed within a single expansion; they are exactly what the
`best_seen_inside` check exists to catch. Aggregating within one expansion only
helps the subset where one finalized trigger generates several candidates for the
same parent (e.g. distinct source symbols whose hom image is the same `concat`
term and whose left rules share a result state).

**Candidate directions (need profiling first).**
- Cheaper product-id resolution for the dominance check (e.g. a dense
  `Vec<Option<StateId>>`-per-right representation), traded against memory —
  contradicts the deliberate right-major sparse `ProductStateMap` choice, so
  benchmark carefully.
- Reduce the *number* of candidates generated rather than filtering them after
  the fact.

**Recommendation.** Treat P5 as a profiling-guided follow-up after P1–P4 land and
the profile is re-taken. The `astar-join-replay` binary already exists to study
candidate-generation strategies in isolation and is the right tool for this.

---

## Summary table

| ID | Opportunity | Location | Leverage | Risk |
| -- | ----------- | -------- | -------- | ---- |
| P1 | Remove per-call `FxHashSet` in `InvHom::step` | `invhom.rs:106`; `astar.rs:682,735` | High (~10^8 allocs) | Low |
| P2 | Skip dead backpointers in chart mode | `astar.rs:919,434,1298,1347` | Medium | Trivial |
| P3 | Hoist child-inside product; single-pass `binary_right_parents` | `astar.rs:486-546,668-692` | Medium (broad) | Low |
| P4 | Pre-size agenda heap to cut rebuilds | `astar.rs:201-230` | Low–Medium | Low |
| P5 | Reduce dominated-candidate cost | `astar.rs:522-526`; `materialize.rs:195-199` | Highest ceiling | Medium (profiling-led) |

## Things that are already good (no change recommended)

- `SpanProductSiblingFinder::sibling_products_into` (`string.rs:122-151`) is
  allocation- and hash-free: direct vector indexing by span boundary and
  `left_state.index()`, results appended into a caller-reused buffer.
- The agenda stores one pending item per product with decrease-key updates;
  dominated candidates short-circuit before scoring/heap work.
- Scratch buffers are already reused via the `std::mem::take` pattern
  (`matches_scratch`, `right_rule_ids_scratch`, `span_product_siblings_scratch`).

---

## Verification strategy

1. **Correctness.** `cargo test` — the `astar` module tests assert equivalence of
   A* output against the indexed and top-down condensed materializers
   (`astar_chart_viterbi_matches_indexed_materializer`,
   `string_sibling_astar_matches_old_index_and_topdown_for_binary_unary_rules`,
   the fallback and partner-set tests, and the `reopen_attempts == 0` invariants).
   P1 specifically must keep `InvHom::step` dedup behavior; add/keep a test with a
   duplicate-producing image to exercise the threshold-escalation path.
2. **Isolated candidate-generation cost.** `src/bin/astar-join-replay.rs`
   (strategies incl. `singleton-no-alloc`, `exact-binary`) for the generic join
   path; note it does **not** cover the span `right.step` path that P1 targets.
3. **End-to-end timing.** `src/bin/ptb-eval.rs` with
   `--strategies astar-zero` (stress) and `astar-sx`/`astar-outside` (production)
   on representative PTB sentences; compare parse time before/after. The design
   doc's PTB20 `astar-zero` ~103s and PTB sentence-20 `astar-sx` ~14.3s are the
   reference points.
4. **Micro-benchmarks.** `cargo bench` (`benches/phase1.rs`) for the
   step/materialize micro-benchmarks; consider adding an `InvHom::step` binary
   `concat` micro-bench to directly measure the P1 allocation removal.
5. **Re-profile.** After P1–P4, take a fresh `sample`/profiler trace on a long
   PTB sentence to decide whether P5 (dominance) or `right.step` volume is the
   next bottleneck, per the design doc's stated methodology.
