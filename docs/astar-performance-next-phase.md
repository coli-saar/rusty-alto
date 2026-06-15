# A* Parser — P5 and Next-Phase Performance

This is the follow-up to `docs/astar-performance-audit.md`. P1–P4 from that audit
have landed; this document diagnoses why the SX heuristic is not yet delivering a
Klein & Manning–scale wall-clock win, then lays out the next round of work
(P5 plus new findings N7–N10), in recommended order.

## Status of P1–P4

Landed in `src/astar.rs` / `src/algebras/string.rs`:

- **P1** was taken via the *narrow* route: the span path now uses deterministic
  stepping (`right.step_det`, `binary_right_parent_det`, `eval_term_det`) under a
  `R: DetBottomUpTa<State = Span>` bound instead of `InvHom::step`. `InvHom::step`
  and its per-call `FxHashSet` are untouched (still used by the generic path).
  The design doc reports this alone cut PTB20 `astar-sx` ~78s → ~43s and
  `astar-outside` ~77s → ~59s.
- **P2** `store_backpointers` (= `!with_builder`) gates the `back` writes/resize.
- **P3** `push_candidate_with_child_score` hoists the child-inside product;
  `binary_right_parent_det` returns a single `Option<StateId>` (one interning
  pass, no double `SmallVec`); children are passed as `[StateId; 2]`/`[StateId;1]`
  arrays, so the only `SmallVec` collect left is the surviving-candidate
  `EmitEdge` (after the dominance gate).
- **P4** `string_product_heap_bound` pre-sizes the agenda to
  `num_left_states × spans`; default bound 16K; growth ×4.

## Why the SX heuristic isn't giving Klein & Manning's ~80% wall-clock win

Measured from `times-150626-opt.csv` (one-best, no chart). The heuristic **is**
delivering K&M-scale *edge* reductions — `finalized_states` for astar-sx vs the
exhaustive `topdown` baseline: sent 1 −95.6%, sent 13 −93%, sent 8 −98.7%,
sent 20 −62%, sent 4 −42%. The algorithm is fine. What does not follow is
wall-clock, because per-finalized-state cost (µs = total_ms·1000/finalized)
*rises* as the heuristic improves:

| sent | topdown | astar-zero | astar-outside | astar-sx |
| ---- | ------- | ---------- | ------------- | -------- |
| 1    | 0.68    | 1.53       | 3.48          | 6.74     |
| 13   | 0.85    | 1.04       | 2.44          | 4.68     |
| 20   | 1.35    | 1.69       | 1.92          | 2.39     |
| 4    | 1.31    | 1.74       | 2.02          | 2.30     |

On sent 1, astar-sx touches ~22× fewer states than exhaustive but is only 2.3×
faster; on sents 4 and 7 it is *slower* despite far fewer states. Three causes:

1. **Per-edge constant ≈ 10× exhaustive CKY.** Each finalized state spawns ~tens
   of candidate pushes, each paying **two hashes** (product-id map + span
   interner) plus a decrease-key sift for survivors, in cache-hostile merit
   order; `topdown` fills chart arrays in span order. → addressed by **N7 + P5**.
2. **Fixed per-sentence grammar-index rebuild (N9 below).** `left.rules().collect()`,
   `LeftIndex::build`, `SpanAstarLeftIndex::build` are sentence-independent but
   rebuilt every parse; on short sentences this dilutes an 84% edge cut to a 29%
   time cut.
3. **Heuristic decays with sentence length** (sent 4 only −42% edges vs −95% on
   sent 1): the SX summary is coarse and ambiguity grows superlinearly, so the
   frontier stays large exactly where exhaustive's low constant wins.

Takeaway: the algorithmic win is already in the edge counts; converting it to
wall-clock is the per-edge-overhead work below (N9, N7, P5), with N10 for the
residual heap ceiling.

## Where the per-candidate cost actually is (reframing P5)

For the span path, `push_candidate_with_child_score` (`src/astar.rs:524-582`)
runs in this order:

1. compute `inside` (one multiply);
2. **product-id resolution** `get_or_create_direct` / `get_or_create_product_id`
   → `ProductStateMap::get` = `by_right[right.index()]` (vec index) + an
   `FxHashMap<StateId,StateId>::get(&left)` **hash** (`src/materialize.rs:195`);
3. `grow_to` + `finalized.contains` (the `finalized_candidate_discards` exit);
4. dominance compare `best_seen_inside[parent]` (the `dominated_candidates` exit);
5. **survivors only**: `best_seen` write, `h.outside_estimate` (verified O(1): a
   `Vec` index for `OutsideHeuristic`/`SxHeuristic`, constant for
   `ZeroHeuristic` — not worth caching), `merit`, `EmitEdge` collect, and one
   decrease-key sift in the indexed heap.

Two corrections to the design doc's framing:

- The "**222M dominated of 334M**" figure overstates the savings from filtering
  earlier: dominated/finalized candidates already short-circuit *before* scoring,
  the heuristic, the `EmitEdge` collect, and the heap. The only non-trivial cost
  they still pay is **step 2, the product-id hash** (and, in the binary path, the
  span-intern hash below).
- The genuinely expensive residual is **step 5 for the ~112M survivors**: one
  decrease-key sift each (≈ `heap_pushes + heap_updates`). This is inherent to
  best-first A* and is the hard ceiling (addressed only by N10).

So the tractable wins are about **removing hashing from the per-candidate path**,
not about the dominance test itself.

There is a *second* hash per candidate that the audit missed:

- `binary_right_parent_det` (`src/astar.rs:701-718`) calls
  `right_interner.intern(parent)` for the parent span. The interner is a
  `FxHashMap<Span,StateId>` (`src/interner.rs:44`). It is called once per
  `symbol_group`, and in a PCFG `rule_indexes.len() ≈ 1` per group, so the
  span-intern hash is effectively **per candidate**, same order as the
  product-id hash. The unary branch interns too (`src/astar.rs:765`).

## N9: build grammar-only indexes once (highest leverage for short sentences / batch)

The span one-best/chart entry points rebuild, **per sentence**, structures that
depend only on the grammar (left automaton), not the sentence:

- `left_rules: Vec<OwnedRule>` — clones every grammar rule
  (`src/astar.rs:1317-1325`, and the chart entry similarly);
- `LeftIndex::build(&left_rules)` (`src/astar.rs:1326`);
- `SpanAstarLeftIndex::build(self.left_rules)` inside
  `run_with_span_product_sibling_finder` (`src/astar.rs:1005`).

For a large PTB grammar these are O(grammar size) and independent of the input,
so in a batch parse (20+ sentences, same grammar) the work is repeated every
time. The per-finalized-state table above shows short sentences barely benefit
from the heuristic — this fixed overhead is a large part of why.

**Fix.** Build `left_rules`, `LeftIndex`, and `SpanAstarLeftIndex` once per
grammar and pass them into the per-sentence entry points (a
`PreparedAstarGrammar` the caller constructs once and reuses; `ptb-eval` builds
it before the sentence loop, next to the SX/Outside precompute it already
hoists). `AstarContext` already borrows `left_rules`/`left_index`, so this is a
plumbing change, not an algorithm change. **Risk.** Low; the indexes are pure
functions of the grammar. Verify identical output and that `ptb-eval` short
sentences drop in `parse_ms`.

## N7: perfect-hash span ids instead of a `FxHashMap` interner

**Idea.** A `Span{start,end}` with `0 ≤ start < end ≤ n` is a tiny dense key.
Replace the generic `Interner<Span>` *on the span path* with a perfect hash
`code(start,end) = start*(n+1)+end` (or triangular packing). Use the code
directly as the right `StateId`. Then:

- every `right_interner.intern(span)` (binary + unary, ~per candidate) becomes
  arithmetic, no hashing;
- every `right_interner.resolve(id)` (per survivor at `src/astar.rs:565`, per
  finalize at `:953`/`:1009`) becomes a decode (no `Vec` indirection);
- `ProductStateMap::by_right` is indexed by the span code directly (range
  ≤ (n+1)², trivially small — n≈40 ⇒ ≤1681 rows).

**Leverage.** Removes a whole `FxHashMap` from the hottest path, benefiting
*all* candidates (dominated and survivors), not just a subset. Span space is
tiny so there is no memory tradeoff. Subsumes the minor N3 below.

**Scope.** The span entry points are already string-specialized
(`materialize_astar_string_intersection_with`,
`astar_one_best_with_stats_and_span_sibling`). Introduce a `SpanInterner`
(or make `AstarContext` generic over an `Intern<R::State>` trait with a
`SpanInterner` impl) used only by these. The generic `CondensedTa` path keeps
the hashmap `Interner`. `is_accepting` (`span == (0,n)`) and nullary seeding work
unchanged through decode.

**Risk.** Low. Behavior-preserving; the only care is keeping `StateId::STUCK`
out of the code range and a clean decode for `resolve`.

## N8: skip dead `finalized_partners` maintenance in pure-binary span mode

`pop_next_finalized` (`src/astar.rs:955`) does
`finalized_partners[right].insert(left, product)` on **every** finalize. In the
span path the siblings come from `SpanProductSiblingFinder` (populated by
`activate_product`, `:1010`); `finalized_partners` is read **only** by the
generic `expand_from_finalized` fallback (`:626`, `:668`), which the span path
enters only when `SpanAstarLeftIndex::has_higher_arity(trigger_left)` is true.
For a fully binarized grammar (no arity > 2 left rules — the PTB case) the
fallback never runs, so the per-finalize `PartnerSet::insert` (grows/touches a
bitset + two `Vec`s) is dead work scaling with the number of finalized states.

**Fix.** `SpanAstarLeftIndex` already knows `higher_arity_left`; expose
"any higher-arity left state exists" and, in the span run loop, skip the
`finalized_partners` insert when false. Analogous to P2's dead-work removal.
**Risk.** Trivial; gate strictly on "fallback unreachable".

## P5: dense dominance gate before product-id resolution — **TRIED & REVERTED**

**Verdict.** Implemented, measured, and then **reverted**. The gate is
correctness-neutral (all 20 parses bit-identical) but delivers **no measurable
wall-clock gain** (~1–2% expected from first principles, buried under ±12%
machine noise) *and* costs **~10× more memory** than the product-keyed
`best_seen_inside` it replaced. Measured gate footprint vs realized products on
PTB `sentences20` (astar-sx, one-best): 450 MB vs 5.9M products (~10×) on the
biggest sentence, up to ~17× on others — a large slice of the 3.17 GB peak RSS.
Root cause is structural: gating *before* product-id resolution forces a key on
raw `(span, left)`, and with 77,546 scattered nonterminals the dense rows are
~90% empty; the only ways to make them sparse reintroduce the very hash the gate
was trying to avoid. The product-keyed `best_seen_inside` is both memory-lean
(one slot per realized product) and time-equivalent, so it wins. `src/astar.rs`
was restored to the pre-P5 baseline (empty diff vs HEAD). **Recommendation:
do not pursue P5; the dominance test is not where the time goes.**

---

**Status (the original idea, for the record).** The product-keyed
`best_seen_inside` was replaced by a dense gate `seen_inside_by_right:
Vec<Vec<f64>>` indexed `[parent_right.index()][parent_left.index()]` with
lazily grown rows (`gate_admits`). The dominance test now runs *before*
product-id resolution in both `push_candidate_with_child_score` and
`push_seed`, so dominated candidates never touch the `ProductStateMap`
hashmap. No finalized check is kept on the survivor path (see the
floating-point note below); the pre-existing pop-side reopen guard handles the
rare rounding cases.

**Measured (PTB `sentences20`, astar-sx, one-best).** Deterministic and exact:
all 20 parse weights bit-identical to baseline; `finalized_states`,
`heap_pushes`, `heap_updates` unchanged. The gate rejects **183.6M of 237.8M**
candidates (77%) before product-id resolution — the old `dominated` (165.3M)
plus the old `finalized_candidate_discards` (18.3M), confirming the gate
subsumes both exits exactly.

**Wall-clock: no measurable win — the change is a wash.** First principles:
the gate replaces, for ~183.6M dominated candidates, one `FxHashMap<u32,u32>`
integer lookup (per-right contiguous table) with a `Vec<Vec<f64>>` double index
(a pointer chase into the row). Both are O(1); the expected delta is on the
order of a couple of ns × 183.6M ≈ **0.5s of a ~33s run (~1–2%)**, and the sign
is not even obvious (the per-right hashmap may have *better* cache locality than
the row-of-rows). This is far below the test machine's run-to-run noise:
identical back-to-back runs span **30.8–38.0s (±~12%)**, and the numbers drift
upward across a session as the machine heats. An earlier "best-observed ~6%"
was thermal luck, not signal. Bottom line: P5 is **correctness-neutral and
performance-neutral within noise** — it removes a hashmap from the hot path
(arguably cleaner) but does not deliver a reliable speedup. A definitive
measurement would need an in-binary A/B toggle interleaved over many runs.

**Subtlety found — NOT SX inadmissibility, it's floating-point.** Removing the
product-keyed `best_seen` exposed 192 `reopen_attempts` where the baseline had
0. Instrumenting the exact 192 candidates: every one has `inside` strictly
greater than the finalized `best_inside` by **1–64 ULP** (absolute gap
1.8e-15 … 1.4e-14; max *relative* gap 2.2e-14, vs f64 ε≈2.2e-16), with merit
values identical to 12 digits. So SX is *not* inadmissible: the count-based SX
is a max-product (Viterbi) outside computation over a word-count relaxation,
seeded at accepting states and propagated parent→child by `max` — admissible and
consistent by construction. By heap monotonicity a *strict* reopen can't come
from a consistent heuristic at all; what actually happens is log-prob
non-associativity — the same product's inside, recomputed along an equal-weight
(or exactly-tied) derivation discovered after finalization, lands 1 ULP higher,
and the strict `>` in `scorer.better` calls that last-bit difference an
"improvement." It would occur with *any* heuristic, including `ZeroHeuristic`.
These 192 re-pushes (of 36M) are caught and discarded by the existing pop-side
guard; the final parses are unaffected (all 20 bit-identical). The earlier
workaround (a finalized check on the survivor path) was removed as unnecessary
scaffolding for pure rounding noise; `reopen_attempts` now reads 192.

  *Where genuine SX inadmissibility could come from (none observed here):* an
  over-estimated `minwidth(X)` or feasibility check (`remaining < min_sum`) that
  wrongly excludes a valid narrow context would push `SX(X,l,r)` *below* the true
  outside (under-estimate ⇒ inadmissible ⇒ real reopens). A *looser* relaxation
  errs the safe way (higher h is still an upper bound). The observed gaps are
  pure rounding, far below any such structural effect.

**Memory.** The lazy-row `Vec<Vec<f64>>` had no observable memory problem on
PTB20; nonzero gate entries ≈ created products, and rows grow only to the max
left id seen per span.

---

**Idea (original).** Maintain a dense best-seen-inside keyed on `(right_code, left)` and
check it *before* step 2. Because the heuristic is consistent, once a product is
finalized its gate value equals its optimal inside, so a single
`!better(inside, gate[right][left])` test **subsumes both** the
`dominated_candidates` and `finalized_candidate_discards` exits — without
resolving or creating a product id. Only candidates that pass the gate (the
~1/3 survivors) then resolve the product id for the pending/heap update.

This removes the product-id hash (step 2) for the ~2/3 of candidates that are
discarded, and turns the dominance read into a 2-D array index.

**Why aggregation-before-push (the design doc's suggestion) is weaker.** Most
dominance is *cross-expansion*: the same parent span+nonterminal is reached from
many split points that finalize at different times (CKY ambiguity). Those cannot
be collapsed inside one expansion. Within a single trigger's expansion the same
parent is rarely hit twice (a `symbol_group` is ~1 rule, and distinct siblings
give distinct parent spans). The gate, unlike aggregation, catches the
cross-expansion case — which is the bulk.

**Cost / caveat (must benchmark).** The gate is `Vec<Vec<f64>>` indexed
`[right_code][left]`. Worst-case width is `num_left_states`, so a fully dense
gate is `spans × num_left × 8 B` — for a long PTB sentence × a large grammar
this can be hundreds of MB, contradicting the deliberately sparse right-major
`ProductStateMap`. Mitigation: allocate each span row lazily and grow only to
the max left id actually seen for that span (reachable left states per span are
far fewer than `num_left`). Measure memory and wall-clock before keeping it.

**Sequencing.** Land N7 first, then **instrument**: split `dominated_candidates`
into within-expansion vs cross-expansion (and report
`finalized_candidate_discards`) to confirm the gate's reach, and re-profile.
Only then implement the gate. `src/bin/astar-join-replay.rs` is the isolation
harness; `src/bin/ptb-eval.rs` is the end-to-end one.

## N10: lazy candidate generation (attacks the survivor/heap ceiling)

**Framing.** The agenda is already a decrease-key heap with ≤ one entry per
*pending product* (`heap.update_or_push(parent.index(), merit)` +
`pending: Vec<Option<AgendaItem>>`), not one per candidate edge. A literal
"agenda of only finalized items" can't drive best-first (Knuth/Dijkstra needs
the open frontier to pick the next finalization). But the explored *frontier*
(pending products) is much larger than the finalized set — the SX heuristic
shrinks finalized states ~20× but not the frontier — and that frontier sizes
every big per-product array (`pending`, `best_inside`, `best_seen_inside`,
`back`, `finalized`, heap index) and drives the ~112M decrease-key sifts (the
survivor "hard ceiling").

**Idea (Pauls & Klein 2009, *K-Best A\* Parsing*; lazy/cube frontier).** When an
item finalizes, push only its single best outgoing combination instead of all
`siblings × rules` candidates; when that is popped, advance the item's generator
to its next-best combination and re-key. Live heap entries then track ~O(#finalized)
rather than O(frontier), and heap operations drop from ~#candidates (≈112M) toward
~#finalized (≈5.6M) — a potential ~20× cut in the dominant cost given the ~60:1
candidate:finalized ratio. Stays exact (not cube *pruning*) iff each generator
yields combinations in non-increasing merit.

**Cost / risk.** Requires per-combination-site nested priority structures
(siblings ordered by merit, arriving over time) with their own constant factor;
real exactness/consistency risk. Significant restructuring — do last.

**Algebra independence & reuse of `SortedLanguageIterator`.** The algebra-specific
part is already isolated behind the candidate source (`SpanProductSiblingFinder` +
`binary_right_parent_det` for spans; the right-rule/set-trie join for the generic
path). N10's lazy *frontier* (per-site sorted streams, on-demand next-best, dedup,
merit ordering) can be fully algebra-independent over `StateId`/`f64` —
`src/sorted_language.rs` is the precedent that this works (it touches only
`Explicit` + `TopDownTa`, nothing span-specific). The lazy-stream *pattern* and
the monotonicity assumption are shared, but the structures do **not** line up for
direct reuse:

- SLI lazily *enumerates* k-best over an already-built chart top-down (fixed rule
  set per state via `rules_topdown`); N10 *builds* the chart bottom-up with
  **append-only growing** sibling streams discovered during the run.
- SLI's `UnevaluatedItem`/`variations()`/`discovered` is a fixed-arity child-rank
  lattice (Huang–Chiang Alg. 3); N10's binary combination fixes the trigger and
  has a single *growing* sibling axis — closer to "merge trigger against a per-site
  heap of finalized siblings" than an n-ary rank lattice.
- SLI keys on inside weight with no cross-stream collisions; N10 keys on merit and
  the same parent is reachable from many sites, so the **decrease-key parent heap
  stays** (lazy generation cuts candidates-emitted-per-finalize, not parent dedup).

Shareable nugget: extract SLI's lazy-merge core (`evaluated` heap + `variations()`
+ `discovered`) into a generic `LazyBestMerge` (also cleans up SLI), then check at
prototype time whether N10's growing-axis generator fits it or is cleaner
purpose-built. Decide reuse after the prototype, not before.

## N3 (minor, subsumed by N7)

In the binary loop the parent span depends only on `right_children`, which is
fixed per sibling; `step_det` + `intern` are redundantly repeated per
`symbol_group`. N7 makes interning free, so this collapses to at most a repeated
`step_det` (cheap arithmetic). Not worth a separate change once N7 lands.

## Recommended order & verification

0. **Instrument first (cheap):** emit `heap_pushes`/`heap_updates` and the
   dominated/finalized discard split in `ptb-eval`. Bounds the payoff of P5 and
   N10 before building either.
1. **N9** (build grammar-only indexes once) — directly recovers the short-sentence
   gap between edge reduction and wall-clock; low risk.
2. **N7** (perfect-hash span ids) — removes one of two per-candidate hashes; low
   risk, no memory cost.
3. **N8** (skip dead `finalized_partners`) — trivial dead-work removal.
4. **P5** dense gate — only if instrumentation confirms reach; benchmark memory.
5. **N10** (lazy candidate generation) — largest restructuring; attacks the
   survivor/heap ceiling; do last, validated against the equivalence tests.

**Verify:**

- `cargo test` — A*-vs-indexed/topdown equivalence
  (`astar_chart_viterbi_matches_indexed_materializer`,
  `string_sibling_astar_matches_old_index_and_topdown_for_binary_unary_rules`,
  the `reopen_attempts == 0` invariants). For N7 add a test that span↔id round
  trips and that accepting detection still fires on `(0,n)`.
- `src/bin/ptb-eval.rs --strategies astar-sx` (production) and `astar-zero`
  (stress) on representative PTB sentences; reference points: `astar-sx` ~43s,
  `astar-zero` ~103s on PTB20.
- `src/bin/astar-join-replay.rs` for isolated candidate-generation cost;
  `cargo bench` (`benches/phase1.rs`) for step/materialize micro-benchmarks.
