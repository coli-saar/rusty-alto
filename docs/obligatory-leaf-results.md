# Obligatory-leaf filter coverage (Step 1 probe results)

## Summary

The F-heuristic's obligatory-leaf filter **has teeth** in this grammar. **79.4% of item-eligible states carry structural/grammatical constraints** on terminals they must emit, making them suitable candidates for outside-context filtering.

## Full results (PTB grammar, `~/Documents/workspace/alto/ptb/out.irtg`)

```
Grammar: 77745 states
Using interpretation: "string"
Flat rules: 113684  accepting: 62

=== Obligatory-leaf coverage report ===
total states      : 77745
productive        : 77745
root-reachable    : 77745
|U| (both)        : 77745

Over |U|:
  mic non-empty       : 67534 / 77745 = 0.869
  req_left non-empty  : 34852 / 77745 = 0.448
  req_right non-empty : 37910 / 77745 = 0.488
  req_any non-empty   : 61709 / 77745 = 0.794  ← HEADLINE

Obligation size distribution (states with req_any non-empty: 61709):
  distinct terminals: min=1 median=1 mean=1.7 p90=3 max=9
  total count       : min=1 median=2 mean=2.0 p90=4 max=24
```

### Key findings

1. **Headline metric: 79.4%** of states in the reachable-productive universe carry
   non-empty `req_left` or `req_right`. This far exceeds the "go" threshold of ~30%
   and indicates strong structural commitment.

2. **Obligation sizes are tractable:**
   - Median obligation size: **1 distinct terminal** (many states commit to exactly one
     required leaf).
   - Mean: **1.7 distinct**, p90: **3 distinct** — focused, not bloated.
   - Total occurrence counts are small (median 2, p90 4) — low-cost lookups.

3. **Top 15 obligatory terminals are grammatical, not noise:**

   ```
   18268 states  ","              (commas — sentence/clause structure)
   10552 states  "NN"             (nouns — core structure)
   10455 states  "."              (periods — clause/sentence boundaries)
    8456 states  "CC"             (coordinating conjunctions)
    7647 states  "NNP"            (proper nouns)
    5987 states  "''"             (closing quotes)
    5858 states  "NNS"            (plural nouns)
    5511 states  "JJ"             (adjectives)
    5336 states  "``"             (opening quotes)
    5335 states  "DT"             (determiners)
    3293 states  "VBD"            (past verbs)
    2636 states  ":"              (colons)
    2621 states  "VBN"            (past participles)
    2145 states  "VB"             (base verbs)
    1871 states  "CD"             (cardinal numbers)
   ```

   These are real grammatical categories and punctuation, not spurious high-frequency
   tokens. A state that forces commas/periods/quotes is expressing genuine syntactic
   constraints.

4. **Distribution across left/right:**
   - 44.8% carry `req_left` obligations (words/tags the state must emit before it).
   - 48.8% carry `req_right` obligations (words/tags after it).
   - 79.4% carry at least one (orthogonal dimensions, both contribute).

### Example states with obligations

```
  state 7:   req_left=[]           req_right=[.:1, ::1]        (expects period or colon to right)
  state 25:  req_left=[VB:1]       req_right=[]                (past tense verb to left)
  state 36:  req_left=[CC:1]       req_right=[.:1]             (conjunction left, period right)
  state 38:  req_left=[VBD:1]      req_right=[]                (past tense verb to left)
  state 94:  req_left=[,:1]        req_right=[.:1]             (comma left, period right)
  state 123: req_left=[,:2]        req_right=[.:1]             (two commas left, period right)
  state 153: req_left=[VB:1, ::1]  req_right=[.:1]             (verb/colon left, period right)
  state 189: req_left=[VBG:1]      req_right=[ADVP-PRP-4:1]    (gerund left, complex right)
  state 197: req_left=[::1, RB:1]  req_right=[.:1, ,:2]        (colon/adverb left, period/commas right)
```

## Decision

**Verdict: PROCEED to Step 2** (strong coverage).

The 79.4% coverage and low obligation sizes make an F-style filter viable. The
next step measures **real pruning on sentences20** via the `inside(s)·h(s) ≥ P*`
finalization metric — i.e., how many A* items the filter actually removes when
combined with SX.

Step 2 will predict, for each heuristic candidate, how many states finalize
(`predicted_finalized(h)`) and compare `SX` vs `SX+F` against an oracle (the true
outside weight). The Step-1 results here show that F has enough coverage to make
that measurement worthwhile.

---

# Step 2 — predicted-pruning probe (results)

**Verdict: CONFIRMED — proceed to Step 3.** Combining F with SX via `min` cuts the
A\*-predicted finalized set by **53.4%** on top of SX alone, and the SX predictor
is **bit-identical** to the real `astar-sx` `finalized_states`.

## Method

`src/bin/f-step2-probe.rs`. For each sentence in `sentences20.txt` we build the
exhaustive fine chart (`materialize_indexed_condensed_intersection_with_pairs`,
newly exposing the internal `product_pairs` map), compute Viterbi inside weights
and `P*` in log-prob space, and tally K&M's finalization predictor
`predicted_finalized(h) = #{ reachable s : inside(s)·h(s) ≥ P* }` for
`h ∈ {zero, SX, F, min(SX,F)}`. Everything is in log-prob space (merit =
`inside + h`, F = `0` pass / `−∞` prune, `min` = numeric min) to match the
`LogProbabilityScorer` A\* path and avoid underflow. SX is loaded from the
`out.irtg.sxcache/nmax41.bin` cache (the n_max=41 build is ~3.5 GB / multi-minute).

## Headline (20 sentences, 49.78M reachable items)

| heuristic    | finalized   | fraction | saves vs zero | saves vs SX |
|--------------|-------------|----------|---------------|-------------|
| zero (Knuth) | 33,625,941  | 0.675    | —             | —           |
| SX           | 15,294,558  | 0.307    | 54.5%         | —           |
| F (alone)    | 13,248,427  | 0.266    | 60.6%         | +13.4% (worse than SX) |
| **min(SX,F)**| **7,134,727** | **0.143** | **78.8%**   | **53.4%**   |

F alone is slightly weaker than SX, but the two are **orthogonal** (F is an
outside *terminal-supply* filter, SX an outside *width/weight* bound): their `min`
finalizes barely over half of what SX alone does. This is exactly the
inside-feasible / outside-impossible class SX wastes pops on.

## SX self-validation (exactness check)

The SX predictor must equal the real A\* `finalized_states` (SX is a consistent
heuristic ⇒ A\* finalizes exactly `{s : inside·h ≥ P*}`). Cross-checked against
`ptb-eval … --strategies astar-sx`:

- **Per sentence: identical for all 20** (38209, 11787, 277581, 3766264, …).
- **Total: 15,294,558 = 15,294,558** (probe `sx_fin` == `ptb-eval`
  `total_finalized_states`). Bit-exact ⇒ the predictor is correct, so the
  `min(SX,F)` projection is trustworthy.

## Per-sentence (`reachable, zero, sx, f, min`)

```
 n=18   865350   238552    38209    82304    17332
 n=13   416798   119333    11787    34916     3943
 n=27  2838746  1332502   277581   493403   125698
 n=41  6476646  5704316  3766264  2470368  1830322
 n=35  5206946  3594587  1725572  1370266   767018
 n=27  2428647  1411772   380871   489747   174348
 n=37  4835175  4279230  2452765  1964983  1275449
 n=12   161940    21424     2090     6132      669
 n=16   697821   160575    16508    58618     6056
 n=10   142862    24975     1916     7482      769
 n=22  1245590   797514   236450   270451    95606
 n=26  2031582   767840   137619   290101    61939
 n=23  1591671   934913   112325   330476    45723
 n=38  5125417  4331344  2336724  1956139  1188324
 n=22  1597252   779801   141880   271349    63107
 n=24  1788544   824560   288685   290264   120183
 n=17   786719   261956    36939    82953    14937
 n=27  2914075  1835254   534205   637140   237276
 n=24  1635429   559920   109250   195797    45534
 n=40  6995829  5645573  2686918  1945538  1060494
```

The relative win is consistent across lengths; `min`/`sx` ranges ~0.40–0.55 per
sentence. The probe is grammar-deterministic and re-runnable:

```
cargo run --release --bin f-step2-probe -- \
    ~/Documents/workspace/alto/ptb/out.irtg \
    ~/Documents/workspace/alto/ptb/sentences20.txt
```


┌───────────┬───────────────────────┬──────────┐
│ heuristic │ finalized (of 49.78M) │ fraction │
├───────────┼───────────────────────┼──────────┤
│ zero      │ 33.6M                 │ 0.675    │
├───────────┼───────────────────────┼──────────┤
│ SX        │ 15.3M                 │ 0.307    │
├───────────┼───────────────────────┼──────────┤
│ F alone   │ 13.2M                 │ 0.266    │
├───────────┼───────────────────────┼──────────┤
│ min(SX,F) │ 7.1M                  │ 0.143    │
└───────────┴───────────────────────┴──────────┘


## Decision

**PROCEED to Step 3** (implement): promote the obligatory-leaf tables into the
library next to the SX builder (`YieldToken::Word(Symbol)`, `mic`/`req_left`/
`req_right` cached per grammar), add per-input terminal supply from the condensed
invhom, and wire `ObligatoryLeafHeuristic` + a generic `MinHeuristic<A,B>` as an
`AstarHeuristic` variant. The 53.4% predicted finalized-state reduction is the
headroom to realize, net of the cheap per-item supply check.

---

# Step 3 — implementation + real timing A/B

**Verdict: it makes the parser faster. ~18% less total parse time on `sentences20`
(up to ~23% on the longest sentences), with bit-identical Viterbi scores and a
one-time 0.3 s precompute.** The 53.4% finalized-state reduction predicted in
Step 2 is realized *exactly* by the real A\*, but wall-clock gains are smaller
because parse time is dominated by candidate generation, which F trims less.

## What was implemented (library, pure SX path untouched)

- `src/obligatory_leaf.rs`: `ObligatoryLeafTables::from_grammar` (grammar-only
  `mic`/`req_left`/`req_right` fixpoints, cached per grammar) and a per-sentence
  `ObligatoryLeafHeuristic` (terminal supply via sorted per-symbol positions +
  `partition_point`; `pass`/`prune` track the scorer's `one()`/`zero()`). It
  walks the homomorphism frontier directly rather than extending the SX
  `YieldToken` (so SX is byte-for-byte unchanged — a deliberate deviation from
  the design's `YieldToken::Word(Symbol)`, same intent, zero SX risk).
- `MinHeuristic<A,B>` (`src/heuristic.rs`): numeric `min` of two admissible
  bounds — admissible and exact in both prob and log-prob space.
- `AstarHeuristic::UniversalSxF { table, oblig, n }` + `ptb-eval` strategy
  `astar-sxf` (reuses the SX disk cache; builds F tables once).

## Exactness (must hold) — confirmed

Per-sentence Viterbi scores are **identical** for all 20 sentences between
`astar-sx` and `astar-sxf` (e.g. −41.0644080913, −104.7344090703, …); `ptb-eval`
prints no weight-disagreement warning. And `astar-sxf` `total_finalized_states`
= **7,134,727 = the Step-2 `min` prediction**, so the real A\* finalizes exactly
the predicted set — the implementation is correct end-to-end.

## Timing A/B (`ptb-eval out.irtg sentences20.txt --strategies astar-sx,astar-sxf`)

| metric                  | astar-sx    | astar-sxf   | change       |
|-------------------------|-------------|-------------|--------------|
| total parse ms          | 31,797.0    | 26,014.8    | **−18.2%**   |
| median parse ms         | 344.4       | 327.9       | −4.8%        |
| finalized states        | 15,294,558  | 7,134,727   | −53.4%       |
| heap pushes             | 36,361,455  | 33,439,845  | −8.0%        |
| candidate edges         | 237,845,007 | 228,658,043 | −3.9%        |
| sibling tuple queries   | 112,785,657 | 104,608,401 | −7.2%        |
| F precompute (one-time) | —           | 336 ms      | grammar-only |

Why finalized −53% but wall-clock only −18%: A\* spends most of its time
*generating and scanning candidate edges* (238M), and a finalized state that F
prunes still had its incoming candidates enumerated. F removes whole expanded
states (heap pushes −8%) but trims candidate scanning only ~4%. The win scales
with sentence length — the longest sentences gain most:

```
 n   astar-sx ms   astar-sxf ms   speedup
 41    8029.5         6446.8       -19.7%
 40    6028.3         4632.2       -23.2%
 38    5119.0         4362.0       -14.8%
 37    4618.6         3833.8       -17.0%
 35    3367.9         2617.7       -22.3%
 27     565.8          515.6        -8.9%   (sentence 3)
 12      12.6           13.0        ~0%     (tiny; F overhead ≈ win)
```

The F per-item cost (a few `partition_point` lookups, median 1 obligation) never
makes a sentence slower in aggregate; only the smallest sentences see it wash out.

## Reproduce

```
cargo build --release --bin ptb-eval
./target/release/ptb-eval ~/Documents/workspace/alto/ptb/out.irtg \
    ~/Documents/workspace/alto/ptb/sentences20.txt --strategies astar-sx,astar-sxf
```

## Bottom line

F + SX is a real, exact speedup (~18% total, ~20–23% on long sentences) for a
negligible 0.3 s grammar-only precompute. The headroom beyond this is in
candidate generation, not finalization — to convert more of the 53% finalized-state
cut into wall-clock, F would need to suppress candidate *enumeration* for pruned
states, not just their expansion.

## Profiling — why −53% finalized is only −18% wall-clock

Sampled `astar-sxf` with macOS `sample` (1 ms, 40 s window) on a heavy workload
(the 5 longest `sentences20` repeated; debuginfo via `CARGO_PROFILE_RELEASE_DEBUG=true`),
33,318 leaf samples. Self-time buckets:

| bucket                                              | self-time | scales with    |
|-----------------------------------------------------|-----------|----------------|
| invhom `eval_term_det` (per candidate)              | 18.7%     | candidates     |
| sibling + product-id generation (per candidate)     | 16.9%     | candidates     |
| decomp `step_det` (per candidate)                   | 7.7%      | candidates     |
| astar loop + `push_candidate_with_child_score`      | 21.3%     | mostly cand.   |
| heap ops (`heapify_*`)                              | 11.2%     | heap pushes    |
| **F+SX heuristic eval (`MinHeuristic`)**            | **8.3%**  | items (F cost) |
| `log()` scoring                                     | 5.5%      | candidates     |
| mem/alloc                                           | 9.8%      | mixed          |

**The diagnosis.** The run generates **1.17 B candidate edges** to finalize
**36.7 M** states — a **~32:1** candidate-to-finalized ratio. Roughly **43% of
self-time** is per-candidate-edge work (`eval_term_det` + sibling/product gen +
`step_det`), plus most of the 21% astar-loop bucket (`push_candidate…` 8.8%) is
also per-candidate. F's pruning happens at the *priority/finalization* level: a
state F kills gets priority `−∞` so it is never popped — but its incoming
candidates were **already enumerated and scored**, and candidate edges only fell
**−3.9%** (228.7 M vs 237.8 M on `sentences20`). So the 53% finalized-state cut
only trims the slices that scale with *finalized states / heap pushes* — heap ops
(−8%) and `pop_next_finalized` (~1.9%) — a minority of total time.

On top of that, F **adds** the `MinHeuristic` per-item cost (**8.3%** of runtime:
the F supply `partition_point` lookups + `min` + dispatch), which partially
offsets its own savings.

Net: dominant cost (candidate enumeration, ~64% of self-time) is upstream of the
pop/finalize step F prunes and is barely reduced ⇒ −53% finalized → −18% wall.

**To capture more of the 53%:** move the F test *earlier*, gating product-state
**activation** so a span F proves impossible never triggers its sibling-join
candidate generation (the `eval_term_det` / `step_det` / product-id work). Used
purely as an admissible A\* heuristic, F can only reorder/skip finalization, not
prevent the candidate enumeration that dominates runtime.

---

# Step 4 — F as a candidate-enumeration filter (the Step-3 follow-through)

**Verdict: it works, and it roughly doubles the win.** Consulting F as a **sound
edge filter at candidate-construction time** (not just as an A\* priority) cuts
`astar-sxf` total parse time to **−33% vs. the same binary with the filter off**
and **−44% vs. `astar-sx`** (up from Step 3's −18%), while staying **bit-exact**:
identical per-sentence Viterbi scores and `finalized_states` **unchanged at
7,134,727** (= the Step-2 `min(SX,F)` prediction).

## The idea (K&M 2003 / Pauls & Klein 2009)

F is not merely an admissible bound — it is a **sound 0/1 filter**: when F prunes,
the true outside weight is genuinely 0, so the item is in *no* parse. K&M 2003's F
got its bite as exactly this — "a sophisticated lookahead condition on suffixes …
dotted-rule edges committed to a rule's terminals" that **blocks edges** (80%→95%
edges blocked), not a collapsed-grammar reparse. Coarse-to-fine (Pauls & Klein
2009) is the same move: never *build* a fine edge a sound coarse model rules out.
Step 3 used F only as a priority (`merit = inside·min(SX,F)`, prune ⇒ `−∞`), which
skips *finalization* but leaves every candidate edge *into* an F-pruned parent fully
enumerated and `step_det`-ed. Step 4 consults F **before** building the edge.

## Implementation (exact; pure-SX path untouched)

- `IntersectionHeuristic` grows a sound filter hook `fn admits(left, right) -> bool`
  (default `true`, so SX / Outside / Zero impose no filtering). `MinHeuristic`
  admits iff **both** admit; `ObligatoryLeafHeuristic::admits = !prunes` (the same
  `req_left`/`req_right` vs. terminal-supply test, refactored out of `estimate`).
- The A\* span fast path
  (`expand_from_finalized_with_span_product_siblings`) tests `admits` on the
  **predicted concat span** of the parent (pos 0: `[trigger.start, sibling.end]`;
  pos 1: `[sibling.start, trigger.end]`) **before** the deterministic right
  transition, and computes `binary_right_parent_det` (= `step_det`) **lazily** —
  only once a rule survives F. A group whose every parent is hopeless never pays
  for `step_det`/`eval_term_det`. The unary path filters on the trigger span.
- A universal gate in `push_candidate_with_child_score` (true resolved span)
  catches the generic / higher-arity fallback path, skipping product-id creation +
  heap push for pruned parents.
- Gated by `RUSTY_ALTO_F_FILTER` (default **on**; `=0` reproduces Step-3 behavior
  exactly, used for the A/B below). New stat `f_filtered_candidates`.

**Why it stays exact.** For any monotone string homomorphism the true parent span
only *widens* the predicted span (edge terminals), and `supply_left`/`supply_right`
are monotone in the span boundary, so the predicted-span test yields **supply ≥
true supply**: it can only *under*-prune. Hence `predicted-prune ⟹ true-prune ⟹
parent gets merit −∞ ⟹ never finalized`. No finalized parent ever loses an incoming
edge, so Viterbi scores, backpointers, and the finalized set are untouched.
Confirmed empirically: `astar-sxf` `finalized_states` is **identical** off vs. on,
and `f_filtered (117,320,539) + candidate_edges (111,337,504) = 228,658,043` =
exactly the filter-off candidate count — the filter removed *precisely* the
F-pruned-parent edges and skipped each one's `step_det`.

## A/B (`sentences20`, same binary, `RUSTY_ALTO_F_FILTER` off vs on)

| metric                         | astar-sx     | sxf filter OFF | sxf filter ON | ON vs OFF |
|--------------------------------|--------------|----------------|---------------|-----------|
| total parse ms (median of 4)   | 31,708       | 26,848         | **17,899**    | **−33.3%**|
| finalized states               | 15,294,558   | 7,134,727      | 7,134,727     | 0 (exact) |
| candidate edges                | 237,845,007  | 228,658,043    | 111,337,504   | −51.3%    |
| right_step_calls (`step_det`)  | 237,845,007  | 228,658,043    | 111,337,504   | −51.3%    |
| heap pushes                    | 36,361,455   | 33,439,845     | 14,089,918    | −57.9%    |
| f_filtered_candidates          | 0            | 0              | 117,320,539   | —         |
| reopen_attempts                | 0            | 0              | 0             | 0         |

Edge counts are deterministic (the robust evidence); wall-clock is the median of 4
runs each (per-run ON/OFF ratio is a stable 0.64–0.70; machine noise ±12%). Total
parse: **−43.6% vs. `astar-sx`** (Step 3's F-as-priority was −18.2%). The filter-off
column matches Step 3 exactly (`heap_pushes` 33,439,845, `candidate_edges`
228,658,043), so it is a faithful baseline.

## Asymptotics

No change to the complexity class — the win is the constant on candidate
enumeration. The candidate-to-finalized ratio drops from **32:1** (228.7M / 7.13M)
to **15.6:1** (111.3M / 7.13M): F halves the edges built and, because the span path
tests F *before* `step_det`, halves `right_step_calls` with them — directly cutting
the `eval_term_det` / `step_det` buckets (Step-3 profile: 18.7% + 7.7% of self-time)
that scale with candidates. Step 3 cut candidate edges only −3.9% (F as priority);
Step 4 cuts them −53.2% vs. `astar-sx`.

## Reproduce

```
cargo build --release --bin ptb-eval
# filter on (default) vs astar-sx — exactness + timing:
./target/release/ptb-eval ~/Documents/workspace/alto/ptb/out.irtg \
    ~/Documents/workspace/alto/ptb/sentences20.txt --strategies astar-sx,astar-sxf
# same-binary A/B baseline (Step-3 behavior):
RUSTY_ALTO_F_FILTER=0 ./target/release/ptb-eval ~/Documents/workspace/alto/ptb/out.irtg \
    ~/Documents/workspace/alto/ptb/sentences20.txt --strategies astar-sxf
```

## Remaining headroom

`f_filtered_candidates` (117.3M) is still *enumerated as sibling pairs* before being
rejected — the filter skips `step_det`/product-id/heap, but not the sibling-pair
iteration itself (`sibling_tuple_queries` fell only 104.6M→104.6M). The next lever
is the **group-level** early-out: when the *fixed* boundary alone dooms every rule
in a group (`req_left` at `trigger.start` for pos 0, `req_right` at `trigger.end`
for pos 1), skip the whole sibling query. Also out of scope here: wiring the same
`admits` filter into the lazy frontier path (`RUSTY_ALTO_LAZY_FRONTIER`).
