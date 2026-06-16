# N10 asymptotics: the hidden factor of *n*

**Summary.** The eager A\* parser and a faithful Pauls–Klein-style lazy parser both
run in `Θ(n³ log n)` for a sentence of `n` words (grammar held constant). The N10
lazy frontier as implemented runs in **`Θ(n⁴)`** — one extra factor of `n`. The
extra factor is not a constant and not memory; it is the cost of the operation
that produces a combination site's *next* candidate: N10 recomputes it by
**rescanning all of the site's siblings (`Θ(siblings)`)**, where eager and
Pauls–Klein get it from a **heap in `Θ(log siblings)`**. This document derives all
three bounds from scratch, with a worked example, and explains the structural
reason N10 is forced into the rescan (and what it would take to avoid it).

No measurements are used; everything below is a counting argument over the parse
chart. Per-element work that does not change between the variants (computing one
candidate's inside weight, one heuristic lookup, one product-id hash) is treated
as `O(1)` and folded into constants, so the comparison isolates the part of the
algorithm that actually differs.

---

## 1. Setting and terminology

We parse a sentence of **`n`** words by intersecting a context-free grammar with
the string. It is cleanest to view the work as building a **hypergraph** (a parse
chart). All terms used later are defined here.

- **Span `[i, j)`** — the word positions `i` up to (not including) `j`. There are
  `Θ(n²)` spans.
- **Item** (a.k.a. *product state*) — a pair `(nonterminal, span)`, e.g.
  `A[0,4]`. With the grammar size held constant there are `Θ(n²)` items.
- **Hyperedge** — one way to build an item from smaller items. For a binary rule
  `A → B C` and a **split point `k`**, the hyperedge combines `B[i,k]` and
  `C[k,j]` into the head item `A[i,j]`. A head `A[i,j]` has one hyperedge per
  `(rule, split point)`; since there are `Θ(n)` split points in a span, each head
  has `Θ(n)` incoming hyperedges, and the whole chart has

  > **number of hyperedges = `Θ(n²)` heads × `Θ(n)` splits = `Θ(n³)`.**

  This `Θ(n³)` is the classic CKY chart size. It is the irreducible amount of
  *combination* the parser must look at.
- **`inside(item)`** — the weight of the item's best sub-derivation (Viterbi
  inside score). Known once the item is *finalized*.
- **Heuristic `h(item)`** — an admissible estimate of the item's outside weight.
  Crucially, **`h` depends only on the item's `(nonterminal, span)`** — not on how
  the item is built. In this codebase it is a 2-D array lookup
  (`SentenceSxHeuristic::outside_estimate` → `lookup_lr`).
- **`merit`** — the A\* priority of a candidate that builds head `Z`:
  `merit = inside(candidate) · h(Z)`. A\* finalizes items in non-increasing
  `merit` order.
- **Combination site `g`** — *the unit a lazy parser streams from.* In N10 a site
  is one finalized **trigger** item together with a child position and a
  sibling-group: e.g. "trigger `B[0,1]` as the **left** child of rule `A → B C`".
- **`s_g`** — the number of **sibling products** that can fill the site's one open
  slot. This is the subtle quantity: a binary rule has a single sibling *slot*
  (the nonterminal `C`), but that slot is filled by every finalized product of the
  form `C[1, ·]` — one per right endpoint — so **`s_g = Θ(n)` for a short
  left trigger**, *not* 1.
- **`r_g`** — the number of candidates actually pulled (realized) from site `g`
  during the run, `0 ≤ r_g ≤ s_g`.

The whole asymptotic story is about one primitive: **`next_best(g)`** — "give me
the highest-merit not-yet-used candidate of site `g`." We count how the total cost
depends on how `next_best` is implemented.

---

## 2. Why a lazy 1-best parser still needs per-site *k*-best streams

It is tempting to think 1-best needs no ranking machinery. It does, once
generation is lazy, and here is why.

A single site feeds **many different heads**. The site "trigger `B[0,1]`, left
child of `A → B C`" produces a *different* candidate for each sibling `C[1,k]`,
and each lands on a *different* head `A[0,k]` (`k = 2, 3, …`). The lazy agenda
consumes a site best-first: it takes the site's top candidate, but that candidate
may build a head that is already finalized, or already has a better edge, or is
not yet the global best — so the site must then yield its **second**, **third**, …
candidate to serve the other heads. A structure that yields successive best
elements on demand is exactly a **k-best stream**. So lazy 1-best parsing is built
out of one k-best stream per site; the efficiency of `next_best` is the whole
game. (This corrects an earlier claim that 1-best needs no k-best machinery — it
does, per site.)

---

## 3. Eager: `Θ(n³ log n)`

Eager generation never streams. When an item finalizes, it immediately walks its
already-finalized partners and pushes **every** resulting candidate onto one
global agenda keyed by the **head** item, with a dominance check that keeps only
each head's best edge (`push_candidate_with_child_score`).

- **Examination:** each of the `Θ(n³)` hyperedges is looked at exactly once. The
  partner lookup is an `O(1)` indexed slice (`SpanProductSiblingFinder`), so there
  is no hidden walk. Examination cost = `Θ(n³)`.
- **Ordering:** each examined candidate may improve its head's agenda entry, a
  decrease-key on a heap of `Θ(n²)` heads = `O(log n)`. Worst case `Θ(n³)` such
  operations = `Θ(n³ log n)`.

> **Eager total = `Θ(n³ log n)`.** No factor beyond CKY's `n³` and the heap's
> `log n`. Nothing here is super-linear in the number of hyperedges, so there is
> no pre-existing hidden cost; the high absolute runtime is just the `Θ(n³)`
> hyperedge volume.

---

## 4. N10 (rescan stream): `Θ(n⁴)`

N10 makes a site object for each finalized trigger and implements `next_best(g)`
by **rescanning** the site: `lazy_best_sibling` iterates the whole
`siblings[..s_g]` slice, recomputing each candidate's merit, and returns the
maximum not-yet-consumed one (`src/astar.rs`, `lazy_best_sibling`). It is called

- **once at site creation** (to seed the frontier key), and
- **once per realization** (to find the new best after consuming one).

So site `g` costs `(1 + r_g) · Θ(s_g)`. Summing over all sites:

```
total = Σ_g (1 + r_g) · s_g
      = Σ_g s_g          (creation: examine every hyperedge once)
      + Σ_g r_g · s_g    (rescans)
```

- The creation term `Σ_g s_g` counts every hyperedge once = `Θ(n³)` — same
  examination work as eager.
- The rescan term: `r_g ≤ s_g`, so `Σ_g r_g · s_g ≤ Σ_g s_g²`. The worst sites —
  a short trigger at the left edge combining with all right-extending siblings —
  have `s_g = Θ(n)`. With `Σ_g s_g = Θ(n³)` and a worst-case `s_g = Θ(n)`,

  ```
  Σ_g r_g · s_g  ≈  Σ_g s_g²  ≤  max_g(s_g) · Σ_g s_g  =  Θ(n) · Θ(n³)  =  Θ(n⁴).
  ```

> **N10 total = `Θ(n⁴)`.** The extra factor of `n` is precisely `max_g(s_g)` — the
> length of the rescan — multiplying the realization work. It is a true asymptotic
> term, which is why the slowdown grows with sentence length rather than being a
> flat constant. (The `u64` consumed-mask caps `s_g` at 64, but the lazy path is
> only used when `n ≤ 64`, so within its operating range the cap never binds and
> `s_g` is free to be `Θ(n)` — the cap does not rescue the asymptotics.)

Compared to eager/Pauls–Klein, N10 replaced an `O(log n)` per-realization heap
operation with an `O(n)` rescan: `Θ(n³ log n) → Θ(n⁴)`, an extra `Θ(n / log n)`.

---

## 5. Worked example: one site, three siblings

Grammar rule `A → B C`. Sentence length `n = 4`. Consider the site

> **`g` = trigger `B[0,1]` as the left child of `A → B C`.**

Its siblings are the finalized `C`-items starting at column 1, one per right
endpoint:

| sibling | builds head | `inside(C)` | candidate `inside = inside(B[0,1])·inside(C)` (with `inside(B[0,1]) = 0.5`) | `h(head)` | `merit = inside · h` |
|---|---|---:|---:|---:|---:|
| `C[1,2]` | `A[0,2]` | 0.60 | 0.30 | 0.20 | **0.060** |
| `C[1,3]` | `A[0,3]` | 0.40 | 0.20 | 0.50 | **0.100** |
| `C[1,4]` | `A[0,4]` | 0.30 | 0.15 | 0.90 | **0.135** |

So `s_g = 3`, and the three candidates land on **three different heads**
(`A[0,2]`, `A[0,3]`, `A[0,4]`) — the reason the site must stream more than its top.

Notice the orderings disagree:

- by **inside**: `C[1,2] (0.30) > C[1,3] (0.20) > C[1,4] (0.15)`
- by **merit**: `C[1,4] (0.135) > C[1,3] (0.100) > C[1,2] (0.060)` — **reversed**,
  because `h` differs per head (different spans) and here grows with span width.

**This is the crux.** Because the candidates of an N10 site go to *different heads*
with *different `h`*, the site **cannot be kept in a single static sorted order**:
sorting by `inside` (which *is* fixed once items finalize) does not give merit
order. So N10 finds the merit-max by scanning all live siblings every time:

- pull 1 (`next_best` over `{C[1,2],C[1,3],C[1,4]}`): scan 3, take `C[1,4]`.
- pull 2 (over `{C[1,2],C[1,3]}`): scan 2, take `C[1,3]`.
- pull 3 (over `{C[1,2]}`): scan 1, take `C[1,2]`.

That is `3 + 2 + 1 = Θ(s_g²)` for this one fully-drained site. Eager, by contrast,
looks at the three candidates once and drops them on the three heads' agenda
entries (`Θ(s_g)`). Generalizing the `Θ(s_g²)` per drained site across the
`Θ(n²)` sites with `s_g` up to `Θ(n)` gives the chart-wide `Θ(n⁴)`.

---

## 6. Pauls–Klein (heap-successor stream): `Θ(n³ log n)`

Pauls & Klein 2009 ("K-Best A\* Parsing", <https://aclanthology.org/P09-1108/>)
stream from a structure where `next_best` is a **binary-heap pop in `O(log s_g)`**,
not a rescan. The reason it *can* is structural: **their site is the head edge**,
so every candidate of a site shares the **same head**, hence the **same `h`**.
With `h` constant across the site, `merit = inside · h` is order-equivalent to
`inside`, which is fixed — so the candidates have one static order and live in a
heap that yields successors in `O(log s_g)`.

- Examination (build the heaps): `Σ_g s_g = Θ(n³)`.
- Streaming: `Σ_g r_g · log s_g ≤ log n · Σ_g r_g = Θ(n³ log n)`.

> **Pauls–Klein total = `Θ(n³ log n)`** — same as eager, and an `n / log n` factor
> below N10.

The price is memory: a materialized per-site heap holds `O(s_g)` entries, up to
`Θ(n³)` live worst case, versus N10's `O(1)` per site (just a consumed bitmask).
N10 deliberately traded that memory away and paid for it in rescan time.

**The single pivot**, side by side:

| variant | site grouped by | `h` across a site | `next_best` | total |
|---|---|---|---|---|
| eager | (pushes eagerly to head agenda) | — | n/a | `Θ(n³ log n)` |
| Pauls–Klein | **head edge** | **constant** → static sort works | heap pop `O(log s)` | `Θ(n³ log n)` |
| N10 | **trigger** | **varies** (siblings → different heads) → no static sort | rescan `O(s)` | **`Θ(n⁴)`** |

---

## 7. What fixing it does and does not buy

- **To remove the `Θ(n)` penalty you must group sites by head, not trigger** — so
  that `h` is constant and a heap successor replaces the rescan. That is precisely
  "make our indexing fit Pauls–Klein's." It restores `Θ(n³ log n)` (at the
  `O(n³)`-memory cost of the per-head heaps).
- **But head-grouping does not beat eager for 1-best.** Both still examine the
  same `Θ(n³)` hyperedges — finding a head's best edge requires looking at all its
  split points to build the heap — and eager already streams nothing while
  achieving `Θ(n³ log n)`. In fact eager *is* head-grouped hypergraph A\* already
  (its agenda is keyed by head). So the lazy machinery, done right, lands back at
  eager.
- **Laziness yields an asymptotic win only when a site is pulled far fewer times
  than it has candidates, without having to examine the rest** — i.e. **k-best
  (k ≫ 1)** extraction over an already-built forest, where the heap is built once
  and popped `k` times, or a setting where many sites are never pulled at all
  (already handled by A\* pruning of unexplored heads). For the 1-best forward
  pass, every explored head's hyperedges are examined regardless, so there is no
  lazy speedup to capture — only the `Θ(n⁴)` rescan penalty to avoid.

## 8. Bottom line

The hidden cost is the `next_best` rescan: `O(siblings)` instead of `O(log
siblings)`, turning a `Θ(n³ log n)` parser into `Θ(n⁴)`. It exists because N10
groups streaming sites by **trigger**, which sends a site's candidates to
**different heads with different heuristics**, destroying the static order a heap
would need. Eager and Pauls–Klein both group by **head** (constant heuristic) and
stay `Θ(n³ log n)`. Matching Pauls–Klein removes the penalty but, for 1-best,
only returns to eager's complexity — the genuine win lives in k-best extraction or
in shrinking the `Θ(n³)` hyperedge count with a tighter heuristic.

> Note: trigger-grouping can also reach `Θ(n³ log n)` — store each site's
> candidates in a heap built once at creation (their merits are computed during
> the unavoidable creation scan, so the varying heuristic is fine; we sort on the
> *actual* computed merit). That is what the implementation does. It costs the
> per-site storage (`Θ(n³)` entries worst case) instead of restructuring to head
> grouping, but reaches the same complexity.

## 9. Empirical confirmation

The heap-successor variant was implemented (`src/astar/lazy_span.rs`:
`SpanGenerator.pending: BinaryHeap<SiblingEntry>` built at spawn, popped on
realize; `RUSTY_ALTO_LAZY_FRONTIER=1`). On PTB `sentences20` (astar-sx, one-best),
the prediction holds exactly:

- **The `Θ(n⁴)` penalty is gone.** The rescan variant ran in 40–47 s with a
  per-sentence ratio climbing with length (≈0.86× at n=22 → 1.70× at n=41). The
  heap variant runs in **32.5 s vs eager 32.1 s — break-even** (both within the
  ±12 % run-to-run noise: eager 32.1–38.1 s, heap 32.5–35.4 s), and the
  per-sentence ratio is now roughly flat: faster on small/medium sentences
  (≈0.60–0.85×, e.g. n=16 0.60×, n=23 0.66×), parity-to-slightly-slower on the
  longest (n=41 ≈1.1–1.2×, a residual *constant* factor from per-site heap
  memory traffic, not the old n-factor).
- **Exact and structurally as designed:** all 20 scores bit-identical to eager,
  `finalized_states` identical (15,294,558), and the lazy wins on traffic are
  intact — heap pushes 0.54×, heap **updates 0.008×**, candidate pushes 0.30×.
- **Memory** ≈ eager (3.10 GB vs 3.07 GB; the per-site heaps did not blow up at
  peak-live, unlike the worst-case `Θ(n³)` bound).

This confirms §7: removing the rescan returns the lazy parser to eager's
complexity *and* its wall-clock — the constant-factor savings from deferring the
product-id hash (fewer/0.008× decrease-keys, 0.30× pushes) are real but cancel
against the heap's `log` factor and memory traffic, netting a wash. A genuine
speedup must come from elsewhere (fewer hyperedges via a tighter heuristic, or
k-best where the per-site streams are pulled `k≫1` times and amortize).
