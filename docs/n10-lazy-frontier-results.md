# N10: lazy candidate generation — results (span/binary fast path)

> **Update.** The numbers below are for the original *rescan* generator, which is
> `Θ(n⁴)` and regressed ~1.25×. It was replaced by a per-site **binary heap**
> (`next_best` in `O(log)`), which is `Θ(n³ log n)` and now runs **break-even with
> eager** (32.5 s vs 32.1 s, within noise), faster on small/medium sentences,
> with the long-sentence regression removed. See
> [`n10-asymptotics.md`](n10-asymptotics.md) (§9) for the derivation and the
> confirming measurements. The verdict ("exact, no wall-clock *win*, gated off")
> stands — break-even, not faster — but it is no longer a regression.

**Verdict: implemented, exact, lower memory, but no wall-clock win — gated off
behind `RUSTY_ALTO_LAZY_FRONTIER`.** Like P5, the optimization targets a cost
(heap traffic / candidate pushes) that turns out not to gate wall-clock; the
per-candidate *merit computation* does, and the lazy frontier cannot avoid it
(it must compute merits to order the frontier) while adding rescan overhead that
regresses long sentences.

## What was built

A lazy candidate-generation frontier for the deterministic binary string-span A*
path (`src/astar/lazy_span.rs` + `run_with_lazy_span_frontier` and helpers in
`src/astar.rs`). Design notes in `astar-performance-next-phase.md` (N10) and the
plan file. Key points:

- Keeps the eager combination rule (later-finalized child = trigger, combined
  with already-finalized siblings) and **reuses `SpanProductSiblingFinder`**.
- A generator stores only `{trigger, position, group, snapshot_len, consumed:u64,
  best_sibling}` (~40 B) — no per-combination materialization. Its frontier key
  is the best unconsumed sibling's merit, found by an `O(snapshot_len)` rescan.
- The main loop interleaves, by merit, finalizing products off the parent agenda
  against realizing candidates off the frontier; a product finalizes only when
  its best realized edge dominates every generator's best unrealized candidate.
- Gated on `RUSTY_ALTO_LAZY_FRONTIER=1`, `sentence_len ≤ 64` (single-`u64`
  consumed mask), and a purely-binary grammar; otherwise the eager path runs.

## Measurements (PTB `sentences20`, astar-sx, one-best)

`out.irtg` + `sentences20.txt` (20 sentences, 10–41 words), release build.

| metric | eager | lazy (final) | ratio |
|---|---:|---:|---:|
| total parse time | 32.1 s | 40.2 s | **1.25× (slower)** |
| median per-sentence | 357 ms | 280 ms | **0.78× (faster)** |
| peak RSS | 3.07 GB | 2.79 GB | **0.91× (less)** |
| finalized states | 15,294,558 | 15,294,558 | identical |
| parent-agenda heap pushes | 36.4 M | 19.5 M | 0.54× |
| parent-agenda heap updates | 17.9 M | 0.15 M | **0.008×** |
| candidate edges pushed | 237.8 M | 70.3 M | 0.30× |
| reopen attempts | 0 | 0 | — |

**Exactness:** all 20 parse scores bit-identical to eager; `finalized_states`
identical; `reopen_attempts` 0. (An initial double-rescan variant ran in 47.0 s;
caching `best_sibling` to drop one of the two per-pop rescans brought it to
40.2 s.)

### Per-sentence: the win flips with length

Short/medium sentences get faster, long ones regress, and the long ones
dominate the total:

```
sent 11 (22w): 383 → 330 ms  0.86×      sent  5 (35w): 3326 → 3805 ms 1.14×
sent  6 (27w): 715 → 621 ms  0.87×      sent 20 (40w): 6099 → 7026 ms 1.15×
sent  9 (16w):  66 →  38 ms  0.58×      sent  7 (37w): 4715 → 5956 ms 1.26×
                                        sent  4 (41w): 8087 → 13717 ms 1.70×
```

## Why no wall-clock win

The frontier must order candidates by **exact** merit, and merit
(`rule × inside_trigger × inside_sibling × h(parent_span)`) has **no static
order in the sibling axis** — `h` depends on the parent span, which depends on
the sibling. So:

1. **Finding each generator's best still costs `O(snapshot_len)`** — the same
   per-candidate `step_det`/`h`/intern work eager does in its enumeration. The
   lazy path does *not* reduce the dominant per-candidate compute.
2. **Advancing to the next-best after a realization costs another `O(L)` rescan**
   (the merit order is dynamic), giving **`O(L²)` per fully-drained generator**.
   On the 41-word sentence this dominates and produces the 1.70× regression.
3. The genuine wins — heap pushes 0.54×, heap **updates 0.008×**, candidate
   pushes 0.30×, RSS 0.91× — confirm the frontier behaves as designed
   (realized-in-merit-order ⇒ first realized edge per parent is its best ⇒
   almost no decrease-keys). But heap/candidate traffic is not what gates
   wall-clock on the long sentences; the `O(L²)` rescan is.

Making it lazy enough to skip the per-candidate compute would need a cheap
admissible per-generator merit bound to defer the scan; the only obvious bound
(`trigger_merit`) is `≥ goal_merit` for every generator spawned before the goal,
so it never prunes in one-best. Storing per-sibling merits to kill the rescan
reintroduces `O(total combinations)` memory (~2 GB; P5's failure mode).

## Recommendation

- **Do not enable by default.** Net wall-clock regression on the benchmarked
  workload; fails the decision gate.
- **Keep the code, gated off.** It is exact, uses less memory, and is faster on
  short/medium sentences and at the median — a usable alternative and a base for
  a future iteration.
- **If revisited:** the blocker is the per-candidate merit compute + the `O(L²)`
  next-best rescan, not heap traffic. A win needs a structure that yields a
  generator's next-best in `O(log L)` without recompute *and* without `O(combos)`
  memory — not obviously achievable given the dynamic merit order. The dominant
  cost remains per-candidate compute (the SX `h` lookup + span stepping), as P5
  also concluded; that is where future effort should go.
