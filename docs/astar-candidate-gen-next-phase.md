# A* candidate generation — next-phase speedups (post F-filter)

This is the follow-up analysis after Step 4 of the obligatory-leaf work (the F
**candidate filter**, see `docs/obligatory-leaf-results.md` §"Step 4"). Step 4 halved
candidate enumeration and brought `astar-sxf` to ~−44% vs `astar-sx`. This doc diagnoses
what now dominates and proposes the next optimizations, **algebra-independent first**.

## The remaining funnel (`astar-sxf`, filter on, `sentences20`)

```
228.7M considerations ─F filter→ 111.3M built ─dom/finalized gate→ 21.1M reach heap → 7.13M finalized
                 (−51%, cheap)          (−81% of built, EXPENSIVE)        (−66%)
```

From the Step-4 counters: `candidate_edges = right_step_calls = 111,337,504`;
`dominated = 76,069,969`; `finalized_discards = 14,168,091` (so **90.2M / 111.3M = 81%**
of built candidates are discarded at the dominance/finalized gate); `f_filtered =
117,320,539`; `sibling_tuple_queries = 104,608,401`; `finalized = pops = 7,134,727`,
`reopen_attempts = 0`.

**Asymptotic framing.** Finalized items are `Θ(|states|·n²)` — one `(X, span)` each. Built
candidates are `Θ(|rules|·n³)` — one per `(rule, split point)`. So `built : finalized ≈
Θ(n)`, and the 15.6:1 we measure *is* that n-factor; the 68% "dominated" rate is the same
`Θ(n³)/Θ(n²)` overhead (each `(X, span)` is reached by ~n splits, only the best kept).
**That count is fundamental to bottom-up A\***; reducing it means best-first sibling
generation (the N10 lazy frontier), already measured break-even
([[n10-lazy-frontier-gated-off]]). So the lever is **cost per** wasted candidate, not the
count.

## Design constraint

Keep the A\* core **algebra-agnostic**. Prioritize algebra-independent optimizations.
Expose any algebra-specific speedup behind a **trait** that any algebra may implement, with
a default that falls back to the generic path — specific algebras opt into faster paths.

## Finding 1 (lead, algebra-independent): `step_det` re-derives per-symbol work on every call

`InvHom::step_det` (`src/combinators/invhom.rs:120`) calls `eval_term_det` (`:80`), which
recursively walks `hom.arena()` on **every** one of the 111M calls. Step-3's `sample`
profile put `eval_term_det` at **18.7%** of self-time.

The redundancy is entirely **per-symbol**, not per-call. `step_det(symbol, [s0, s1])`
factors into:
- **per-symbol** — interpreting the hom term (is it `*(?1,?2)`? which child goes where).
  Identical for every call with the same `symbol`. Bounded by the number of grammar rule
  symbols (grammar-bounded, ≲113k here), **not** the millions of calls.
- **per-call** — the `[left.start, right.end]` arithmetic. Genuinely varies; already trivial.

So the fix is to **memoize the per-symbol interpretation once**; the millions of calls then
do only the arithmetic.

> Note the granularity. Memoizing the *interpretation per symbol* is cheap and grammar-
> bounded. Memoizing whole *calls* keyed by `symbol × s0 × s1` would be the wrong unit —
> that key space *is* the `O(n³)` adjacent span pairs (the millions), adding a hashmap
> lookup per call plus memory to save a two-field `Span::new`: a net loss.

### Sketch

- In `src/combinators/invhom.rs`, give `InvHom` a `Vec` indexed by `Symbol` holding the
  memoized interpretation, built once via the **existing** `direct_linear_term` recognizer
  (`invhom.rs:151`, already used across the condensed paths): `Direct { inner_symbol,
  var_order }` for the `*(?i,?j)`-style flat case, else `General` (fall back to today's
  `eval_term_det`).
- `step_det` indexes the table: on `Direct`, reindex `children` by `var_order` and call
  `self.inner.step_det(inner_symbol, &reordered)` — no recursion, no arena lookups.
- Algebra-independent: benefits any wrapped algebra (string **and** tree decomposition).
  No A\* changes, no trait.
- Build the table **once** (grammar+hom only). `InvHom` is currently constructed per
  sentence (`src/bin/ptb-eval.rs:897`); build the table lazily/internally so it isn't
  rebuilt per sentence, or thread it through the prepared grammar. `InvHom::new` keeps
  working as today.

Exactness: identical transitions, only faster — `step_det` returns the same state, so
Viterbi scores and `finalized_states` are unchanged.

## Deferred follow-ups

- **Trait-based early dominance gate (algebra-specific).** 90.2M built candidates die at
  the dominance/finalized gate, which runs *after* `step_det` + product-id resolution. A
  default-`None` hook on the right-automaton trait (e.g. `fn fast_parent_state(symbol,
  children) -> Option<State>`) would let the generic candidate path run the gate *before*
  the full transition and skip it for the doomed. `StringDecompositionAutomaton` implements
  it via concat-span arithmetic (`[left.start, right.end]`, exact per
  `src/algebras/string.rs:332`); other algebras inherit the generic order. Pursue only if
  profiling after Finding 1 shows the transition still dominating.
- **Dominance-churn structure (algebra-independent).** The 90.2M `ProductStateMap` lookups
  on doomed candidates (the P5 problem; P5's dense `[right][left]` gate was reverted for
  ~10× memory — [[p5-dominance-gate-rejected]]). Revisit only if re-profiling shows
  product-id resolution dominates.
- **Group-level early-out (span-local).** Skip a whole sibling group's query when the
  trigger's fixed span boundary alone dooms every rule in it; lives inside the already
  string-specialized `expand_from_finalized_with_span_product_siblings`, so no core leakage.

## Verification (when implemented)

0. **Profile first.** `sample` the current Step-4 `release` binary
   (`CARGO_PROFILE_RELEASE_DEBUG=true`, 5 longest `sentences20` repeated) to confirm
   `eval_term_det`/`step_det` is still the top per-candidate bucket post-Step-4 (the 18.7%
   is from the old 228M-candidate binary), then again after to confirm the drop.
1. `cargo test` — full suite green (astar / invhom / string tests).
2. **Exactness:** `ptb-eval out.irtg sentences20.txt --strategies astar-sx,astar-sxf` —
   Viterbi bit-identical, `astar-sxf total_finalized_states == 7,134,727`.
3. **Timing A/B:** ≥3 runs, median total parse ms vs the Step-4 baseline (`astar-sxf` ≈
   17.9 s) given ±12% machine noise.
4. Append a "Step 5" results section to `docs/obligatory-leaf-results.md`.

## Critical files

- `src/combinators/invhom.rs` — `InvHom` struct + `step_det`; reuse `direct_linear_term`.
- `src/bin/ptb-eval.rs:897` / prepared-grammar path — build/pass the per-symbol table once.
