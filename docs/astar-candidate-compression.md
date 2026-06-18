# Compressing the A* candidate & item explosion

> Status: **diagnosis + plan**, written to be reviewed before we change code. After Step 5 the
> invhom step is no longer a cost (111.3M requests → 56k actual evaluations). What remains, on
> `sentences20` / `astar-sxf`, is **111.3M candidate edges** and **7.13M finalized cells**.
> The working hypothesis (from the Alto author) is that we are *multiplying out things that
> don't need multiplying out*, and the target is a **100–1000×** cut, not 10%.
>
> Two standing rules: **(1)** don't preserve item/candidate counts — drive them as low as
> possible; the *only* invariant is that the first goal item popped keeps its value. **(2)**
> stay **condensed** — the term-id memo gave ~2000× on invhom by working once per term-id
> instead of per symbol, so see whether *candidates* can be about term-ids and combine with
> concrete grammar symbols as late as possible.

---

## 1. The machine we are running

We parse by intersecting two weighted tree automata over the IRTG's **rule-symbol** signature:

- **LEFT = the grammar `G`** (`irtg.grammar()`, an `Explicit` weighted TA;
  `PreparedAstarGrammar.left_rules` in `src/astar.rs`). A state is a grammar nonterminal `q`;
  a binary rule is `f : (q_X, q_Y) → q_P` with weight `w`. `|R|` rules, `|N|` nonterminals.
- **RIGHT = `InvHom(StringDecomposition)`** (`src/combinators/invhom.rs`,
  `src/algebras/string.rs`). A state is a **span** `[i,k]` of the input. The homomorphism maps
  each rule symbol `f` to a string term; an ordinary binary rule's term is `concat(?0,?1)`, so
  the right transition is `[i,j] · [j,k] → [i,k]` when the two spans are adjacent. **All**
  binary concat rules share **one** term-id — the key fact Step 5 exploited.

A **product state = chart cell** is `(q_P, [i,k])` (`product_pairs`, interned). The goal cell
is `(start, [0,n])` (`is_accepting_product`, `astar.rs:655`). We run **A\***: each cell has
`merit = inside(cell) × ĥ(cell)` where `ĥ` is an *admissible* outside estimate
(`outside_estimate`, in `(0,1]`); SX is the estimate, F (obligatory-leaf) tightens it via
`min` **and** acts as a hard `admits` filter that proves some cells have zero outside weight.
We pop cells best-first, finalize each once with its Viterbi `inside`, and **stop at the first
goal pop** (`run`, `astar.rs:1252`; `stop_at_first_goal`).

The funnel we measure (`astar-sxf`, 20 sentences):

```
228.7M considerations ─F admits→ 111.3M built ─dominance/finalized gate→ 21.1M heap → 7.13M finalized → goal
                       (−51%)                   (−81% of built)                        (≈ reachable chart?)
```

## 2. How one cell gets built — the candidate loop (worked example)

Grammar fragment (rule symbols in brackets):
`S→NP VP [r1]`, `NP→Det N [r2]`, `VP→V NP [r3]`, `NP→NP PP [r4]`, `PP→P NP [r5]`, + lexicon.
Input: `the(0) dog(1) saw(2) the(3) cat(4)` → `n = 5`.

Lexical cells seed and finalize: `Det[0,1] N[1,2] V[2,3] Det[3,4] N[4,5]`. Then, when a cell
finalizes, `expand_from_finalized_with_span_product_siblings` (`astar.rs:903`) fires. Say
**`NP[0,2]`** has just finalized:

1. **Left-index lookup** (`SpanAstarLeftIndex::binary_groups`, `astar/span.rs`): the rules in
   which `NP` is a child, grouped by `(position, sibling_left, symbol)`:
   - pos 0 (NP is the left child): `S→NP VP` (sibling `VP`), `NP→NP PP` (sibling `PP`).
   - pos 1 (NP is the right child): `VP→V NP` (sibling `V`), `PP→P NP` (sibling `P`).
2. **Sibling finder** (`SpanProductSiblingFinder::siblings_slice`, `string.rs:140`): for each
   group it returns the *already-finalized* products with the matching nonterminal that are
   span-adjacent — e.g. for `S→NP VP` it returns every finalized `VP[2,k]`.
3. **Cross-product** (`astar.rs:1035`–`1118`): `for each sibling { for each symbol_group { for
   each rule { build candidate } } }`. Each candidate runs the (now-memoized) right transition
   → parent span, then `push_candidate_with_child_score` (`astar.rs:705`): F `admits` →
   product-id → finalized? → `best_seen_inside` dominance → heap.

The dominance gate (`astar.rs:744`) is keyed on the **parent cell** `(q_P, [i,k])`, keeping
only the best `inside`. So the same cell `(VP,[2,5])` reached via split `j=3` and via `j=4`
competes there; the loser is counted `dominated`. (Note: partners are recorded *only on
finalize*, so each binary edge is built **once**, when the later child finalizes — there are
no exact duplicate candidates to dedupe.)

## 3. The accounting — where the hundreds of millions come from

- **Cells**: `|N| · O(n²)`. We finalize **≈357k per sentence**. *Open question for the
  measurement:* how does that compare to the number of *reachable* cells (nonzero inside)? If
  it is ≈ all of them, the heuristic is barely pruning and A\* is exhaustive CKY + a heap.
- **Edges (candidates)**: `Σ_cell (splits × rules)` = `Θ(|R| · n³)`, sparsified by F and by
  pairing only finalized siblings → **5.5M per sentence built**, **81% dominated**.
- **Right transitions**: only **56k distinct** `(term-id, span-pair)` across *all* 20
  sentences. The right side of the search is tiny; the explosion is **grammar (left) × these
  right-transitions**, re-materialized per rule and per split.

## 4. The three multiplications

- **M1 — grammar-rules × sibling-spans.** The rule set for a trigger depends only on
  `(X, Y)`; the sibling set only on `(Y, j)`; the right transition only on the term-id. Yet the
  loop re-walks all grammar rules *inside* the per-sibling loop and re-derives a product-id per
  `(rule, sibling)`. The right work is shared (memo); the *grammar attachment and the
  product-id/gate* are paid per edge.
- **M2 — splits per cell.** A cell `(P,[i,k])` is reached by every split `i<j<k` whose two
  children are finalized: `Θ(n)` edges per cell, one survives. This is the 76M `dominated` and
  the `built : finalized = Θ(n)` factor.
- **M3 — per-symbol.** Fixed on the right by the term-id memo. On the left, symbols are 1:1
  with rules, so the residual is the genuine grammar size — *unless* the grammar has parallel
  rules `P→X Y` differing only in symbol/weight (a measurement target: for one-best only the
  max-weight one can ever win, so they could be condensed).

## 5. What "condensed / term-ids / attach symbols late" buys — and what it cannot

Keying edge generation on `(term-id, span-pair)` and fanning out to grammar rules late removes
M1's **constant** (one right transition + one product-id per span-pair instead of per edge) and
is the natural home for laziness — but it does **not** reduce the `Θ(|R|n³)` edge **count**:
context-free derivation has that many steps, and even Alto's condensed intersection produces
that many chart edges. **So the 100–1000× cannot come from a cheaper-but-exhaustive chart.** It
must come from **not being exhaustive**:

- **(a) Finalize far fewer cells** — a tighter admissible `ĥ`. If the measurement shows we
  finalize ≈ the whole reachable chart, SX/F is loose and this is the dominant lever.
- **(b) Generate edges lazily in merit order with a goal-bound cutoff** — so the `Θ(n)`
  dominated edges per cell (M2) and *all* edges of cells that never beat the goal are never
  built. The existing lazy frontier (`astar/lazy_span.rs`, `RUSTY_ALTO_LAZY_FRONTIER`) was
  break-even because it **pre-scores every sibling** (an `O(s)` scan per generator) and has no F
  and no goal cutoff. Fixing those is the candidate lever.

## 6. Measurements that pinpoint the waste (add a gated `RUSTY_ALTO_AUDIT` counter set)

1. **Finalized vs reachable** — distinct reachable cells (any finalized-or-pushed product) vs
   finalized; tells us whether (a) is the lever.
2. **Candidates built *after* the first goal is popped** — pure waste a goal-bound cutoff would
   erase; the laziness ceiling.
3. **Edges per parent cell** (M2 factor) and **distinct parent cells vs candidates**.
4. **Rules per `(X, position, Y)` group** and **parallel-rule rate** (M3 / M1 constant).
5. **`ĥ` slack**: distribution of `inside·ĥ` at finalize vs the optimal goal merit.

## 7. Candidate fixes (to choose after the measurements)

- **F1 (cut M2/items): lazy best-first sibling generation done right** — order siblings by a
  monotone key without the full scan, wire F `admits` in, and stop a generator once its best
  remaining merit ≤ the best goal bound. Targets the 76M dominated and the post-goal waste.
- **F2 (cut M1 constant): condensed late-binding edge generation** — drive the inner loop by
  `(term-id, span-pair)`: one right transition + one parent product-id per span-pair, then
  attach grammar rules; skip whole groups by the fixed-boundary F early-out (`req_left` at
  `trigger.start` for pos 0 / `req_right` at `trigger.end` for pos 1).
- **F3 (cut items): tighter admissible heuristic** — only if measurement #1/#5 shows large
  slack; a separate subsystem from candidate-gen.

---

## Plan / sequencing

1. Finalize this doc (you are reading it) and align on the diagnosis.
2. **Add a gated audit harness** (`RUSTY_ALTO_AUDIT`, off by default) producing the §6 numbers
   on `sentences20`; record results back into §6. No behavior change.
3. **Pick among F1/F2/F3** and implement behind the existing exactness checks.

## Critical files

- `src/astar.rs` — `expand_from_finalized_with_span_product_siblings` (:903), the dominance
  gate `push_candidate_with_child_score` (:705), the run loop (:1252), the lazy frontier
  driver; audit counters would live in `AstarStats` + the `ptb-eval` summary line.
- `src/astar/span.rs`, `src/astar/lazy_span.rs`, `src/algebras/string.rs` (sibling finder).
- `src/heuristic.rs`, `src/obligatory_leaf.rs` (ĥ / F).

## Verification (for any fix)

- Audit numbers reproduce across runs (deterministic counts).
- `astar-sx`/`astar-sxf` Viterbi scores **bit-identical**; `finalized_states` ≤ today (lower is
  the goal); candidate/finalized counts down toward the target factor; interleaved timing A/B
  vs HEAD; `cargo test` green.
