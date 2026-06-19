# Step 1 — Obligatory-leaf coverage probe (detailed, executable)

Goal of Step 1 (and ONLY Step 1): decide cheaply, from the grammar alone, whether
the grammar's states commit to specific terminal leaves strongly enough that an
F-style "obligatory leaf must be present in the context" filter could prune
anything. We compute, per grammar state `X`, the multisets of leaves every
derivation/completion is *forced* to emit (`mic`, `req_left`, `req_right`), then
report **coverage** (what fraction of states carry obligations, and how big). No
heuristic, no A\*, no inverse-homomorphism supply check — those are Steps 2–3.

This is a measurement. If coverage is essentially zero, F cannot help and we stop.

## Deliverable

A single new binary: **`src/bin/oblig-coverage.rs`**. No library files change.
It only uses already-public APIs (verified):

```rust
use std::collections::BTreeMap;
use std::env;
use rusty_alto::{parse_irtg, Explicit, StateId, Symbol, StringAlgebra, BottomUpTa};
use rusty_alto::homomorphism::HomLabel;          // also: rusty_alto::HomLabel
use packed_term_arena::tree::{Tree, TreeArena};         // same crate string.rs already uses
```

Relevant APIs (all `pub`):
- `parse_irtg(reader) -> Result<Irtg, _>`; `irtg.grammar() -> &Explicit`;
  `irtg.string_interpretation_names() -> Vec<&str>`;
  `irtg.interpretation::<StringAlgebra>(name) -> Result<TypedInterpretation, _>`.
- `interp.homomorphism() -> &Homomorphism`; `interp.algebra_signature() -> &Signature`.
- `hom.get(sym: Symbol) -> Option<Tree>`; `hom.arena() -> &TreeArena<HomLabel>`;
  `arena.get_label(node) -> &HomLabel`; `arena.get_children(node) -> &[Tree]`.
- `grammar.num_states() -> u32`; `grammar.rules()` yields `Rule { symbol: Symbol,
  children: &[StateId], result: StateId, weight: f64 }`; `grammar.initial_states(&mut
  |s: StateId| ...)` enumerates the **accepting (root) states**.
- `StateId(pub u32)`, `.index() -> usize`, `.is_stuck() -> bool`; `Symbol(pub u32)`;
  `signature.resolve(sym) -> &str` (turn a leaf symbol into its word, for the report).

## Core data types (put in the binary)

```rust
/// One flattened, left-to-right yield token of a rule.
#[derive(Clone, Debug)]
enum Tok { Word(u32), Child(usize) }   // Word=leaf symbol .0 ; Child=child STATE index

/// A rule reduced to what the analysis needs.
struct FlatRule { result: usize, tokens: Vec<Tok> }

/// Sparse leaf multiset: symbol-id -> count (absent key == 0). BTreeMap for determinism.
type Bag = BTreeMap<u32, u32>;
```

Helpers:
```rust
fn bag_add(a: &mut Bag, b: &Bag)          // a += b  (multiset sum)
fn bag_min(a: &Bag, b: &Bag) -> Bag       // per-key min(a,b); drop keys whose min == 0
```

## Phase A — extract `FlatRule`s from grammar + homomorphism

For each `rule` in `grammar.rules()`:
1. `let Some(term) = hom.get(rule.symbol) else { skip rule };`
2. If any `rule.children[i].is_stuck()` or `index() >= num_states`, **skip the rule**
   (it can never fire — mirrors how SX filters stuck children).
3. Walk the homomorphism term frontier left-to-right (copy of `walk_frontier` in
   `src/algebras/string.rs:489`, but capturing the leaf symbol and mapping vars to
   child *states*):
   ```
   fn frontier(arena, node, children: &[StateId], out: &mut Vec<Tok>):
       match *arena.get_label(node):
         HomLabel::Var(i)    => out.push(Tok::Child(children[i].index()))
         HomLabel::Symbol(s) => if arena.get_children(node).is_empty()
                                    { out.push(Tok::Word(s.0)) }       // a word constant
                                else { for c in get_children: frontier(arena,c,children,out) }
   ```
   (The concat symbol only ever appears as an inner node, so it is recursed into and
   never emitted as a `Word` — no special-casing needed, same as `walk_frontier`.)
4. Push `FlatRule { result: rule.result.index(), tokens }`.

Also collect `accepting: Vec<usize>` via `grammar.initial_states(&mut |s| if !s.is_stuck()
&& s.index() < num_states { push s.index() })`.

## Phase B — `mic` (obligatory INSIDE leaves), per state

`mic[X]` = the multiset of leaves that *every* derivation rooted at `X` must yield.
`Vec<Option<Bag>>`, length `num_states`; `None` means ⊤ / not-yet-productive.
Fixpoint (same shape as the existing `minwidth` loop, `src/algebras/string.rs:698`):

```
mic = vec![None; num_states]
loop:
  changed = false
  for r in flat_rules:
     // build candidate bag = consts(r) ⊎ Σ_child mic[child]; needs every child finite
     acc = Bag::new()
     for tok in r.tokens:
        match tok:
          Word(s)  => *acc.entry(s).or(0) += 1
          Child(c) => match &mic[c] { None => { acc = INFEASIBLE; break } Some(m) => bag_add(&mut acc, m) }
     if INFEASIBLE: continue
     new = match &mic[r.result] { None => acc, Some(cur) => bag_min(cur, &acc) }   // MEET
     if mic[r.result] != Some(new): mic[r.result] = Some(new); changed = true
  if !changed: break
```

Semantics & safety:
- `MEET` (`bag_min`) makes `mic[X]` the per-terminal **min over the state's rules** =
  "required by every alternative." It only ever shrinks once finite, so the loop
  terminates (each state goes `None→Some` once, then Some→smaller a bounded number of
  times).
- Read values **only after `!changed`** (the fixpoint); intermediate values may be
  over-estimates. At the fixpoint `mic[X]` is exact. States left `None` are
  non-productive (no finite derivation) — they never appear as A\* items; exclude them.
- This must never over-estimate (an over-estimate would inflate the probe). Validate
  with the worked example below before trusting big-grammar numbers. Conservative
  fallback if a cyclic grammar misbehaves: treat any not-yet-`Some` child as `None`
  and keep iterating — that yields a sound under-estimate (weaker, never wrong).

## Phase C — `req_left` / `req_right` (obligatory OUTSIDE leaves), per state

`req_right[X]` = leaves every completion of `X` (embedding up to a root) must emit
strictly to the **right** of `X`'s span; `req_left[X]` symmetric. `Vec<Option<Bag>>`.

Precompute `productive_rules` = flat rules whose every `Child(c)` has `mic[c] = Some`
(after Phase B). Only these can appear in a finite parse.

Seed roots, then fixpoint over the "X is a child of rule r" relation:
```
req_left  = vec![None; num_states]; req_right = vec![None; num_states]
for a in accepting: req_left[a] = Some(empty); req_right[a] = Some(empty)
loop:
  changed = false
  for r in productive_rules:
     // skip until the parent's side req is known
     for (pos, tok) in r.tokens.enumerate():
        let Tok::Child(x) = tok else continue;           // x = child STATE index at this position
        // within-rule obligations on each side of THIS occurrence:
        left = Bag::new(); right = Bag::new()
        for (q, t2) in r.tokens.enumerate():
           match t2:
             Word(s)  if q<pos => *left.entry(s)+=1
             Word(s)  if q>pos => *right.entry(s)+=1
             Child(c) if q<pos => bag_add(&mut left,  mic[c].as_ref().unwrap())   // productive ⇒ Some
             Child(c) if q>pos => bag_add(&mut right, mic[c].as_ref().unwrap())
             _ => {}
        if let Some(pr) = &req_right[r.result] { let mut cand = pr.clone(); bag_add(&mut cand,&right);
            meet_update(&mut req_right[x], cand, &mut changed) }
        if let Some(pl) = &req_left[r.result]  { let mut cand = pl.clone();  bag_add(&mut cand,&left);
            meet_update(&mut req_left[x],  cand, &mut changed) }
  if !changed: break
```
`meet_update(slot, cand, changed)`: `None=>Some(cand)`, `Some(cur)=>bag_min(cur,&cand)`;
set `changed` if the slot changed. Note we iterate **token positions**, not child
indices, so a rule that uses the same state twice updates it from both positions.

Same termination/exactness/safety notes as Phase B. States left `None` are
unreachable from any root (never items); exclude.

## Phase D — coverage report (what to print)

Let `U` = states that are both productive (`mic = Some`) and root-reachable
(`req_left` or `req_right` = `Some`) — the universe that can actually be A\* items.
Print:

1. `total_states`, `|productive|`, `|root_reachable|`, `|U|`.
2. Over `U` — counts and fractions of states with non-empty: `mic`, `req_left`,
   `req_right`, and **`req_left ∪ req_right`** (the headline number).
3. For states in `U` with non-empty `req_left ∪ req_right`: distribution of
   (a) number of distinct obligatory terminals and (b) total obligatory count —
   report min / median / mean / p90 / max.
4. Top 15 obligatory terminals ranked by how many states require them, each resolved
   to its word via `signature.resolve(Symbol(id))`.
5. `--examples N` (default 10) example states: state index + `req_left` and
   `req_right` as `word:count` lists (resolved).
6. A one-line **verdict** (thresholds in Evaluation below).

Output plain text to stdout; also emit one machine-readable summary line prefixed
`SUMMARY ` with the key fractions, so it can be grepped/collected.

## Build & run

```
cargo build --release --bin oblig-coverage
./target/release/oblig-coverage <PATH_TO_IRTG_GRAMMAR> [--examples 10]
```
Use the **same IRTG grammar file you pass to `ptb-eval`** (its first positional arg;
see `src/bin/ptb-eval.rs:171`). The probe is grammar-only, so no sentences are needed.

## Unit test (correctness gate — run before trusting big numbers)

Put a `#[cfg(test)]` test in the binary that calls the pure `compute(num_states,
&[FlatRule], &accepting) -> (mic, req_left, req_right)` on a hand-built grammar — no
IRTG needed, since `compute` takes `FlatRule`s directly:

States `S=0, A=1, B=2`; word symbols `x=10, y=11, z=12`. Rules:
```
r1: result=0(S), tokens=[Child(1), Child(2)]   // S -> A B
r2: result=1(A), tokens=[Word(10)]             // A -> "x"
r3: result=2(B), tokens=[Word(11)]             // B -> "y"
r4: result=1(A), tokens=[Word(12)]             // A -> "z"
accepting = [0]
```
Expected (assert exactly):
- `mic[A] = {}`  (A is "x" OR "z" — nothing forced)
- `mic[B] = {11:1}`,  `mic[S] = {11:1}`  (every S contains a y)
- `req_right[A] = {11:1}`  (an A always has a y to its right),  `req_left[A] = {}`
- `req_left[B] = {}`,  `req_right[B] = {}`  (A forces nothing, so B's left is empty)
- `req_left[S] = req_right[S] = {}`

If these match, the fixpoints are correct.

## Evaluation — how to read it / decide

The headline is the fraction of `U` with non-empty `req_left ∪ req_right`, plus what
those obligatory terminals *are*:

- **≥ ~0.30 and obligations look discriminating** (content words / specific tags, not
  only ubiquitous punctuation): states commit strongly → F has real teeth →
  **proceed to Step 2** (predicted-pruning probe on `sentences20`).
- **≤ ~0.05**: states barely commit (coarse grammar) → an obligatory-leaf filter
  cannot prune much → **stop**; revisit only with a different statistic.
- **In between, or obligations dominated by near-ubiquitous tokens**: inconclusive on
  structure alone → **proceed to Step 2**, which weights by states actually processed
  and measures real pruning (`inside·h ≥ P*`), rather than guessing from coverage.

Record the printed report (and the `SUMMARY` line) in
`docs/obligatory-leaf-results.md` alongside the eventual Step 2 numbers.

## Explicitly out of scope for Step 1

The condensed-invhom terminal-supply check, the `ObligatoryLeafHeuristic`, the
`MinHeuristic` combinator, `AstarHeuristic`/`ptb-eval` wiring, and any change to
`YieldToken`/`string.rs` — all deferred. Step 1 ships exactly one throwaway binary.
If Steps 1–2 are positive, Step 3 promotes the `compute` logic into the library
(reusing the real `YieldTemplate`, extending `YieldToken::Word(Symbol)`).
```
