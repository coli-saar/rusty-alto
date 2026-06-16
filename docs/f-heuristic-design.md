# Adapting F to the automaton-intersection setting: an obligatory-leaf suffix filter

## Context

SX has known headroom (from the A\* agenda-pop statistics) and single-`X`
coarse-to-fine doesn't help (universal bracketing — see "Why single-`X` fails"
below). K&M 2003 describe their **F** estimate not as a projected parse but as
*"a sophisticated lookahead condition on suffixes"*: an active constituent is
hopeless if the grammar **forces** it to emit terminals that the context can't
supply. We adapt exactly that to our two ingredients — the grammar (`Explicit`)
and the **condensed invhom**. The A\* items have shape
`(grammar state X, right-state q)` (for strings, `q` is a span `[i,j)`); the filter
kills items whose completion is terminal-infeasible against the actual input, and
is combined with SX by `min`.

### Why single-`X` coarse-to-fine fails (recorded so we don't revisit it)

Project every state to one `X`. Any binarized/CNF grammar has a pure-concat rule
`A→B C` ↦ coarse `X X→X`, plus `X→wᵢ` per word; by induction `X` derives *every*
span, so coarse reachability prunes zero edges. Keeping terminals distinct (K&M's
**F** projection) doesn't help — the phrasal `X` is still universal over spans.
This is K&M's **XBAR**, reported "ineffective, since most productions merged to
probability 1." F's real bite came from *dotted-rule* edges committed to a rule's
terminals — i.e. a lookahead condition, not a collapsed-grammar parse.

## Statistic A — obligatory leaves, from the grammar (no binarization assumption)

terminal = a constant leaf (word) of a rule's yield template (needs `YieldToken`
to carry its `Symbol`; today it is a unit). Per-terminal min-count fixpoints, same
shape as the existing `minwidth` pass:

- `mic(X)[t]` = min over derivations rooted at `X` of count of leaf `t`:
  `mic(X) = ⊓_{r: result=X}( consts(r) ⊎ Σ_{c∈children(r)} mic(c) )`,
  `⊓` = per-terminal min (a terminal absent from any rule drops to 0).
- `req_right(X)`, `req_left(X)` = obligatory leaves every completion of `X` emits
  strictly right / left of `X`'s span. Fixpoint over sites where `X` is a child at
  template position `p` of a rule `→ A`:
  `side_within(r,p) = consts on that side ⊎ Σ_{siblings on that side} mic(sibling)`;
  `req_side(X) = ⊓_{sites}( req_side(A) ⊎ side_within(r,p) )`; roots seed to `∅`.
  Uses the existing `YieldTemplate` ordering helpers (`words_right_of_child`,
  `children_right_of`, …) and the template order = span order that SX already
  relies on.

Runs over **whatever states the grammar has** and extracts whatever terminal
commitment they carry → no assumption about binarization. Grammar-only, sparse,
cached per grammar.

## Statistic B — terminal supply, from the condensed invhom (per input)

`supply_total[t]`, and supply consumed *under* right-state `q`. Strings: prefix /
suffix token counts, O(1) per terminal via prefix sums. Algebra-neutrally it comes
from the invhom's nullary shapes / sub-state coverage.

## The filter

Item `(X, q)` exists ⇒ inside is already feasible, so only the outside matters:

- **Sided (string-strong):** prune (`h_F = zero()`) if `req_left(X)` exceeds the
  supply left of `q`, or `req_right(X)` exceeds the supply right of `q`; else
  `one()`.
- **Bag (strictly algebra-neutral, weaker):** prune if
  `req_total(X) ⊄ supply_total − supply_under(q)`.

Admissible: we zero only when an obligatory leaf is genuinely unavailable (true
outside weight = 0). Combine with SX via a generic `MinHeuristic`. Targets exactly
the inside-feasible / outside-impossible items SX wastes pops on — the orthogonal
info that took K&M 80%→95% edges blocked.

## Step 1 (cheap, decisive): measure whether the grammar gives F teeth

Computing Statistic A is grammar-only and cheap. Before any heuristic/A\* work,
report **coverage**: fraction of grammar states with non-empty `req_left`/
`req_right`, and the size distribution. If almost all are empty, the states don't
commit to terminals and the filter can't help — stop here. (This replaces the
headroom question, already answered, with the only open unknown.)

## Step 2 (if it has teeth): predicted pruning

Reuse the `inside(s)·h(s) ≥ P*` finalization predictor on `sentences20`: tally
`predicted_finalized` for `SX` vs `min(SX, F)` (and self-validate `SX` against the
`astar-sx` `finalized_states` already reported). Confirms the filter prunes
real processed items net of its cheap per-item cost.

The predictor: A\* with a consistent max-product heuristic finalizes a fine product
state `s=(X,q)` iff `inside(s)·h(s) ≥ P*` (`P*` = best goal score); `inside(s)` and
`P*` are heuristic-independent, so one exhaustive fine parse lets us tally
`predicted_finalized(h) = #{ reachable s : inside(s)·h(s) ≥ P* }` for any `h`.

## Step 3 (if confirmed): implement

- `YieldToken::Word(Symbol)`; obligatory-leaf tables (`mic`, `req_left`,
  `req_right`) next to the SX builder, reusing the `minwidth` pattern + template
  helpers. Cache per grammar.
- Per-input supply from the condensed invhom (prefix counts for strings).
- `ObligatoryLeafHeuristic` (separate heuristic) + generic `MinHeuristic<A,B>`
  combinator (`a.min(b)`, correct in prob and log-prob); wire as an
  `AstarHeuristic` variant + `ptb-eval` selection. Pure SX path untouched.

## Verification

- Unit: a grammar that forces a terminal → `req` correct; filter prunes when the
  token is absent on the needed side, passes otherwise; `MinHeuristic` = min.
- Exactness — must hold: `astar-(sx+F)` bit-identical Viterbi scores/trees to
  `astar-sx` / `astar-zero` on `sentences20` (`finalized_states` compared as
  `n10-asymptotics.md` §9).
- Edge-count + timing A/B (incl. precompute) → `docs/obligatory-leaf-results.md`.

## Pieces to reuse / touch

`minwidth` fixpoint + `YieldTemplate` helpers (`src/algebras/string.rs`),
`UniversalSxHeuristic` (combine via min), the condensed invhom interface
(`condensed_rules_by_child`, nullary shapes), `OutsideHeuristic` /
`materialize_indexed_condensed_intersection` (for the Step-2 probe's exhaustive
fine parse + product mapping, which is built internally at `src/materialize.rs:609`
but not yet returned), `AstarHeuristic` wiring (`src/irtg.rs:49/359/399`),
`ptb-eval` selection (`src/bin/ptb-eval.rs:664/846`).
