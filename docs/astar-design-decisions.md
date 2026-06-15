# A* Intersection Design Decisions

This note records the current A* design after the PTB optimization work. The
main goal is to keep A* semantically general while giving the string/span case a
data structure that returns useful candidate siblings directly.

## Current Design

A* finalizes product states `(left_state, right_state)` in best-first order. The
agenda stores one pending item per product state and uses decrease-key updates,
so improved candidates replace older priorities instead of adding stale heap
entries.

For arbitrary condensed right automata, candidate generation uses a conservative
fallback:

1. Cache right rules by `(child_position, finalized_right_state)`.
2. For each such right rule, look up finalized left partners for every sibling
   right child.
3. Use the left set-trie index to find matching left rules.
4. Resolve concrete product children and push only candidates whose trigger
   product is the first occurrence of itself in the child tuple.

For right automata whose states are string `Span`s, A* uses a product-aware span
sibling finder for unary and binary rules. The left rules are grouped by
finalized left child, child position, required sibling left state, and symbol.
When a product finalizes, it is inserted into the sibling finder only for the
binary child positions in which its left state can occur. A later expansion can
then query by span boundary and required sibling left state, returning exact
finalized sibling products rather than adjacent right spans that still need to
be filtered.

The span path calls deterministic right transitions. This matters for
`InvHom<StringDecompositionAutomaton>`: the generic `InvHom::step` allocates a
deduplication set per call, while the string/span transition for a concrete
child tuple has at most one parent.

Rules of arity greater than two still use the generic fallback. This keeps the
span optimization small and avoids building a special-purpose higher-arity
string parser inside A*.

## Discarded Experiments

The right-state-only span sibling finder reduced some set-trie work, but it
returned all adjacent right spans. On PTB it produced about 2.27B sibling tuples,
most of which had no finalized product with the left sibling state required by
the rule. The product-aware finder replaced it.

The span-boundary right-rule index attempted to cache string rules generated
from either side of a binary span. It became unnecessary once the span path
switched to exact product-sibling lookup followed by `right.step(symbol,
children)`. The code was moved to `experimental/astar-span-indexes.md` as a
reference.

A small right-transition result cache was also removed. The smoke runs showed
no useful hit rate, and the extra bookkeeping made the hot path harder to
reason about.

## Measured Effect

The product-aware finder reduced span sibling iteration dramatically:

- PTB20 `astar-zero` sibling tuples: about 2.27B -> about 108M.
- PTB20 `astar-zero` total time: roughly unchanged, about 103s.
- PTB sentence 20 `astar-sx`: about 15.9s -> about 14.3s.
- Switching the span path from generic `InvHom::step` to deterministic stepping
  removed per-call deduplication allocation. In one PTB20 smoke run,
  `astar-outside` improved from about 77s to about 59s, and `astar-sx` improved
  from about 78s to about 43s.

So the data structure fixed a real asymptotic waste, and deterministic stepping
removed a large constant factor that was hidden by the old counters.

## Limitations

The largest current waste is candidate dominance. In the PTB20 `astar-zero`
run, A* still considered about 334M candidate edges, and about 222M of them were
discarded because they did not improve the best pending score for their parent
product state. The sibling finder cannot fix this: by the time a candidate has
been generated, we have already paid for sibling lookup, `right.step`, child
tuple construction, and score computation.

The span specialization currently only handles unary and binary left rules
directly. Higher arities are correct via the generic fallback, but they do not
benefit from product-aware span lookup.

The zero heuristic remains a stress test rather than the intended fast mode. It
finalizes many states and therefore exposes candidate-generation overhead. SX
and outside heuristics should reduce finalized states, but they still suffer
from dominated candidate generation among the states they do explore.

## Next Steps

The next optimization should reduce dominated candidate work before agenda
insertion. The promising direction is to aggregate candidate alternatives for
the same parent product state and keep only the best local candidate before
calling `push_candidate`. This targets the 222M dominated candidates directly
and should reduce scoring, heap updates, and backpointer churn.

After that change, profile again. If candidate dominance is no longer the main
cost, the next likely targets are right-transition volume in the span path and
the generic set-trie fallback for higher-arity rules.

If higher-arity string rules become important, extend the product-aware sibling
idea to tuples of finalized products. That should be done as a general
arity-aware span index, not as inverse-homomorphism-specific logic.
