# Parsing pipeline

Parsing an IRTG means finding grammar derivation trees whose interpretations
match one or more observed inputs.

## 1. Read the grammar

An `InputCodec<Irtg>` reads the grammar. The standard codec registry selects
`.irtg` syntax directly or compiles a Tulipac `.tag` grammar to the same `Irtg`
result type. The resulting grammar contains:

- an explicit weighted tree automaton for grammar derivations;
- a signature for grammar rule labels;
- one homomorphism and algebra instance per interpretation.

The grammar automaton recognizes valid derivation trees. It does not directly
recognize strings or interpreted trees.

## 2. Parse and decompose an input value

A typed interpretation parses the external object. For a string algebra, the
input text becomes a sequence of interned terminal symbols.

The algebra then constructs a decomposition automaton for that value. String
states are spans; TAG string values may also represent discontinuous pairs,
and TAG derived-tree decomposition uses subtrees and one-hole contexts. Each
decomposition recognizes exactly the algebra terms that evaluate to the
observed value.

## 3. Apply inverse homomorphism

The interpretation's homomorphism maps each grammar symbol to a term over the
algebra signature. `InvHom` asks the decomposition automaton what state results
from evaluating that term.

Conceptually, the inverse-homomorphic automaton recognizes grammar-labeled
trees whose interpreted value equals the input. Symbols with identical
homomorphic images can share work through condensed transitions.

## 4. Intersect with the grammar

The grammar automaton is intersected with the inverse-homomorphic
decomposition automaton. A product state records both:

- the grammar state reached by a derivation;
- the decomposition state reached by its interpretation.

An accepting product state therefore represents a complete grammatical
derivation whose interpretation covers the input.

With several input interpretations, `Irtg::parse` repeats this process,
intersecting the current chart with each additional interpretation.

## 5. Choose an execution strategy

`MaterializationStrategy` controls how the intersection is explored.

### Top-down condensed materialization

This is the default chart-building strategy. It starts from accepting state
pairs and follows compatible rules downward. Condensed inverse-homomorphism
rules allow one transition computation to cover many grammar symbols with the
same image.

The result is a complete explicit parse chart suitable for Viterbi extraction,
language enumeration, or further automaton processing.

### Indexed condensed materialization

This strategy grows reachable product states using partial-child indexes,
joining rules only when they share an already known child. It exposes detailed
intersection statistics and remains useful for algorithm comparison.

### A* one-best parsing

A* searches product states in best-first order and can stop after proving the
best accepting derivation. It avoids building parts of the chart that cannot
affect the one-best result.

Available heuristics are:

| Heuristic | Information used |
| --- | --- |
| `zero` | No estimate beyond accumulated weight. |
| `outside` | Grammar-only outside weights. |
| `sx` | A sentence-length-aware universal string bound. |
| `sxf` | SX combined with obligatory-terminal feasibility filtering. |

A* is exact when its heuristic is admissible. The current implementation
requires grammar rule weights no greater than one.

String parsing has a product-aware span sibling finder for common unary and
binary rules. Higher arities use the general indexed fallback.

## 6. Extract and interpret a derivation

For a complete chart, `Explicit::viterbi` returns the highest-weight derivation
tree. The direct A* interface returns the one-best derivation without requiring
a full chart.

The grammar signature resolves numeric rule symbols back to names. Each
interpretation can then evaluate the derivation tree to produce its public
value. Its algebra-owned display codec chooses a GUI-neutral visual
representation; independent textual output codecs provide Copy/export
formats. `eval` writes interpretation values and the derivation into an
annotated Alto corpus.
