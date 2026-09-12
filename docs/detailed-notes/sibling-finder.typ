#import "@preview/pergamon:0.7.1": *
#import "@preview/bananote:0.1.2": *
#import "@preview/ctheorems:1.1.3": *

#show: note.with(
  title: [Algebra-specific sibling indexes for IRTG parsing],
  authors: (
    ([Alexander Koller], [Saarland University]),
  ),
  date: datetime.today(),
  version: [0.1],
)

#show: thmrules.with(qed-symbol: $square$)
#set math.equation(numbering: "(1)")

#let proposition = thmbox(
  "proposition",
  "Proposition",
  base: none,
  fill: rgb("#fbfaf4"),
  stroke: rgb("#d9cfa8"),
  inset: (x: 1em, y: 0.75em),
)

#abstract[
Parsing an interpreted regular tree grammar can be expressed as the intersection of its derivation-tree automaton with the inverse homomorphic image of an input decomposition automaton. A literal implementation constructs the inverse image before intersecting it and may enumerate many transitions that cannot participate in a parse. The sibling-finder algorithm fuses both operations. For each binary algebra operation, the algebra supplies a sibling index that directly enumerates compatible items. The index representation is private to the algebra: strings use one-dimensional boundary arrays, while TAG uses one- or two-dimensional boundary arrays depending on the operation. A generic bottom-up evaluator lifts these local indexes through homomorphism terms of target rank at most two. Rules with the same homomorphism right-hand side share this evaluation: the algorithm first constructs a condensed inverse-homomorphism transition and only then matches it against grammar rules. The resulting automaton is still the complete packed parse chart. This note specifies the interface, algorithm, correctness argument, and its consequences for string and TAG parsing.
]

= Parsing as automaton intersection

An interpreted regular tree grammar consists of a finite regular tree grammar $G$ and, for each interpretation, a tree homomorphism $h$ into an algebra. A derivation tree $t$ is licensed by the interpretation exactly when evaluating $h(t)$ yields the observed input $w$.

The input is represented by a decomposition tree automaton $D_w$. Its states describe parts of $w$, its transitions describe valid applications of algebra operations, and its accepting states describe the complete input. For the ordinary string algebra, states are half-open spans $[i,j)$ and concatenation has the transition

$ "concat"([i,k), [k,j)) -> [i,j). $

Let $A_G$ be the tree automaton that recognizes the derivation trees of $G$. The parse chart recognizes

$ L(A_G) ∩ h^(-1)(L(D_w)). $

This equation separates grammatical well-formedness from input decomposition, but it does not prescribe an efficient construction. Materializing $h^(-1)(D_w)$ first can create transitions without knowing which grammar states will ever meet their children. The implementation therefore evaluates homomorphism terms only as product states become reachable. This is the same broad objective as the sibling-finder technique of #citet("groschwitz-etal-2016-efficient").

= The local sibling-index contract

Consider a binary operation $f$ of the decomposition automaton. A conventional bottom-up step receives two child states and returns zero or more parent states. The computational problem is to find the useful second child after the first child has become available.

A _sibling index_ belongs to one occurrence of $f$ in a term program. It stores term-chart item identifiers separately for child positions 0 and 1. After an item with state $q$ arrives at position $i$, the query $"partners"(i,q)$ returns exactly the previously stored items at position $1-i$ whose states can participate with $q$ in an $f$-transition. The query order is unspecified, but the result must be complete and contain no incompatible items.

The interface deliberately does not expose a key type. Equality keys are one possible implementation, but an algebra can instead map states directly to array coordinates. This keeps representation knowledge with the algebra and lets the generic parser monomorphize a query into ordinary indexing operations. The parser still calls the decomposition automaton after lookup because the index finds child pairs, whereas the automaton constructs their parent state or states.

For string concatenation, the index contains one bucket for every input boundary. A left span $[i,k)$ is stored in the position-0 array at $k$, and a new right span $[k,j)$ reads that bucket. The position-1 array supports the symmetric arrival order. Both insertion and lookup are constant-time apart from iterating the returned partners, and the two arrays contain $O(n)$ buckets in total.

The TAG string algebra uses contiguous states $[i,j)$ and discontinuous states $([i,j),[k,l))$. Its five binary operations require either one shared boundary or a pair of boundaries. Each operation gets its own index with the following coordinates:

#table(
  columns: (1.1fr, 2fr, 2fr),
  align: (left, left, left),
  inset: 5pt,
  stroke: 0.5pt + luma(75%),
  [operation], [coordinate for child 0], [coordinate for child 1],
  [concatenate two strings], [$j$ from $[i,j)$], [$k$ from $[k,l)$],
  [prefix string to pair], [$j$ from $[i,j)$], [$k$ from $([k,l),[m,n))$],
  [append string to pair], [$l$ from $([i,j),[k,l))$], [$m$ from $[m,n)$],
  [fill a gap], [$(j,k)$ from $([i,j),[k,l))$], [$(m,n)$ from $[m,n)$],
  [insert pair into gap], [$(j,k)$ from $([i,j),[k,l))$], [$(m,p)$ from $([m,n),[o,p))$],
)

The concatenation indexes allocate $O(n)$ buckets, and the wrapping indexes allocate $O(n^2)$ buckets. A coordinate pair $(a,b)$ is represented by the row-major offset $a(n+1)+b$, so it is still accessed by one array lookup. State shapes that cannot occupy a given child position are neither inserted nor returned.

= From a homomorphism term to a chart rule

The sibling indexes from the previous section apply to one algebra operation at a time. An interpretation, however, may map one grammar symbol to a term containing several operations. We therefore need to propagate decomposition states through the entire term before we can add a rule to the parse chart.

Consider a grammar rule

$ g(p_0, p_1) -> p, $

where $p_0$ and $p_1$ are its child grammar states and $p$ is its parent grammar state. Suppose the interpretation maps its label $g$ to

$ h(g) = f(a(x_0), b(x_1)). $

The variables refer to the children of the grammar rule: $x_0$ denotes the value produced below $p_0$, and $x_1$ denotes the value produced below $p_1$. The operations $a$, $b$, and $f$ belong to the interpreted algebra. For example, they may manipulate string spans. To check the rule against an input, the parser must find decomposition states $q_0$, $q_1$, and $q$ such that evaluating $h(g)$ with $x_0=q_0$ and $x_1=q_1$ can produce $q$.

The parser compiles $h(g)$ into a small description of its tree structure. The description records each variable and operation, the children of every operation, and the parent of every non-root node. We call this description the _term program_. It lets the parser evaluate the term incrementally from its variables toward its root. The current implementation permits nullary, unary, and binary algebra operations. Operations with more than two arguments are rejected because the sibling-index interface joins two child positions. This restriction concerns operations inside $h(g)$; the grammar rule itself may have more than two children.

The incremental evaluation is stored in a _term chart_. An item in this chart has the form

$ (u, q, a_u), $

where:

- $u$ is a node of the term program;
- $q$ is a decomposition state obtained by evaluating the subterm rooted at $u$; and
- $a_u$ is the compact sequence of decomposition states assigned to the variables below $u$, in their term-traversal order.

For the example, learning that $x_0$ may have state $q_0$ first creates the item $(x_0,q_0,[q_0])$. Evaluating $a$ may turn this into $(a(x_0),q_a,[q_0])$. The right branch similarly produces $(b(x_1),q_b,[q_1])$. At $f$, the sibling index retrieves the previously stored items compatible with the newly arrived state. The decomposition automaton constructs the parent state for each pair. If it produces $q$, the two assignment sequences are merged to obtain

$ (h(g), q, [q_0,q_1]). $

If the variables occur in a different order in the homomorphism term, the compiler records one root permutation that restores source-rule child order. Intermediate items remain compact and do not carry empty slots for variables outside their subterm.

At the root of the term, this item represents the inverse-homomorphism transition

$ g(q_0,q_1) -> q. $

The transition is _condensed_ because the term chart does not attach it to one particular grammar rule. Every grammar label with the same homomorphism term shares the same term program, term chart, and transition. The stored item contains decomposition states only; it contains neither grammar-rule identifiers nor parse-chart state identifiers.

It remains to combine this condensed transition with grammar rules. A parse-chart state is a pair $(p,q)$: the grammar can be in state $p$ while the decomposition automaton is in state $q$. If the chart already contains $(p_0,q_0)$ and $(p_1,q_1)$, combining the example grammar rule with the condensed transition adds

$ g((p_0,q_0),(p_1,q_1)) -> (p,q) $

to the parse chart.

The parser must perform this combination in either arrival order. When a new condensed transition appears, it looks up all grammar rules whose child states have compatible parse-chart pairs. When a new parse-chart state appears, it looks up all previously constructed condensed transitions that mention its decomposition state in the corresponding child position. Two indexes support these lookups: a trie stores grammar rules by their ordered child-state sequence, and a child-position index stores condensed transitions by variable position and decomposition state. Thus neither lookup scans all grammar rules or all condensed transitions.

Every newly created parent state $(p,q)$ is placed on an agenda of states that still need to be processed. Processing continues until the agenda is empty. Duplicate term items, condensed transitions, parse-chart states, and parse-chart rules are suppressed, so reaching this fixed point terminates whenever the finite product chart has been exhausted.

= Correctness

The output must retain the derivation trees and weights of the ordinary intersection. Sibling indexes change partner search, but they must not change this language.

#proposition("Soundness")[
Every rule emitted by the sibling-finder construction belongs to $A_G ∩ h^(-1)(D_w)$.
]

Every emitted rule originates in a rule of $A_G$ selected by the program-specific trie. Its child grammar states match product states for every component of the condensed transition. The homomorphism term reaches that transition only through successful calls to the transition function of $D_w$. Therefore the emitted parent pair is licensed by both automata. The output rule copies the source symbol and weight, so neither derivation identity nor weight is invented.

#proposition("Completeness")[
Assume every sibling index returns every previously stored compatible partner. Every reachable rule of $A_G ∩ h^(-1)(D_w)$ is eventually emitted.
]

Proceed bottom-up over a successful product derivation. Its child product states are eventually placed on the outer agenda. They therefore activate every corresponding variable in the shared term chart. Nullary and unary term steps are enumerated directly. At a binary term node, whichever valid child item arrives second retrieves the first from the sibling index. The decomposition step therefore reproduces the successful transition. Induction over the homomorphism term produces its condensed root transition. The child grammar states are members of the corresponding product-state query sets, so the trie returns the source rule and the algorithm emits the product rule.

Together, soundness and completeness show that sibling finding is an evaluation strategy for the same packed chart, not an approximation.

= Complexity and scope

For an array-backed equality index, let $C_k$ be a bucket and let $|C_k^0|$ and $|C_k^1|$ count the items indexed on its two sides. A binary term node examines

$ sum_k |C_k^0| |C_k^1| $

candidate pairs, rather than the full Cartesian product of both sides. Exact boundary coordinates partition spans by the constraints already imposed by the algebra. Another sibling-index implementation may organize its compatible partners differently; the generic interface guarantees exact enumeration, not a particular asymptotic bound.

For a fixed context-free grammar under the string algebra, there are $O(n^2)$ span states and the familiar split-point combinations give $O(n^3)$ time and $O(n^2)$ product states. For a fixed, binarized TAG encoding, discontinuous states contribute $O(n^4)$ possible product states and binary combinations yield the standard $O(n^6)$ worst-case parsing time. Grammar size, homomorphism-term size, ambiguity, and the number of emitted packed rules multiply these input-length bounds.

These are worst-case bounds. Boundary indexes can make a constrained grammar grow much more slowly in practice because only reachable grammar--span pairs and matching buckets are visited. Condensation gives an independent reduction. If $r$ source rules share one homomorphism right-hand side, their algebra-side term items are stored once rather than $r$ times. The grammar-rule trie and the final output rules still retain the distinctions that affect the parse chart; condensation removes only redundant intermediate structure.

= Engineering consequences

The sibling-index factory owns algebra-specific compatibility knowledge. It receives the concrete decomposition automaton and operation symbol, and creates the index for one binary term node. The evaluator owns the generic machinery for agendas, term programs, deduplication, and output packing. This boundary avoids both embedding string or TAG cases in the intersection algorithm and adding sibling-finder concerns to the general tree-automaton traits.

The implementation uses append-only item arrays and stores item identifiers in algebra-specific buckets. Partner lookup borrows these buckets rather than copying them. Small vectors keep the common low-arity decomposition tuples and child lists inline. Program-specific tries store each grammar rule once, while child-position indexes connect new product states to existing condensed transitions. A persistent stack drains local propagation work, and the outer FIFO agenda discovers product states. Thus every large structure represents either a distinct algebra-side fact, a source rule, a source-child occurrence, an algebra-specific boundary table, or an emitted chart rule; there is no generic table proportional to an unnecessary Cartesian product.

The present abstraction deliberately supports binary target operations. It does not require equality matching: an algebra may implement inequalities, intervals, or another exact partner search behind the same interface. A target operation of rank above two requires a different joining protocol and is rejected during term compilation.

= Summary

The sibling finder fuses inverse homomorphism with automaton intersection while retaining the useful condensation boundary inside the fused computation. Product states activate variables in charts shared by equal homomorphism right-hand sides; decomposition states propagate upward; algebra-specific indexes retrieve compatible partners at binary nodes; and ordinary transition calls construct their parent states. Condensed root transitions are then joined with source rules through the product chart. The result remains a complete explicit parse chart. For strings and TAG strings, dense span-boundary arrays provide constant-time access to partner buckets, but the method is neither universally applicable nor guaranteed to dominate goal-directed parsing on every grammar.

#add-bib-resource(read("sibling-finder-references.bib"))
#print-bananote-bibliography()
