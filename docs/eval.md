# The `eval` evaluation frontend

`eval` reads an [Alto corpus](https://github.com/coli-saar/alto/wiki/Corpora), parses every
instance with an IRTG, and writes a new corpus containing, for each instance, the **derivation
tree** and the **interpreted value on every interpretation** (e.g. the predicted parse tree).

It shows a live progress bar, can dump per-sentence timing as CSV, supports a `--limit`, and lets
you choose the intersection algorithm and (for A*) the heuristic.

## Building and running

```sh
cargo build --release --bin eval
./target/release/eval <grammar.irtg> <corpus> [options]
```

For large grammars (e.g. the PTB grammar) always use `--release`; the debug build is far slower.

## Synopsis

```
eval <grammar.irtg> <corpus|-> [options]

  -o, --output <file>               write the output corpus to <file> (default: stdout)
  --limit <n>                       parse only the first n instances
  --algorithm <exhaustive|astar>    intersection algorithm (default: exhaustive)
  --heuristic <zero|outside|sx|sxf> A* heuristic, only with --algorithm astar (default: zero)
  --times <file.csv>                write per-sentence timing as CSV
  --input <interp>                  interpretation that parameterizes the sx/sxf heuristic
                                    (default: chosen automatically)
  --parseval <interp>               score a constituency-tree interpretation
  --parseval-output <file>          write Parseval table (default: parseval.txt)
  --evalb-param <file.prm>          EVALB parameters (default: Collins/PTB profile)
```

- `<corpus>` may be `-` to read from standard input.
- If `-o` is omitted, the output corpus is written to standard output (the progress bar is on
  stderr, so `-o` is optional even when piping).

## What it does, step by step

1. Loads the IRTG grammar (`<grammar.irtg>`).
2. Reads the corpus. Each interpretation line is handled according to its algebra:
   - **inputable** interpretations (string algebras) are parsed into values used as parse input;
   - **output-only** interpretations (tree algebras) are kept as raw text — they are *evaluated
     into* for output, never parsed *from*.
3. For each instance, intersects the inputable interpretations through the IRTG and extracts the
   best (Viterbi) derivation tree.
4. Writes an annotated output corpus: for every interpretation, the value obtained by interpreting
   the best derivation tree, followed by the derivation tree itself.

Instances that do not parse are written with `_null_` in place of the derivation tree (their input
lines are echoed unchanged), so the output stays 1:1 with the input.

## Corpus format

A corpus is a text file with a header and a sequence of instances. The header's first non-blank
line declares the comment prefix and whether the corpus is *annotated* (carries a derivation tree
per instance):

```
# IRTG annotated corpus file, v1.0
#
# interpretation string: de.up.ling.irtg.algebra.StringAlgebra
# interpretation tree: de.up.ling.irtg.algebra.BinarizingTreeWithAritiesAlgebra

NNP NNP VBZ NP .
S(NP-SBJ(NNP, NNP), VP(VBZ, NP), '.')
r22(r23(r1, r1), ...)

... next instance ...
```

- The comment prefix is whatever precedes `IRTG` on the header line (`#`, `///`, …); the reader
  accepts any prefix.
- Each instance is one line per interpretation, **in the order they are declared**, optionally
  followed by a derivation-tree line (only for annotated corpora), then a blank separator.
- The interpretations named in the corpus header must exist in the IRTG (otherwise `eval` panics
  with a clear message).

The **output** corpus is always annotated, with a header comment recording the run: timestamp,
algorithm, heuristic, grammar, and corpus paths. Tree values are written in term notation with
labels quoted as needed (e.g. `','`, `'PRP$'`) so the output round-trips.

## Interpretations and supported algebras

`eval` distinguishes two roles:

| Algebra class (Alto)                                  | Role         | Used for                |
| ----------------------------------------------------- | ------------ | ----------------------- |
| `de.up.ling.irtg.algebra.StringAlgebra`               | inputable    | parse input + output    |
| `de.up.ling.irtg.algebra.TreeWithAritiesAlgebra`      | output-only  | output (predicted tree) |
| `de.up.ling.irtg.algebra.BinarizingTreeWithAritiesAlgebra` | output-only | output (predicted tree) |

Any other algebra class causes the grammar to be rejected at load time. Parsing *from* a tree
interpretation (decomposition) is not implemented; tree interpretations are output-only.

When a corpus has several inputable interpretations they are all intersected. The predicted value
for **every** declared interpretation (inputable or output-only) is written to the output.

## Algorithms and heuristics

- `--algorithm exhaustive` (default): full chart intersection. Always applicable.
- `--algorithm astar`: A* one-best search. **Requires all grammar rule weights ≤ 1**
  (probability weights); otherwise the run aborts with a clear error. A* is exact, so it yields
  the same derivation trees as `exhaustive`, usually much faster on long sentences.

A* heuristics (`--heuristic`, only with `astar`):

| Heuristic | Description                                                                         |
| --------- | ----------------------------------------------------------------------------------- |
| `zero`    | Uninformed (default). A* degenerates to Knuth's algorithm; exact.                   |
| `outside` | Grammar-only outside-weight estimate. Algebra-agnostic, sentence-independent.       |
| `sx`      | Universal SX table built once for the longest sentence; admissible and exact.       |
| `sxf`     | `sx` combined with the obligatory-leaf F filter (prunes impossible spans).          |

`sx`/`sxf` are parameterized by the length of one input interpretation (the **primary**
interpretation). It is chosen automatically (preferring an interpretation named `english`, then
`i`, then the first inputable one); override with `--input <name>`. For corpora with a single
string interpretation — the usual case — this is automatic. With multiple string interpretations,
`sx`/`sxf` are exact only for the primary one, so prefer `zero`/`outside` there.

SX tables are cached beside the grammar in `<grammar>.sxcache/nmax<N>.bin`. `eval` first looks for
an exact entry, then reuses the smallest cached table whose `n_max` covers the corpus. The cache is
compatible with `ptb-eval`.

## Timing CSV

With `--times <file.csv>`, one row per instance is written (flushed as it goes):

```
sentence_no,length,parsed,score,parse_ms,output_ms,total_ms
```

- `length` — token count of the primary interpretation.
- `parsed` — whether a derivation was found.
- `score` — the best tree's score (log-probability with the default scorer); empty if no parse.
- `parse_ms` / `output_ms` — parse time and value-interpretation/write time.

## Parseval scoring

`--parseval <interp>` compares each predicted tree with the tree stored on that interpretation's
corpus line. The interpretation must use `TreeWithAritiesAlgebra` or
`BinarizingTreeWithAritiesAlgebra`.

For every scored sentence, `eval` writes labeled and unlabeled precision, recall, and F1 to a
human-readable EVALB-style table. The report defaults to `parseval.txt`; override it with
`--parseval-output`. The report ends with corpus-level micro-averages from the summed matched,
predicted, and gold constituent counts. Parseval scores are not printed to the console.

Failed parses contribute zero predicted constituents and retain their gold constituent count.
Sentences whose normalized terminal counts differ are marked as skipped.

Without `--evalb-param`, scoring uses a built-in Collins/PTB profile: conventional root, trace,
auxiliary, and punctuation labels are deleted, `ADVP` and `PRT` are equivalent, and sentences
longer than 40 normalized terminals are skipped. Custom parameter files may use `DELETE_LABEL`,
`DELETE_WORD`, `EQ_LABEL`, and `CUTOFF_LEN`. Standard non-scoring controls such as `DEBUG` and
`MAX_ERROR` are accepted and ignored.

## Examples

Parse a small string corpus with the bundled grammar, to stdout:

```sh
cargo run --release --bin eval -- benchdata/irtg/cfg.irtg my.corpus
```

Parse the PTB corpus, first 100 sentences, with A* + the SX heuristic, writing a corpus and a
timing CSV:

```sh
./target/release/eval ../alto/ptb/out.irtg ../alto/ptb/out.txt \
    --limit 100 --algorithm astar --heuristic sx \
    -o predicted.corpus --times times.csv
```

Read a corpus from stdin:

```sh
cat my.corpus | ./target/release/eval grammar.irtg -
```

Score a tree interpretation with custom EVALB parameters:

```sh
./target/release/eval grammar.irtg gold.corpus \
    --parseval tree --parseval-output scores.txt \
    --evalb-param COLLINS.prm -o predicted.corpus
```

## Notes and limitations

- The output is the parser's **best** tree, which generally differs from any gold tree in the
  input corpus — that is the point of an evaluation run. Scoring is opt-in with `--parseval`.
- Tree interpretations are output-only (no decomposition yet), so a corpus whose *only*
  interpretation is a tree algebra has nothing to parse from and is rejected.
- A* requires probability weights (≤ 1); use `exhaustive` for grammars with arbitrary weights.
