#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
usage:
  scripts/compare-condensed-parsing.sh [--states N] [--len N] [--vocab N] [--lexical-labels N] [--binary-labels N] [--iterations N] [--warmup N] [--report REPORT.md] [--alto-jar JAR]

Compares condensed inverse-homomorphism parsing for rusty-alto and Alto.
The generated workload maps many source grammar labels to terms over the
StringAlgebra signature and intersects the grammar with the condensed inverse
homomorphism of a string decomposition automaton.
USAGE
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STATES=16
LEN=12
VOCAB=4
LEXICAL_LABELS=4
BINARY_LABELS=16
ITERATIONS=10
WARMUP=2
REPORT="$ROOT/target/alto-comparison/condensed-parsing-report.md"
ALTO_JAR="${ALTO_JAR:-$HOME/Documents/workspace/alto/build/libs/alto-2.3.8-SNAPSHOT-all.jar}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --states)
      STATES="$2"
      shift 2
      ;;
    --len)
      LEN="$2"
      shift 2
      ;;
    --vocab)
      VOCAB="$2"
      shift 2
      ;;
    --lexical-labels)
      LEXICAL_LABELS="$2"
      shift 2
      ;;
    --binary-labels)
      BINARY_LABELS="$2"
      shift 2
      ;;
    --iterations)
      ITERATIONS="$2"
      shift 2
      ;;
    --warmup)
      WARMUP="$2"
      shift 2
      ;;
    --report)
      REPORT="$2"
      shift 2
      ;;
    --alto-jar)
      ALTO_JAR="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ ! -f "$ALTO_JAR" ]]; then
  echo "Alto jar not found: $ALTO_JAR" >&2
  echo "Set ALTO_JAR, pass --alto-jar, or build Alto with ./gradlew shadowJar." >&2
  exit 1
fi

CLASS_DIR="$ROOT/target/alto-compare-classes"
RESULTS="$ROOT/target/alto-comparison/condensed-parsing-results.tsv"
mkdir -p "$CLASS_DIR" "$(dirname "$RESULTS")" "$(dirname "$REPORT")"
: > "$RESULTS"

javac -cp "$ALTO_JAR" -d "$CLASS_DIR" "$ROOT/tools/alto-compare/AltoCondensedParsingRun.java"
cargo build --quiet --release --bin compare_condensed_parsing

run_engine() {
  local engine="$1"
  local decomp="${2:-explicit}"
  local intersection="${3:-indexed-condensed}"
  if [[ "$engine" == "rust" ]]; then
    "$ROOT/target/release/compare_condensed_parsing" \
      --states "$STATES" \
      --len "$LEN" \
      --vocab "$VOCAB" \
      --lexical-labels "$LEXICAL_LABELS" \
      --binary-labels "$BINARY_LABELS" \
      --iterations "$ITERATIONS" \
      --warmup "$WARMUP" \
      --decomp "$decomp" \
      --intersection "$intersection"
  else
    java -cp "$CLASS_DIR:$ALTO_JAR" AltoCondensedParsingRun \
      --states "$STATES" \
      --len "$LEN" \
      --vocab "$VOCAB" \
      --lexical-labels "$LEXICAL_LABELS" \
      --binary-labels "$BINARY_LABELS" \
      --iterations "$ITERATIONS" \
      --warmup "$WARMUP"
  fi
}

field() {
  local key="$1"
  local text="$2"
  printf '%s\n' "$text" | awk -F= -v k="$key" '$1 == k {print $2; exit}'
}

record() {
  local engine="$1"
  local decomp="${2:-explicit}"
  local intersection="${3:-indexed-condensed}"
  local label="$engine"
  if [[ "$engine" == "rust" ]]; then
    label="rust-$decomp-$intersection"
  fi
  echo "running $label condensed parsing" >&2
  local out
  out="$(run_engine "$engine" "$decomp" "$intersection")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$label" \
    "$(field decomp "$out")" \
    "$(field intersection "$out")" \
    "$(field grammar_rules "$out")" \
    "$(field decomp_rules "$out")" \
    "$(field condensed_rules_last "$out")" \
    "$(field output_states "$out")" \
    "$(field output_rules "$out")" \
    "$(field ns_per_parse "$out")" \
    "$(field elapsed_ms "$out")" \
    "$(field iterations "$out")" \
    "$(field algorithm "$out")" >> "$RESULTS"
}

record rust explicit eager
record rust explicit indexed-condensed
record rust implicit eager
record rust implicit indexed-condensed
record alto

state_rule_pairs="$(awk -F'\t' '{print $7 "\t" $8}' "$RESULTS" | sort -u | wc -l | tr -d ' ')"

if [[ "$state_rule_pairs" != "1" ]]; then
  echo "rusty-alto/Alto semantic mismatch" >&2
  cat "$RESULTS" >&2
  exit 1
fi

{
  echo "# Condensed Parsing Comparison Report"
  echo
  echo "- Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "- Grammar states: $STATES"
  echo "- Sentence length: $LEN"
  echo "- Vocabulary size: $VOCAB"
  echo "- Lexical source labels per word: $LEXICAL_LABELS"
  echo "- Binary source labels mapping to concat: $BINARY_LABELS"
  echo "- Iterations: $ITERATIONS"
  echo "- Warmup iterations: $WARMUP"
  echo "- Alto jar: \`$ALTO_JAR\`"
  echo
  echo "The workload maps source-side tree automaton labels into terms over the StringAlgebra signature. Lexical source labels map to word constants, and all binary source labels map to \`*(?0, ?1)\`. The parser intersects the source grammar with the condensed inverse homomorphism of the string decomposition automaton."
  echo
  echo "| Engine | Decomp | Intersection | Grammar rules | Decomp rules | Right queries/rules | Output states | Output rules | ns/parse | Elapsed ms |"
  echo "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
  awk -F'\t' '{
    printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6,$7,$8,$9,$10
  }' "$RESULTS"
  echo
  echo "## Derived Ratios"
  echo
  echo "| Comparison | Speedup |"
  echo "| --- | ---: |"
  awk -F'\t' '
    $1 == "rust-explicit-indexed-condensed" { rust_explicit = $9 }
    $1 == "rust-implicit-indexed-condensed" { rust_implicit = $9 }
    $1 == "alto" { alto = $9 }
    END {
      if (rust_explicit > 0) printf "| Alto / rusty-alto explicit | %.2f |\n", alto / rust_explicit;
      if (rust_implicit > 0) printf "| Alto / rusty-alto implicit | %.2f |\n", alto / rust_implicit;
      if (rust_implicit > 0) printf "| rusty-alto explicit / implicit | %.2f |\n", rust_explicit / rust_implicit;
    }
  ' "$RESULTS"
} > "$REPORT"

cat "$REPORT"
echo
echo "wrote report: $REPORT" >&2
