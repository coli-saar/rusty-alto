#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
usage:
  scripts/compare-intersection.sh [--states N] [--len N] [--vocab N] [--iterations N] [--warmup N] [--report REPORT.md] [--alto-jar JAR]

Compares naive and sibling-finder-style intersection materialization for
rusty-alto and Alto on a generated grammar-vs-string-chart workload.
USAGE
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STATES=16
LEN=12
VOCAB=4
ITERATIONS=10
WARMUP=2
REPORT="$ROOT/target/alto-comparison/intersection-report.md"
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
RESULTS="$ROOT/target/alto-comparison/intersection-results.tsv"
mkdir -p "$CLASS_DIR" "$(dirname "$RESULTS")" "$(dirname "$REPORT")"
: > "$RESULTS"

javac -cp "$ALTO_JAR" -d "$CLASS_DIR" "$ROOT/tools/alto-compare/AltoIntersectionRun.java"
cargo build --quiet --release --bin compare_intersection

run_engine() {
  local engine="$1"
  local algorithm="$2"
  if [[ "$engine" == "rust" ]]; then
    "$ROOT/target/release/compare_intersection" \
      --algorithm "$algorithm" \
      --states "$STATES" \
      --len "$LEN" \
      --vocab "$VOCAB" \
      --iterations "$ITERATIONS" \
      --warmup "$WARMUP"
  else
    java -cp "$CLASS_DIR:$ALTO_JAR" AltoIntersectionRun \
      --algorithm "$algorithm" \
      --states "$STATES" \
      --len "$LEN" \
      --vocab "$VOCAB" \
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
  local algorithm="$2"
  echo "running $engine/$algorithm" >&2
  local out
  out="$(run_engine "$engine" "$algorithm")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$engine" \
    "$algorithm" \
    "$(field left_rules "$out")" \
    "$(field right_rules "$out")" \
    "$(field output_states "$out")" \
    "$(field output_rules "$out")" \
    "$(field ns_per_intersection "$out")" \
    "$(field elapsed_ms "$out")" \
    "$(field iterations "$out")" >> "$RESULTS"
}

record rust naive
record rust sibling
record alto naive
record alto sibling

rust_naive_states="$(awk -F'\t' '$1 == "rust" && $2 == "naive" {print $5}' "$RESULTS")"
rust_sibling_states="$(awk -F'\t' '$1 == "rust" && $2 == "sibling" {print $5}' "$RESULTS")"
rust_naive_rules="$(awk -F'\t' '$1 == "rust" && $2 == "naive" {print $6}' "$RESULTS")"
rust_sibling_rules="$(awk -F'\t' '$1 == "rust" && $2 == "sibling" {print $6}' "$RESULTS")"

if [[ "$rust_naive_states" != "$rust_sibling_states" || "$rust_naive_rules" != "$rust_sibling_rules" ]]; then
  echo "rust naive/sibling semantic mismatch" >&2
  cat "$RESULTS" >&2
  exit 1
fi

{
  echo "# Intersection Comparison Report"
  echo
  echo "- Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "- Grammar states: $STATES"
  echo "- Sentence length: $LEN"
  echo "- Vocabulary size: $VOCAB"
  echo "- Iterations: $ITERATIONS"
  echo "- Warmup iterations: $WARMUP"
  echo "- Alto jar: \`$ALTO_JAR\`"
  echo
  echo "The workload intersects a generated explicit grammar automaton with an explicit CKY-style string-span automaton. The naive algorithm repeatedly scans compatible rule pairs; the sibling algorithm uses child-state indexes / sibling finders to consider only rules adjacent to discovered child pairs."
  echo
  echo "| Engine | Algorithm | Left rules | Right rules | Output states | Output rules | ns/intersection | Elapsed ms |"
  echo "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"
  awk -F'\t' '{
    printf "| %s | %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6,$7,$8
  }' "$RESULTS"
  echo
  echo "## Derived Ratios"
  echo
  echo "| Comparison | Speedup |"
  echo "| --- | ---: |"
  awk -F'\t' '
    $1 == "rust" && $2 == "naive" { rn = $7 }
    $1 == "rust" && $2 == "sibling" { rs = $7 }
    $1 == "alto" && $2 == "naive" { an = $7 }
    $1 == "alto" && $2 == "sibling" { as = $7 }
    END {
      if (rs > 0) printf "| rusty-alto naive / sibling | %.2f |\n", rn / rs;
      if (as > 0) printf "| Alto naive / sibling | %.2f |\n", an / as;
      if (rs > 0) printf "| Alto sibling / rusty-alto sibling | %.2f |\n", as / rs;
      if (rn > 0) printf "| Alto naive / rusty-alto naive | %.2f |\n", an / rn;
    }
  ' "$RESULTS"
} > "$REPORT"

cat "$REPORT"
echo
echo "wrote report: $REPORT" >&2
