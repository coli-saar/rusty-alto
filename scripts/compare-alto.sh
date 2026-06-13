#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
usage:
  scripts/compare-alto.sh --suite [--report REPORT.md] [--iterations N] [--warmup N] [--alto-jar JAR]
  scripts/compare-alto.sh --auto FILE.auto --trees TREES.txt [--name NAME] [--report REPORT.md] [--iterations N] [--warmup N] [--alto-jar JAR]

Runs the same automaton/tree workloads with rusty-alto and Alto.
By default, the script uses ~/Documents/workspace/alto/build/libs/alto-2.3.8-SNAPSHOT-all.jar.

The --suite mode generates small/large deterministic and nondeterministic
workloads across several automaton shapes and writes a Markdown report with
comparison tables.
USAGE
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
AUTO=""
TREES=""
NAME="custom"
REPORT=""
ITERATIONS="100"
WARMUP="10"
SUITE=0
ALTO_JAR="${ALTO_JAR:-$HOME/Documents/workspace/alto/build/libs/alto-2.3.8-SNAPSHOT-all.jar}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --suite)
      SUITE=1
      shift
      ;;
    --auto)
      AUTO="$2"
      shift 2
      ;;
    --trees)
      TREES="$2"
      shift 2
      ;;
    --name)
      NAME="$2"
      shift 2
      ;;
    --report)
      REPORT="$2"
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

if [[ "$SUITE" -eq 0 && ( -z "$AUTO" || -z "$TREES" ) ]]; then
  usage >&2
  exit 2
fi

if [[ -z "$REPORT" ]]; then
  if [[ "$SUITE" -eq 1 ]]; then
    REPORT="$ROOT/target/alto-comparison/report.md"
  else
    REPORT="$ROOT/target/alto-comparison/${NAME}.md"
  fi
fi

CLASS_DIR="$ROOT/target/alto-compare-classes"
RESULTS="$ROOT/target/alto-comparison/results.tsv"
WORKLOAD_DIR="$ROOT/target/alto-comparison/workloads"
mkdir -p "$CLASS_DIR" "$(dirname "$RESULTS")" "$WORKLOAD_DIR" "$(dirname "$REPORT")"
: > "$RESULTS"

javac -cp "$ALTO_JAR" -d "$CLASS_DIR" "$ROOT/tools/alto-compare/AltoRun.java"
cargo build --quiet --release --bin compare_alto

write_det_workload() {
  local name="$1"
  local depth="$2"
  local count="$3"
  local dir="$WORKLOAD_DIR/$name"
  mkdir -p "$dir"
  DEPTH="$depth" COUNT="$count" "$ROOT/scripts/make-deterministic-workload.sh" "$dir" >/dev/null
  echo "$dir/deterministic.auto"$'\t'"$dir/deterministic.trees"
}

write_det_unary_workload() {
  local name="$1"
  local depth="$2"
  local count="$3"
  local dir="$WORKLOAD_DIR/$name"
  mkdir -p "$dir"
  local auto="$dir/deterministic-unary.auto"
  local trees="$dir/deterministic-unary.trees"
  local tree
  tree="$(make_unary_tree "$depth")"

  cat > "$auto" <<'AUTO'
Q! -> g(Q)
Q! -> a
AUTO

  write_repeated_tree "$tree" "$count" "$trees"
  echo "$auto"$'\t'"$trees"
}

write_nondet_binary_workload() {
  local name="$1"
  local depth="$2"
  local count="$3"
  local dir="$WORKLOAD_DIR/$name"
  mkdir -p "$dir"
  local auto="$dir/nondeterministic-binary.auto"
  local trees="$dir/nondeterministic-binary.trees"
  local tree
  tree="$(make_balanced_tree "$depth")"

  cat > "$auto" <<'AUTO'
Q! -> f(Q,Q)
R! -> f(R,R)
Q! -> a
R! -> a
AUTO

  write_repeated_tree "$tree" "$count" "$trees"
  echo "$auto"$'\t'"$trees"
}

write_nondet_unary_workload() {
  local name="$1"
  local depth="$2"
  local count="$3"
  local dir="$WORKLOAD_DIR/$name"
  mkdir -p "$dir"
  local auto="$dir/nondeterministic-unary.auto"
  local trees="$dir/nondeterministic-unary.trees"
  local tree
  tree="$(make_unary_tree "$depth")"

  cat > "$auto" <<'AUTO'
Q! -> g(Q)
R! -> g(R)
Q! -> a
R! -> a
AUTO

  write_repeated_tree "$tree" "$count" "$trees"
  echo "$auto"$'\t'"$trees"
}

write_repeated_tree() {
  local tree="$1"
  local count="$2"
  local trees="$3"
  local i
  : > "$trees"
  for ((i = 0; i < count; i++)); do
    printf '%s\n' "$tree" >> "$trees"
  done
}

make_balanced_tree() {
  local depth="$1"
  if [[ "$depth" -eq 0 ]]; then
    printf 'a'
  else
    printf 'f('
    make_balanced_tree "$((depth - 1))"
    printf ','
    make_balanced_tree "$((depth - 1))"
    printf ')'
  fi
}

make_unary_tree() {
  local depth="$1"
  if [[ "$depth" -eq 0 ]]; then
    printf 'a'
  else
    printf 'g('
    make_unary_tree "$((depth - 1))"
    printf ')'
  fi
}

run_engine() {
  local engine="$1"
  local auto="$2"
  local trees="$3"
  if [[ "$engine" == "rust" ]]; then
    "$ROOT/target/release/compare_alto" \
      --auto "$auto" \
      --trees "$trees" \
      --iterations "$ITERATIONS" \
      --warmup "$WARMUP"
  else
    java -cp "$CLASS_DIR:$ALTO_JAR" AltoRun \
      --auto "$auto" \
      --trees "$trees" \
      --iterations "$ITERATIONS" \
      --warmup "$WARMUP"
  fi
}

field() {
  local key="$1"
  local text="$2"
  printf '%s\n' "$text" | awk -F= -v k="$key" '$1 == k {print $2; exit}'
}

run_workload() {
  local name="$1"
  local kind="$2"
  local size="$3"
  local auto="$4"
  local trees="$5"

  echo "running $name ($kind/$size)" >&2
  local rust_out alto_out
  rust_out="$(run_engine rust "$auto" "$trees")"
  alto_out="$(run_engine alto "$auto" "$trees")"

  local rust_accepted alto_accepted rust_roots alto_roots rust_ns alto_ns rust_mode tree_count runs
  rust_accepted="$(field accepted_last "$rust_out")"
  alto_accepted="$(field accepted_last "$alto_out")"
  rust_roots="$(field root_states_last "$rust_out")"
  alto_roots="$(field root_states_last "$alto_out")"
  rust_ns="$(field ns_per_tree "$rust_out")"
  alto_ns="$(field ns_per_tree "$alto_out")"
  rust_mode="$(field mode "$rust_out")"
  tree_count="$(field tree_count "$rust_out")"
  runs="$(field runs "$rust_out")"

  if [[ "$rust_accepted" != "$alto_accepted" || "$rust_roots" != "$alto_roots" ]]; then
    echo "semantic mismatch for $name" >&2
    echo "rust output:" >&2
    echo "$rust_out" >&2
    echo "alto output:" >&2
    echo "$alto_out" >&2
    exit 1
  fi

  local speedup
  speedup="$(awk -v a="$alto_ns" -v r="$rust_ns" 'BEGIN { if (r == 0) print "inf"; else printf "%.2f", a / r }')"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "$kind" "$size" "$rust_mode" "$tree_count" "$runs" \
    "$rust_accepted" "$rust_roots" "$rust_ns" "$alto_ns" "$speedup" "$auto" "$trees" >> "$RESULTS"
}

if [[ "$SUITE" -eq 1 ]]; then
  IFS=$'\t' read -r auto trees < <(write_det_workload deterministic-binary-small 5 64)
  run_workload deterministic-binary-small deterministic-binary small "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_det_workload deterministic-binary-large 9 32)
  run_workload deterministic-binary-large deterministic-binary large "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_det_unary_workload deterministic-unary-small 16 128)
  run_workload deterministic-unary-small deterministic-unary small "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_det_unary_workload deterministic-unary-large 256 32)
  run_workload deterministic-unary-large deterministic-unary large "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_nondet_binary_workload nondeterministic-binary-small 3 64)
  run_workload nondeterministic-binary-small nondeterministic-binary small "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_nondet_binary_workload nondeterministic-binary-large 5 16)
  run_workload nondeterministic-binary-large nondeterministic-binary large "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_nondet_unary_workload nondeterministic-unary-small 16 128)
  run_workload nondeterministic-unary-small nondeterministic-unary small "$auto" "$trees"

  IFS=$'\t' read -r auto trees < <(write_nondet_unary_workload nondeterministic-unary-large 256 32)
  run_workload nondeterministic-unary-large nondeterministic-unary large "$auto" "$trees"
else
  run_workload "$NAME" custom custom "$AUTO" "$TREES"
fi

{
  echo "# Alto Comparison Report"
  echo
  echo "- Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "- Iterations: $ITERATIONS"
  echo "- Warmup iterations: $WARMUP"
  echo "- Alto jar: \`$ALTO_JAR\`"
  echo
  echo "All workloads use the same automaton and tree files for both engines. The Rust runner reports \`mode=det\` when it can use its deterministic path."
  echo
  echo "| Workload | Kind | Size | Rust mode | Trees | Runs | Accepted | Root states | rusty-alto ns/tree | Alto ns/tree | Alto/rusty speedup |"
  echo "| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
  awk -F'\t' '{
    printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11
  }' "$RESULTS"
  echo
  echo "## Inputs"
  echo
  echo "| Workload | Automaton | Trees |"
  echo "| --- | --- | --- |"
  awk -F'\t' '{
    printf "| %s | `%s` | `%s` |\n", $1,$12,$13
  }' "$RESULTS"
} > "$REPORT"

cat "$REPORT"
echo
echo "wrote report: $REPORT" >&2
