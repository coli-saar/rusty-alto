#!/usr/bin/env bash
set -euo pipefail

OUT_DIR="${1:-benchdata/alto/deterministic}"
DEPTH="${DEPTH:-10}"
COUNT="${COUNT:-64}"

mkdir -p "$OUT_DIR"
AUTO="$OUT_DIR/deterministic.auto"
TREES="$OUT_DIR/deterministic.trees"

cat > "$AUTO" <<'AUTO'
Q! -> f(Q,Q)
Q! -> a
AUTO

make_tree() {
  local depth="$1"
  if [[ "$depth" -eq 0 ]]; then
    printf 'a'
  else
    printf 'f('
    make_tree "$((depth - 1))"
    printf ','
    make_tree "$((depth - 1))"
    printf ')'
  fi
}

: > "$TREES"
for _ in $(seq 1 "$COUNT"); do
  make_tree "$DEPTH" >> "$TREES"
  printf '\n' >> "$TREES"
done

cat <<EOF
wrote $AUTO
wrote $TREES
depth=$DEPTH
count=$COUNT
EOF
