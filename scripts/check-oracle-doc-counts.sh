#!/usr/bin/env bash
# The model-oracle corpus size quoted in the README and docs/model-oracle.md
# is the one `Oracle.corpus_shape` proves (issue #470).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
count="$(sed -n 's/^theorem corpus_shape : vectors.length = \([0-9]*\) := by decide$/\1/p' LeanOS/Oracle.lean)"
[[ "$count" =~ ^[0-9]+$ ]] || { echo "error: corpus_shape count not found" >&2; exit 1; }
for doc in README.md docs/model-oracle.md; do
  quoted="$(grep -oE '[0-9]+-vector' "$doc" | sort -u)"
  if [[ "$quoted" != "$count-vector" ]]; then
    echo "error: $doc quotes ${quoted//$'\n'/,} but corpus_shape proves $count vectors" >&2
    exit 1
  fi
done
echo "oracle corpus size in docs matches corpus_shape ($count)"
