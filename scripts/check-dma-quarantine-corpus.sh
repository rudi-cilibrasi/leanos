#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

first="$(mktemp)"
second="$(mktemp)"
trap 'rm -f "$first" "$second"' EXIT

LEANOS_SOURCE_REVISION=corpus-check lake exe leanos-dma-corpus >"$first"
LEANOS_SOURCE_REVISION=corpus-check lake exe leanos-dma-corpus >"$second"
cmp "$first" "$second"

awk -F '\t' '
  NR == 1 {
    if ($1 != "leanos-dma-quarantine-corpus" || $2 != "1") exit 10
    next
  }
  NR == 2 {
    if ($1 != "source-revision" || $2 != "corpus-check") exit 11
    next
  }
  {
    if (NF != 7) exit 12
    pre = split($4, words, ",")
    operation = split($5, words, ",")
    post = split($6, words, ",")
    result = split($7, words, ",")
    if (pre != 421 || operation != 211 || post != 421 || result != 1) exit 13
    if ($1 == previous_trace && $4 != previous_post) exit 14
    previous_trace = $1
    previous_post = $6
    vectors++
  }
  END { if (vectors != 6) exit 15 }
' "$first"

echo "DMA quarantine corpus checks passed"
