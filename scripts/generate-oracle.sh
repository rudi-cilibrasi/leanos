#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
out="${1:-build/oracle}"
revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
mkdir -p "$out"
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-oracle > "$out/corpus.tsv"
awk -F '\t' '
  BEGIN { print "/* Generated from LeanOS.Oracle; do not edit. */"; print "struct oracle_vector { unsigned adapter, argc; unsigned long long words[4], expected; const char *id; };"; print "static const struct oracle_vector oracle_vectors[] = {" }
  $1 ~ /^[0-9]+$/ {
    n=split($4,w,","); printf "{%s,%d,{", ($3=="KernelTransition" ? 0 : 1),n
    for(i=1;i<=4;i++) printf "%s%sULL",(i>1 ? "," : ""),(i<=n ? w[i] : 0)
    printf "},%sULL,\"%s\"},\n",$5,$2
  }
  END { print "};"; print "#define ORACLE_VECTOR_COUNT (sizeof(oracle_vectors)/sizeof(oracle_vectors[0]))" }
' "$out/corpus.tsv" > "$out/corpus.h"

