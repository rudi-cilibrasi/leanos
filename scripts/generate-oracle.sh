#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
out="${1:-build/oracle}"
revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
mkdir -p "$out"
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-oracle > "$out/corpus.tsv"
awk -F '\t' '
  BEGIN { print "/* Generated from LeanOS.Oracle; do not edit. */"; print "struct oracle_vector { unsigned adapter, argc; unsigned long long words[5], expected; const char *id; };"; print "static const struct oracle_vector oracle_vectors[] = {"; vectorIndex=0 }
  $1 ~ /^[0-9]+$/ {
    name=toupper($2); gsub(/[^A-Z0-9]/,"_",name); printf "#define ORACLE_INDEX_%s %d\n",name,vectorIndex++
    n=split($4,w,","); adapter=($3=="KernelTransition" ? 0 : ($3=="Syscall.scalar" ? 1 : ($3=="IPCSyscall.scalar" ? 2 : ($3=="Preemption.scalar" ? 3 : ($3=="Preemption.resumable" ? 4 : ($3=="BootAllocation.scalar" ? 5 : ($3=="Interrupt.userReturn" ? 6 : ($3=="BlockingIPC.scalar" ? 7 : ($3=="CapabilityReuse.scalar" ? 8 : 9))))))))); printf "{%s,%d,{", adapter,n
    for(i=1;i<=5;i++) printf "%s%sULL",(i>1 ? "," : ""),(i<=n ? w[i] : 0)
    printf "},%sULL,\"%s\"},\n",$5,$2
  }
  END { print "};"; print "#define ORACLE_VECTOR_COUNT (sizeof(oracle_vectors)/sizeof(oracle_vectors[0]))" }
' "$out/corpus.tsv" > "$out/corpus.h"
