#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
out="${1:-build/oracle}"
revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
mkdir -p "$out"
tool_signature="${LEANOS_ORACLE_TOOL_SIGNATURE:-}"
signature_file="$out/generated-oracle.inputs.sha256"
if [[ -n "$tool_signature" ]]; then
  current_signature="$({
    printf '%s\0%s\0' "$revision" "$tool_signature"
    sha256sum "$root/scripts/generate-oracle.sh"
  } | sha256sum | awk '{print $1}')"
  if [[ -f "$out/corpus.tsv" && -f "$out/corpus.h" && \
      -f "$signature_file" ]] &&
      read -r stored_signature stored_tsv_hash stored_header_hash \
        < "$signature_file" &&
      [[ "$stored_signature" == "$current_signature" ]] &&
      [[ "$stored_tsv_hash" == "$(sha256sum "$out/corpus.tsv" | awk '{print $1}')" ]] &&
      [[ "$stored_header_hash" == "$(sha256sum "$out/corpus.h" | awk '{print $1}')" ]]; then
    exit 0
  fi
fi
stage="$(mktemp -d "$out/.oracle.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-oracle > "$stage/corpus.tsv"
awk -F '\t' '
  BEGIN { print "/* Generated from LeanOS.Oracle; do not edit. */"; print "struct oracle_vector { unsigned adapter, argc; unsigned long long words[6], expected; const char *id; };"; print "static const struct oracle_vector oracle_vectors[] = {"; vectorIndex=0 }
  $1 ~ /^[0-9]+$/ {
    name=toupper($2); gsub(/[^A-Z0-9]/,"_",name); printf "#define ORACLE_INDEX_%s %d\n",name,vectorIndex++
    n=split($4,w,","); adapter=($3=="KernelTransition" ? 0 : ($3=="Syscall.scalar" ? 1 : ($3=="IPCSyscall.scalar" ? 2 : ($3=="Preemption.scalar" ? 3 : ($3=="Preemption.resumable" ? 4 : ($3=="BootAllocation.scalar" ? 5 : ($3=="Interrupt.userReturn" ? 6 : ($3=="BlockingIPC.scalar" ? 7 : ($3=="CapabilityReuse.scalar" ? 8 : ($3=="Interrupt.entry" ? 9 : ($3=="ExtendedState.denialDispatch" ? 10 : ($3=="PrivilegeEntryControl.scalar" ? 11 : ($3=="FaultDispatch.scalar" ? 12 : ($3=="DirectPortIO.scalar" ? 13 : ($3=="Interrupt.nmi" ? 14 : ($3=="Interrupt.bootPhase" ? 15 : ($3=="StaleTranslation.scalar" ? 16 : ($3=="CompositeDispatcher.stateful" ? 18 : ($3=="IOTLB.scalar" ? 19 : 17))))))))))))))))))); printf "{%s,%d,{", adapter,n
    for(i=1;i<=6;i++) printf "%s%sULL",(i>1 ? "," : ""),(i<=n ? w[i] : 0)
    printf "},%sULL,\"%s\"},\n",$5,$2
  }
  END { print "};"; print "#define ORACLE_VECTOR_COUNT (sizeof(oracle_vectors)/sizeof(oracle_vectors[0]))" }
' "$stage/corpus.tsv" > "$stage/corpus.h"
for artifact in corpus.tsv corpus.h; do
  if [[ -f "$out/$artifact" ]] && cmp -s "$stage/$artifact" "$out/$artifact"; then
    continue
  fi
  mv "$stage/$artifact" "$out/$artifact"
done
if [[ -n "$tool_signature" ]]; then
  printf '%s %s %s\n' "$current_signature" \
    "$(sha256sum "$out/corpus.tsv" | awk '{print $1}')" \
    "$(sha256sum "$out/corpus.h" | awk '{print $1}')" > "$signature_file"
fi
