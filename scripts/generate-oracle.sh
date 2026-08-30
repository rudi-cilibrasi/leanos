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
awk -f scripts/render-oracle-header.awk "$stage/corpus.tsv" > "$stage/corpus.h"
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
