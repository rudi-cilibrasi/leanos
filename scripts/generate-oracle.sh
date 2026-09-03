#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
out="${1:-build/oracle}"
revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
mkdir -p "$out"
tool_signature="${LEANOS_ORACLE_TOOL_SIGNATURE:-}"
signature_file="$out/generated-oracle.inputs.sha256"
# corpus.tsv/corpus.h: the frozen scalar corpus and its C table.
# vocabulary.tsv/composite-tokens.h: the Lean-owned boundary token vocabulary.
# boundary-abi.tsv/boundary-abi.h: the @[export] prototype inventory.
# serial-protocol.tsv/.h/.sh: the versioned serial record vocabulary.
artifacts=(corpus.tsv corpus.h vocabulary.tsv composite-tokens.h
  boundary-abi.tsv boundary-abi.h
  serial-protocol.tsv serial-protocol.h serial-protocol.sh)
artifact_hashes() {
  local artifact
  for artifact in "${artifacts[@]}"; do
    [[ -f "$out/$artifact" ]] || { printf 'missing\n'; return; }
  done
  (cd "$out" && sha256sum "${artifacts[@]}") | sha256sum | awk '{print $1}'
}
if [[ -n "$tool_signature" ]]; then
  current_signature="$({
    printf '%s\0%s\0' "$revision" "$tool_signature"
    sha256sum "$root/scripts/generate-oracle.sh" \
      "$root/scripts/render-oracle-header.awk" \
      "$root/scripts/render-composite-tokens.awk" \
      "$root/scripts/render-boundary-abi.awk" \
      "$root/scripts/render-serial-protocol.awk"
  } | sha256sum | awk '{print $1}')"
  if [[ -f "$signature_file" ]] &&
      read -r stored_signature stored_hashes < "$signature_file" &&
      [[ "$stored_signature" == "$current_signature" ]] &&
      [[ "$stored_hashes" == "$(artifact_hashes)" ]]; then
    exit 0
  fi
fi
stage="$(mktemp -d "$out/.oracle.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-oracle > "$stage/corpus.tsv"
awk -f scripts/render-oracle-header.awk "$stage/corpus.tsv" > "$stage/corpus.h"
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-oracle tokens > "$stage/vocabulary.tsv"
awk -f scripts/render-composite-tokens.awk "$stage/vocabulary.tsv" \
  > "$stage/composite-tokens.h"
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-oracle serial > "$stage/serial-protocol.tsv"
awk -v target=h -f scripts/render-serial-protocol.awk "$stage/serial-protocol.tsv" \
  > "$stage/serial-protocol.h"
awk -v target=sh -f scripts/render-serial-protocol.awk "$stage/serial-protocol.tsv" \
  > "$stage/serial-protocol.sh"
# The export inventory walks the compiled LeanOS environment, so every library
# module must be built before it runs; the oracle executable above only builds
# its own imports.
lake build LeanOS >/dev/null
LEANOS_SOURCE_REVISION="$revision" lake exe leanos-abi > "$stage/boundary-abi.tsv"
awk -f scripts/render-boundary-abi.awk "$stage/boundary-abi.tsv" \
  > "$stage/boundary-abi.h"
for artifact in "${artifacts[@]}"; do
  if [[ -f "$out/$artifact" ]] && cmp -s "$stage/$artifact" "$out/$artifact"; then
    continue
  fi
  mv "$stage/$artifact" "$out/$artifact"
done
if [[ -n "$tool_signature" ]]; then
  printf '%s %s\n' "$current_signature" "$(artifact_hashes)" > "$signature_file"
fi
