#!/usr/bin/env bash
# Hosted generated-C replay of the firmware handoff corpus: normalize the
# checked captures into the exact decoder inputs, then run the corpus harness
# through the shared lake-ir hosted-boundary runner (ordinary or sanitized).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
export LEANOS_HOSTED_BOUNDARY_ID="${LEANOS_HOSTED_BOUNDARY_ID:-firmware-corpus}"
out="build/firmware-corpus"
rm -rf "$out"
python3 ./scripts/firmware-corpus.py validate
python3 ./scripts/firmware-corpus.py normalize --out "$out"
LEANOS_FIRMWARE_CORPUS_REPLAY="$out/replay.tsv" \
  exec ./scripts/check-boot-handoff-host.sh "$mode"
