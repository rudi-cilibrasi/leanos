#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="${1:-$repo_root/build/qemu-wasm-reproducibility}"

if [[ "$output" != /* ]]; then
  output="$repo_root/$output"
fi
mkdir -p "$output"
output="$(cd "$output" && pwd)"
if [[ -n "$(find "$output" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  echo "error: reproducibility output directory is not empty: $output" >&2
  exit 1
fi

first="$output/clean-build-1"
second="$output/clean-build-2"
"$repo_root/scripts/build-qemu-wasm-source.sh" "$first"
"$repo_root/scripts/build-qemu-wasm-source.sh" "$second"
"$repo_root/scripts/verify-qemu-wasm-manifest.py" \
  --prototype --staging "$first" --compare "$second"

echo "two byte-identical clean qemu-wasm builds preserved in ${output#$repo_root/}"
