#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="${1:-$repo_root/build/ci/tool-versions.txt}"
mkdir -p "$(dirname "$output")"

{
  printf 'source-revision: '
  git -C "$repo_root" rev-parse HEAD
  printf 'release-version: %s\n' "${LEANOS_VERSION:-0.1.0}"
  echo 'reference-os: Ubuntu 24.04 (x86_64)'
  printf 'lean-toolchain: '
  cat "$repo_root/lean-toolchain"
  lake --version
  lean --version
  gcc --version | head -n 1
  ld --version | head -n 1
  grub-mkrescue --version | head -n 1
  xorriso -version 2>&1 | head -n 1
  qemu-system-x86_64 --version | head -n 1
  timeout --version | head -n 1
} > "$output"

echo "recorded tool versions in ${output#$repo_root/}"
