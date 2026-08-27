#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="${1:-$repo_root/build/ci/tool-versions.txt}"
cc="${LEANOS_CC:-gcc}"
mkdir -p "$(dirname "$output")"

image_digest="${LEANOS_CI_IMAGE_DIGEST:-}"
if [[ -n "$image_digest" && ! "$image_digest" =~ ^sha256:[0-9a-f]{64}$ ]]; then
  echo "error: LEANOS_CI_IMAGE_DIGEST must be an sha256 OCI digest" >&2
  exit 1
fi

{
  printf 'source-revision: '
  git -C "$repo_root" rev-parse HEAD
  printf 'release-version: %s\n' "${LEANOS_VERSION:-0.1.0}"
  printf 'ci-image-digest: %s\n' "${image_digest:-not-containerized}"
  echo 'reference-os: Ubuntu 24.04 (x86_64)'
  printf 'lean-toolchain: '
  cat "$repo_root/lean-toolchain"
  lake --version
  lean --version
  printf 'image-compiler-command: %s\n' "$cc"
  "$cc" --version | sed -n '1p'
  ld --version | sed -n '1p'
  grub-mkrescue --version | sed -n '1p'
  xorriso -version 2>&1 | sed -n '1p'
  qemu-system-x86_64 --version | sed -n '1p'
  timeout --version | sed -n '1p'
} > "$output"

echo "recorded tool versions in ${output#$repo_root/}"
