#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="${1:-$repo_root/build/ci/tool-versions.txt}"
cc="${LEANOS_CC:-gcc}"
toolchain_profile="${LEANOS_TOOLCHAIN_PROFILE:-gcc-reference}"
mkdir -p "$(dirname "$output")"

IFS=$'\t' read -r toolchain_profile toolchain_status toolchain_claim \
    lean_c_interface elf_layout_profile toolchain_manifest_sha256 \
    _profile_compiler _profile_compiler_version < <(
  "$repo_root/scripts/toolchain-profile.py" resolve \
    --profile "$toolchain_profile" --compiler "$cc" --format tsv
)

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
  printf 'toolchain-profile: %s\n' "$toolchain_profile"
  printf 'toolchain-profile-status: %s\n' "$toolchain_status"
  printf 'toolchain-profile-claim: %s\n' "$toolchain_claim"
  printf 'toolchain-profile-manifest-sha256: %s\n' \
    "$toolchain_manifest_sha256"
  printf 'lean-c-interface: %s\n' "$lean_c_interface"
  printf 'direct-port-elf-normalization: %s\n' "$elf_layout_profile"
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
