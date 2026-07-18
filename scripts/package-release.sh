#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tag="${1:-${GITHUB_REF_NAME:-}}"
if [[ ! "$tag" =~ ^v([0-9]+\.[0-9]+\.[0-9]+)$ ]]; then
  echo "error: release tag must be vMAJOR.MINOR.PATCH" >&2
  exit 1
fi
version="${BASH_REMATCH[1]}"
revision="$(git rev-parse HEAD)"
if [[ "$(git rev-list -n 1 "$tag")" != "$revision" ]]; then
  echo "error: tag $tag does not resolve to checked-out revision $revision" >&2
  exit 1
fi

release="$repo_root/build/release"
rm -rf "$release"
mkdir -p "$release"
cp "build/boot/leanos-${version}-x86_64.iso" \
  "$release/leanos-${version}-x86_64.iso"
cp build/boot/leanos.elf "$release/leanos-${version}-x86_64.elf"
cp build/boot/leanos.map "$release/leanos-${version}-x86_64.map"
cp build/boot/serial.log "$release/leanos-${version}-serial.log"
cp "build/boot/leanos-${version}-x86_64-preemption.iso" \
  "$release/leanos-${version}-x86_64-preemption.iso"
cp build/boot/leanos-preemption.elf \
  "$release/leanos-${version}-x86_64-preemption.elf"
cp build/boot/leanos-preemption.map \
  "$release/leanos-${version}-x86_64-preemption.map"
cp build/boot/preemption.serial.log \
  "$release/leanos-${version}-preemption-serial.log"
cp build/boot/corpus.tsv "$release/leanos-${version}-oracle.tsv"
cp build/boot/SOURCE_REVISION "$release/SOURCE_REVISION"
cp docs/release-notes.md "$release/RELEASE_NOTES.md"
LEANOS_VERSION="$version" ./scripts/record-tool-versions.sh \
  "$release/TOOLCHAIN.txt"
(cd "$release" && sha256sum \
  "leanos-${version}-x86_64.iso" "leanos-${version}-x86_64.elf" \
  "leanos-${version}-x86_64.map" "leanos-${version}-serial.log" \
  "leanos-${version}-x86_64-preemption.iso" \
  "leanos-${version}-x86_64-preemption.elf" \
  "leanos-${version}-x86_64-preemption.map" \
  "leanos-${version}-preemption-serial.log" \
  "leanos-${version}-oracle.tsv" \
  SOURCE_REVISION TOOLCHAIN.txt RELEASE_NOTES.md > SHA256SUMS)

echo "packaged $tag release assets in build/release"
