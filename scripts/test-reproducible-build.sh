#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
version="${LEANOS_VERSION:-0.1.0}"
first="$(mktemp -d)"
trap 'rm -rf "$first"' EXIT

./scripts/build-image.sh
cp "build/boot/leanos-${version}-x86_64.iso" build/boot/leanos.elf \
  build/boot/leanos.map build/boot/SOURCE_REVISION "$first/"
./scripts/build-image.sh

for artifact in "leanos-${version}-x86_64.iso" leanos.elf leanos.map \
  SOURCE_REVISION; do
  if ! cmp -s "$first/$artifact" "build/boot/$artifact"; then
    echo "error: repeated build changed $artifact" >&2
    sha256sum "$first/$artifact" "build/boot/$artifact" >&2
    exit 1
  fi
done

echo "Repeated image, ELF, map, and revision builds are byte-identical"
