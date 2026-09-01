#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/source/build/boot" "$scratch/restored"
printf 'fixture image\n' > "$scratch/source/build/boot/leanos.iso"

bundle="$scratch/leanos-image.tar.gz"
./scripts/image-bundle.sh create "$bundle" "$scratch/source"
revision="$(git rev-parse HEAD)"
./scripts/image-bundle.sh verify "$bundle" "$revision" "$scratch/restored"
cmp "$scratch/source/build/boot/leanos.iso" "$scratch/restored/build/boot/leanos.iso"

printf 'stale image\n' > "$scratch/restored/build/boot/leanos.iso"
./scripts/image-bundle.sh verify "$bundle" "$revision" "$scratch/restored"
cmp "$scratch/source/build/boot/leanos.iso" "$scratch/restored/build/boot/leanos.iso"

if ./scripts/image-bundle.sh verify "$bundle" \
    "0000000000000000000000000000000000000000" "$scratch/rejected" \
    >/dev/null 2>&1; then
  echo "error: image bundle accepted the wrong source revision" >&2
  exit 1
fi

echo "Image bundle regression checks passed"
