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

mkdir -p "$scratch/unsafe-source/build/boot"
ln -s /tmp "$scratch/unsafe-source/build/boot/escape"
if ./scripts/image-bundle.sh create "$scratch/unsafe-source.tar.gz" \
    "$scratch/unsafe-source" >/dev/null 2>&1; then
  echo "error: image bundle accepted a symlink source" >&2
  exit 1
fi

mkdir -p "$scratch/unsafe-archive/build/boot"
ln -s /tmp "$scratch/unsafe-archive/build/boot/escape"
tar -C "$scratch/unsafe-archive" -czf "$scratch/unsafe-archive.tar.gz" build/boot
sha256sum "$scratch/unsafe-archive.tar.gz" | awk \
  '{print $1 "  unsafe-archive.tar.gz"}' > "$scratch/unsafe-archive.tar.gz.sha256"
if ./scripts/image-bundle.sh verify "$scratch/unsafe-archive.tar.gz" "$revision" \
    "$scratch/rejected" >/dev/null 2>&1; then
  echo "error: image bundle extracted a symlink entry" >&2
  exit 1
fi

echo "Image bundle regression checks passed"
