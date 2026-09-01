#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

usage() {
  echo "usage: $0 create BUNDLE [SOURCE_ROOT] | verify BUNDLE EXPECTED_REVISION [DEST_ROOT]" >&2
  exit 2
}

case "${1:-}" in
  create)
    bundle="${2:-}"
    source_root="${3:-$repo_root}"
    [[ -n "$bundle" ]] || usage
    [[ -d "$source_root/build/boot" ]] || {
      echo "error: image bundle source is missing build/boot" >&2
      exit 1
    }
    if find "$source_root/build/boot" ! -type d ! -type f -print -quit | grep -q .; then
      echo "error: image bundle source contains a non-regular entry" >&2
      exit 1
    fi
    revision="$(git -C "$repo_root" rev-parse HEAD)"
    staging="$(mktemp -d)"
    trap 'rm -rf "$staging"' EXIT
    mkdir -p "$staging/build"
    cp -a "$source_root/build/boot" "$staging/build/boot"
    {
      printf 'schema\tleanos-image-bundle-v1\n'
      printf 'revision\t%s\n' "$revision"
    } > "$staging/IMAGE_BUNDLE_MANIFEST.tsv"
    (
      cd "$staging"
      find build/boot -type f -print0 | sort -z | xargs -0 sha256sum \
        > IMAGE_BUNDLE_SHA256SUMS
    )
    mkdir -p "$(dirname "$bundle")"
    tar -C "$staging" -czf "$bundle" \
      IMAGE_BUNDLE_MANIFEST.tsv IMAGE_BUNDLE_SHA256SUMS build/boot
    sha256sum "$bundle" | awk -v name="$(basename "$bundle")" \
      '{print $1 "  " name}' > "$bundle.sha256"
    ;;
  verify)
    bundle="${2:-}"
    expected_revision="${3:-}"
    dest_root="${4:-$repo_root}"
    [[ -n "$bundle" && -n "$expected_revision" ]] || usage
    [[ -s "$bundle" && -s "$bundle.sha256" ]] || {
      echo "error: image bundle or outer digest is missing" >&2
      exit 1
    }
    (cd "$(dirname "$bundle")" && sha256sum -c "$(basename "$bundle").sha256")
    if tar -tzf "$bundle" | grep -Eq '(^/|(^|/)\.\.(/|$))'; then
      echo "error: image bundle contains an unsafe path" >&2
      exit 1
    fi
    if tar -tvzf "$bundle" | awk '
      substr($1, 1, 1) != "-" && substr($1, 1, 1) != "d" { found = 1 }
      END { exit found ? 0 : 1 }
    '; then
      echo "error: image bundle contains a non-regular entry" >&2
      exit 1
    fi
    staging="$(mktemp -d)"
    trap 'rm -rf "$staging"' EXIT
    tar -C "$staging" -xzf "$bundle"
    manifest="$staging/IMAGE_BUNDLE_MANIFEST.tsv"
    [[ "$(awk -F '\t' '$1 == "schema" {print $2}' "$manifest")" == "leanos-image-bundle-v1" ]] || {
      echo "error: unsupported image bundle schema" >&2
      exit 1
    }
    [[ "$(awk -F '\t' '$1 == "revision" {print $2}' "$manifest")" == "$expected_revision" ]] || {
      echo "error: image bundle revision does not match checkout" >&2
      exit 1
    }
    (cd "$staging" && sha256sum -c IMAGE_BUNDLE_SHA256SUMS)
    mkdir -p "$dest_root/build"
    rm -rf "$dest_root/build/boot"
    cp -a "$staging/build/boot" "$dest_root/build/boot"
    ;;
  *)
    usage
    ;;
esac
