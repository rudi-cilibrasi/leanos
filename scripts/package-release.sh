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

evidence="build/evidence/emulator-evidence.json"
./scripts/run-emulator-evidence.py verify "$evidence" --version "$version"

release="$repo_root/build/release"
rm -rf "$release"
mkdir -p "$release"
# Every build/boot artifact that ships in a release is derived from
# scripts/scenario-manifest.json by the evidence runner; nothing here names one
# by hand. The list is (source, release name) pairs, one per line.
release_destinations=()
while IFS=$'\t' read -r source destination; do
  [[ -n "$source" && -n "$destination" ]] || {
    echo "error: malformed derived release artifact line" >&2
    exit 1
  }
  [[ -f "$source" ]] || {
    echo "error: derived release artifact is missing: $source" >&2
    exit 1
  }
  cp "$source" "$release/$destination"
  release_destinations+=("$destination")
done < <(./scripts/run-emulator-evidence.py release-artifacts --version "$version")
[[ ${#release_destinations[@]} -gt 0 ]] || {
  echo "error: the derived release artifact list is empty" >&2
  exit 1
}
cp "$evidence" "$release/EMULATOR_EVIDENCE.json"
cp scripts/emulator-evidence-matrix.tsv "$release/EMULATOR_EVIDENCE_MATRIX.tsv"
cp docs/release-notes.md "$release/RELEASE_NOTES.md"
LEANOS_VERSION="$version" ./scripts/record-tool-versions.sh \
  "$release/TOOLCHAIN.txt"
(cd "$release" && sha256sum "${release_destinations[@]}" \
  EMULATOR_EVIDENCE.json EMULATOR_EVIDENCE_MATRIX.tsv \
  TOOLCHAIN.txt RELEASE_NOTES.md \
  > SHA256SUMS)

echo "packaged $tag release assets in build/release"
