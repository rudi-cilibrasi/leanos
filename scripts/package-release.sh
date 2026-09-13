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

# Materialize the complete query before replacing a prior release. A process
# substitution would hide a producer failure after it emitted partial rows.
artifact_rows="$(./scripts/run-emulator-evidence.py release-artifacts --version "$version")"
[[ -n "$artifact_rows" ]] || {
  echo "error: the derived release artifact list is empty" >&2
  exit 1
}
python3 scripts/check-platform-profiles.py
platform_rows="$(python3 - <<'PY'
import json
from pathlib import Path
registry = json.loads(Path('hardware/platform-profiles.json').read_text())
for row in registry['profiles']:
    print('hardware/' + row['manifest'] + '\t' + row['release_asset'])
PY
)"
[[ -n "$platform_rows" ]] || {
  echo "error: the platform profile registry is empty" >&2
  exit 1
}

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
done <<< "$artifact_rows"
[[ ${#release_destinations[@]} -gt 0 ]] || {
  echo "error: the derived release artifact list is empty" >&2
  exit 1
}
cp "$evidence" "$release/EMULATOR_EVIDENCE.json"
cp scripts/emulator-evidence-matrix.tsv "$release/EMULATOR_EVIDENCE_MATRIX.tsv"
cp docs/release-notes.md "$release/RELEASE_NOTES.md"
cp hardware/platform-profiles.json "$release/PLATFORM_PROFILES.json"
profile_destinations=()
while IFS=$'\t' read -r source destination; do
  [[ -f "$source" && -n "$destination" ]] || {
    echo "error: malformed platform profile release row" >&2
    exit 1
  }
  cp "$source" "$release/$destination"
  profile_destinations+=("$destination")
done <<< "$platform_rows"
LEANOS_VERSION="$version" ./scripts/record-tool-versions.sh \
  "$release/TOOLCHAIN.txt"
(cd "$release" && sha256sum "${release_destinations[@]}" \
  EMULATOR_EVIDENCE.json EMULATOR_EVIDENCE_MATRIX.tsv \
  PLATFORM_PROFILES.json "${profile_destinations[@]}" \
  TOOLCHAIN.txt RELEASE_NOTES.md \
  > SHA256SUMS)

echo "packaged $tag release assets in build/release"
