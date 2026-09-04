#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
version="${LEANOS_VERSION:-0.1.0}"
# The byte-reproducible artifact set is derived from scripts/scenario-manifest.json
# by the evidence runner, so a new scenario's artifacts cannot escape this gate
# without a manifest entry.
mapfile -t artifacts < <(
  "$repo_root/scripts/run-emulator-evidence.py" reproducibility-artifacts \
    --version "$version"
)
[[ ${#artifacts[@]} -gt 0 ]] || {
  echo "error: the derived reproducibility artifact list is empty" >&2
  exit 1
}

if [[ "${1:-}" == "--list" ]]; then
  printf '%s\n' "${artifacts[@]}"
  exit 0
fi

output="${1:-$repo_root/build/boot/REPRODUCIBILITY-SHA256SUMS}"
boot_dir="${2:-$repo_root/build/boot}"
mkdir -p "$(dirname "$output")"
for artifact in "${artifacts[@]}"; do
  [[ -f "$boot_dir/$artifact" ]] || {
    echo "error: reproducibility artifact is missing: $artifact" >&2
    exit 1
  }
done
(
  cd "$boot_dir"
  sha256sum "${artifacts[@]}"
) >"$output"
