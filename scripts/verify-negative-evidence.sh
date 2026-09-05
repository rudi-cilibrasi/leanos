#!/usr/bin/env bash
# Verify one scenario's controlled-negative evidence directory against the
# declaration in scripts/scenario-manifest.json: the manifest must list exactly
# the declared number of negatives, every negative must have failed with a
# classified failure (or the declared exact class), and its serial and output
# logs must be retained.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
scenario="${1:?usage: verify-negative-evidence.sh <scenario> [build-dir]}"
build="${2:-build/boot}"
IFS=$'\t' read -r _ directory count failure_class _ \
  < <(./scripts/run-emulator-evidence.py negative-evidence "$scenario")
manifest="$build/$directory/manifest.tsv"
[[ -s "$manifest" ]] || {
  echo "error: $scenario negative evidence manifest is missing: $manifest" >&2
  exit 1
}
observed="$(tail -n +2 "$manifest" | wc -l)"
[[ "$observed" -eq "$count" ]] || {
  echo "error: $scenario declares $count controlled negatives but recorded $observed" >&2
  exit 1
}
while IFS=$'\t' read -r mode status observed_class serial_log output_log; do
  [[ "$status" -ne 0 ]] || {
    echo "error: $scenario negative '$mode' did not fail" >&2
    exit 1
  }
  if [[ "$failure_class" == serial-protocol ]]; then
    [[ "$observed_class" == serial-protocol ]] || {
      echo "error: $scenario negative '$mode' failed as '$observed_class', not serial-protocol" >&2
      exit 1
    }
  else
    [[ "$observed_class" != unexpected ]] || {
      echo "error: $scenario negative '$mode' failed without a classified reason" >&2
      exit 1
    }
  fi
  [[ -s "$build/$directory/$serial_log" && -s "$build/$directory/$output_log" ]] || {
    echo "error: $scenario negative '$mode' lacks retained serial or output evidence" >&2
    exit 1
  }
done < <(tail -n +2 "$manifest")
echo "$scenario negative evidence verified: $count controlled negatives"
