#!/usr/bin/env bash
set -euo pipefail

first="${1:?usage: compare-reproducibility-manifests.sh FIRST SECOND}"
second="${2:?usage: compare-reproducibility-manifests.sh FIRST SECOND}"

if ! cmp -s "$first" "$second"; then
  echo "error: independent builds changed the reproducibility manifest" >&2
  diff -u "$first" "$second" >&2 || true
  exit 1
fi

echo "Independent build reproducibility manifests are byte-identical"
