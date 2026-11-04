#!/usr/bin/env bash
# QuickProof pin check (ADR 0030, issue #597). Each experiments/quickproof/*/pins.tsv
# lists the repository files a QuickProof theorem is about, with the SHA-256 of
# their contents at the commit the proof covers. A file that differs at HEAD
# means the theorem no longer covers the code that is built: re-check the proof
# (scripts/check-quickproof.sh) and update the pin, as for refinement drift.
# Needs no QuickProof, Coq or CompCert, so it runs in ordinary CI.
#
# usage: scripts/check-quickproof-pins.sh [--update]
#   --update rewrites each pins.tsv after a re-check: the digests of the files
#   it lists outside the experiment (the C under test, the Lean sources of the
#   modelled exports) and of every file under the experiment's project/ and
#   proof/, with the upstream commit of its project.conf.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
shopt -s nullglob
if [[ "${1:-}" == "--update" ]]; then
  for exp in experiments/quickproof/*/; do
    pins="${exp}pins.tsv"
    commit="$(sed -n 's/^COMMIT=\([0-9a-f]*\).*/\1/p' "${exp}project/project.conf" | cut -c1-12)"
    [[ -n "$commit" ]] || { echo "error: ${exp}project/project.conf has no COMMIT" >&2; exit 1; }
    {
      printf '# path\tsha256\tupstream commit the theorems are about (project.conf COMMIT)\n'
      { if [[ -f "$pins" ]]; then grep -v '^#' "$pins" | cut -f1 | grep -v "^${exp}" || true; fi
        find "${exp}project" "${exp}proof" -type f; } | sort -u |
        while read -r path; do
          [[ -n "$path" ]] && printf '%s\t%s\t%s\n' "$path" "$(sha256sum "$path" | cut -d' ' -f1)" "$commit"
        done
    } >"$pins.new"
    mv "$pins.new" "$pins"
    echo "updated $pins: $(grep -vc '^#' "$pins") files"
  done
  exit 0
fi
status=0 count=0
for pins in experiments/quickproof/*/pins.tsv; do
  while IFS=$'\t' read -r path digest commit || [[ -n "$path" ]]; do
    [[ -z "$path" || "$path" == \#* ]] && continue
    count=$((count + 1))
    if [[ ! -f "$path" ]]; then
      echo "error: $pins: pinned file $path is missing" >&2; status=1; continue
    fi
    actual="$(sha256sum "$path" | cut -d' ' -f1)"
    if [[ "$actual" != "$digest" ]]; then
      echo "error: $path changed since the QuickProof theorem of $(dirname "$pins") (pinned at $commit)" >&2
      status=1
    fi
  done <"$pins"
done
if [[ "$count" -eq 0 ]]; then
  echo "error: no QuickProof pins found under experiments/quickproof/*/pins.tsv" >&2; exit 1
fi
[[ "$status" -eq 0 ]] && echo "QuickProof pins current: $count files"
exit "$status"
