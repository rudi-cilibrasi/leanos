#!/usr/bin/env bash
# Every boot-runner scenario's expected-transcript template must render through
# the generated serial vocabulary and the shared renderer without QEMU: each
# line is a known record placeholder or common segment marker, every @var:@
# placeholder is an allowlisted runner variable, and the shared segments appear
# once each in protocol order. The scenario manifest already requires one
# template per boot-runner row.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
./scripts/generate-oracle.sh "$tmp/oracle" >"$tmp/generate-oracle.log"
corpus="$tmp/oracle/corpus.tsv"
# shellcheck source=/dev/null
source "$tmp/oracle/serial-protocol.sh"
source ./scripts/expectation-template.sh
count=0
while IFS=$'\t' read -r scenario boot_scenario template; do
  [[ "$scenario" == scenario ]] && continue
  for name in "${expectation_variables[@]}"; do
    printf -v "$name" '%s' "1"
  done
  render_expectation "$template" >"$tmp/rendered"
  if grep -n '@' "$tmp/rendered"; then
    echo "expectation template $template renders an unresolved placeholder" >&2
    exit 1
  fi
  if ! head -n 1 "$template" | grep -Eq '^@[0-9]+/BOOT@ target=x86_64-q35 '; then
    echo "expectation template $template must open with the scenario's BOOT record" >&2
    exit 1
  fi
  if [[ "$(grep -c '^@common:' "$template")" != 4 ]] ||
    [[ "$(grep '^@common:' "$template" | tr '\n' ' ')" != "@common:prefix@ @common:oracle@ @common:pre-cpl3@ @common:controls@ " ]]; then
    echo "expectation template $template must use each common segment once, in protocol order" >&2
    exit 1
  fi
  if grep -Eq '^$|^[[:space:]]|[[:space:]]$' "$template"; then
    echo "expectation template $template has a blank or space-padded line" >&2
    exit 1
  fi
  count=$((count + 1))
done < <(python3 ./scripts/scenario-manifest.py expectations)
(( count > 0 )) || { echo "no expectation templates listed by the scenario manifest" >&2; exit 1; }
echo "Expectation templates render for all $count boot-runner scenarios"
