#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
source scripts/hosted-boundary-harness-scan.sh

fixture="$(mktemp -d)"
trap 'rm -r -- "$fixture"' EXIT
positive="$fixture/early-call.c"
declarations_only="$fixture/declarations-only.c"

{
  printf 'extern void leanos_fixture_export(void);\n'
  printf 'void invoke_fixture(void) { leanos_fixture_export(); }\n'
  for ((line = 0; line < 8192; line++)); do
    printf 'static const unsigned char padding_%04d = %d;\n' \
      "$line" "$((line % 256))"
  done
} >"$positive"

{
  printf 'extern void leanos_fixture_export(void);\n'
  for ((line = 0; line < 8192; line++)); do
    printf 'static const unsigned char padding_%04d = %d;\n' \
      "$line" "$((line % 256))"
  done
} >"$declarations_only"

leanos_harness_calls_export "$positive" leanos_fixture_export || {
  echo "error: large harness with an early export call was rejected" >&2
  exit 1
}
if leanos_harness_calls_export "$declarations_only" leanos_fixture_export; then
  echo "error: declarations-only harness was accepted as export coverage" >&2
  exit 1
fi

echo "Hosted boundary harness scan fixtures passed"
