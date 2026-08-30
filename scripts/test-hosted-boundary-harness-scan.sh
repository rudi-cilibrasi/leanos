#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
source scripts/hosted-boundary-harness-scan.sh

fixture="$(mktemp -d)"
trap 'rm -r -- "$fixture"' EXIT
positive="$fixture/early-call.c"
declarations_only="$fixture/declarations-only.c"
generated_dispatch="$fixture/generated-dispatch.c"
oracle_source="$fixture/Oracle.lean"

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

{
  printf '#include "leanos/oracle-dispatch.h"\n'
  printf 'uint64_t invoke_fixture(const struct oracle_vector *v) { return leanos_oracle_dispatch(v); }\n'
} >"$generated_dispatch"
printf '  adapter "Fixture" 0 "leanos_fixture_export" 2,\n' >"$oracle_source"

leanos_harness_calls_export "$positive" leanos_fixture_export || {
  echo "error: large harness with an early export call was rejected" >&2
  exit 1
}
if leanos_harness_calls_export "$declarations_only" leanos_fixture_export; then
  echo "error: declarations-only harness was accepted as export coverage" >&2
  exit 1
fi
leanos_harness_dispatches_generated_oracle_export \
  "$generated_dispatch" leanos_fixture_export "$oracle_source" || {
    echo "error: generated oracle dispatch coverage was rejected" >&2
    exit 1
  }
if leanos_harness_dispatches_generated_oracle_export \
    "$generated_dispatch" leanos_other_export "$oracle_source"; then
  echo "error: generated oracle dispatch accepted an unmapped export" >&2
  exit 1
fi

echo "Hosted boundary harness scan fixtures passed"
