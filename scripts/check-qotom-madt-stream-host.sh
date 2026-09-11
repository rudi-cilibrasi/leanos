#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-both}"
case "$mode" in ordinary|sanitized|both) ;; *) echo 'usage: check-qotom-madt-stream-host.sh [ordinary|sanitized|both]' >&2; exit 2;; esac
source scripts/hosted-boundary-coverage.sh
source scripts/hosted-sanitizer-config.sh
if [[ "$mode" != ordinary ]]; then leanos_assert_pinned_toolchain; fi
python3 scripts/test-qotom-madt-stream.py
python3 scripts/test-qotom-madt-finish.py
bash scripts/check-qotom-madt-stream-object.sh
bash scripts/generate-oracle.sh build/boundary-abi
corpus=build/qotom-madt-stream
prefix="$(lean --print-prefix)"
exports="$(awk -F '\t' '$1 == "qotom-madt-stream" { print $7; found=1 } END { exit !found }' scripts/hosted-generated-boundaries.tsv)"
modes=("$mode")
if [[ "$mode" == both ]]; then modes=(ordinary sanitized); fi
for current in "${modes[@]}"; do
  build="build/qotom-madt-stream-host-$current"
  mkdir -p "$build"
  leanos_prepare_boundary_coverage "$build" "$exports"
  cc_command="${LEANOS_HOST_CC:-cc}"
  flags=(-O2 -ffunction-sections -fdata-sections -finstrument-functions -fno-pie)
  run=()
  if [[ "$current" == sanitized ]]; then
    cc_command="$leanos_host_cc"
    flags=("${leanos_host_sanitizer_flags[@]}" -finstrument-functions -fno-pie)
    run=(leanos_run_sanitized)
  fi
  "$cc_command" "${flags[@]}" -I"$prefix/include" \
    -c "$corpus/QotomMadtStream.c" -o "$build/generated.o"
  if [[ "$current" == sanitized ]]; then
    leanos_require_sanitized_object "$build/generated.o"
  fi
  "$cc_command" "${flags[@]}" -Wall -Wextra -Werror -I"$corpus" -Ibuild/boundary-abi -I"$prefix/include" \
    -c tests/qotom-madt-stream-host.c -o "$build/host.o"
  "$cc_command" -fno-pie -c "$build/boundary-coverage.c" -o "$build/coverage.o"
  "$cc_command" "${flags[@]}" -no-pie -Wl,--gc-sections \
    "$build/generated.o" "$build/host.o" "$build/coverage.o" -o "$build/host"
  LEANOS_BOUNDARY_COVERAGE_FILE="$build/boundary-coverage.actual" \
    "${run[@]}" "$build/host" > "$build/results.txt"
  leanos_check_boundary_coverage "$build"
  if [[ "$current" == sanitized ]]; then
    cmp build/qotom-madt-stream-host-ordinary/results.txt "$build/results.txt"
  fi
done
printf '%s\n' "PASS generated-C $mode scalar MADT replay and export coverage"
