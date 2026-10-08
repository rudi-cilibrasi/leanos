#!/usr/bin/env bash
# Hosted post-state replay (#476): Lake-generated C of LeanOS.PostStateProjection
# and its import closure, linked with the Lean runtime, against the corpus that
# `lake exe leanos-poststate` evaluates in Lean. The ordinary run also builds
# two controlled fixtures (an unscrubbed reallocation and a stale generation),
# each of which must fail with its named projection mismatch.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
id="${LEANOS_HOSTED_BOUNDARY_ID:-poststate}"
manifest=scripts/hosted-generated-boundaries.tsv
row="$(awk -F '\t' -v id="$id" '$1 == id { print; found=1 } END { exit !found }' "$manifest")" || {
  echo "error: hosted boundary '$id' is absent from $manifest" >&2
  exit 1
}
IFS=$'\t' read -r _ _ harness generation target modules exports assertion <<<"$row"
source scripts/hosted-boundary-coverage.sh
source scripts/hosted-sanitizer-config.sh
[[ "$generation" == lake-ir ]] || {
  echo "error: $id is not a lake-ir hosted boundary" >&2
  exit 1
}

if [[ "$mode" == sanitized ]]; then
  leanos_assert_pinned_toolchain
  build="build/${id}-host-sanitized"
  cc_command="$leanos_host_cc"
  cflags=("${leanos_host_sanitizer_flags[@]}" -finstrument-functions)
  run=(leanos_run_sanitized)
elif [[ "$mode" == ordinary ]]; then
  build="build/${id}-host"
  cc_command="${LEANOS_HOST_CC:-cc}"
  cflags=(-O2 -ffunction-sections -fdata-sections -finstrument-functions)
  run=()
else
  echo "usage: $0 [ordinary|sanitized]" >&2
  exit 2
fi

rm -rf "$build"
mkdir -p "$build"
leanos_prepare_boundary_coverage "$build" "$exports"
lake build "$target" leanos-poststate
prefix="$(lake env lean --print-prefix)"
generated="build/boundary-abi"
./scripts/generate-oracle.sh "$generated"
lake exe leanos-poststate >"$build/poststate.tsv"
awk -f scripts/render-poststate-header.awk "$build/poststate.tsv" >"$build/poststate.h"

# The root module imports the composite dispatcher, so its initializer calls
# every module in the import closure; compile the whole closure.
IFS=',' read -ra module_names <<<"$modules"
mapfile -t compiled_modules < <(leanos_project_module_closure "${module_names[@]}")
objects=()
for module in "${compiled_modules[@]}"; do
  source=".lake/build/ir/LeanOS/$module.c"
  object_name="${module//\//_}"
  [[ -f "$source" ]] || {
    echo "error: generated module inventory is missing $source" >&2
    exit 1
  }
  "$cc_command" -std=c11 "${cflags[@]}" -I"$prefix/include" \
    -c "$source" -o "$build/$object_name.o"
  if [[ "$mode" == sanitized ]]; then
    leanos_require_sanitized_object "$build/$object_name.o"
  fi
  objects+=("$build/$object_name.o")
done
"$cc_command" -std=c11 -Wall -Wextra -Werror \
  -c "$build/boundary-coverage.c" -o "$build/boundary-coverage.o"

link_host() {
  local output="$1"
  shift
  "$cc_command" -std=c11 -Wall -Wextra -Werror -I"$prefix/include" \
    -I"$generated" -I"$build" "${cflags[@]}" "$@" -c "$harness" -o "$output.o"
  if [[ "$mode" == sanitized ]]; then
    leanos_link_sanitized_host "$output" "$output.o" \
      "$build/boundary-coverage.o" "${objects[@]}"
  else
    lake env leanc -Wl,--gc-sections "${cflags[@]}" \
      "$output.o" "$build/boundary-coverage.o" "${objects[@]}" -o "$output"
  fi
}

link_host "$build/host"
LEANOS_BOUNDARY_COVERAGE_FILE="$build/boundary-coverage.actual" \
  "${run[@]}" "$build/host" >"$build/results.txt"
leanos_check_boundary_coverage "$build"
expected_lines="${assertion#lines=}"
[[ "$assertion" == lines=* && \
    "$(grep -c '^POSTSTATE/' "$build/results.txt")" -eq "$expected_lines" ]] &&
  grep -Fxq 'Hosted generated-C post-state projection replay passed' "$build/results.txt" || {
  echo "error: hosted $id replay did not produce $expected_lines passing projections" >&2
  exit 1
}

if [[ "$mode" == sanitized ]]; then
  ordinary="build/${id}-host/results.txt"
  [[ -f "$ordinary" ]] || {
    echo "error: ordinary $id results are required before sanitized replay" >&2
    exit 1
  }
  cmp -s "$ordinary" "$build/results.txt" || {
    echo "error: sanitized $id replay diverged from the ordinary replay" >&2
    diff "$ordinary" "$build/results.txt" | head -n 4 >&2
    exit 1
  }
else
  fixtures=(
    "unscrubbed-reallocation:LEANOS_FIXTURE_POSTSTATE_UNSCRUBBED_REALLOCATION:operation=frame-scrub.b-fresh.frame-100-republished-zero field=projection"
    "stale-generation:LEANOS_FIXTURE_POSTSTATE_STALE_GENERATION:operation=mixed-row.capability-copied.subject-2-slot-3 field=projection"
  )
  for fixture in "${fixtures[@]}"; do
    IFS=: read -r name define diagnostic <<<"$fixture"
    link_host "$build/host-$name" "-D$define"
    if LEANOS_BOUNDARY_COVERAGE_FILE="$build/boundary-coverage-$name.actual" \
        "$build/host-$name" >"$build/host-$name.txt" 2>&1; then
      echo "error: post-state fixture '$name' unexpectedly passed" >&2
      exit 1
    fi
    grep -Fq "$diagnostic" "$build/host-$name.txt" || {
      echo "error: post-state fixture '$name' lacked '$diagnostic'" >&2
      cat "$build/host-$name.txt" >&2
      exit 1
    }
    echo "post-state fixture $name failed as expected: $diagnostic"
  done
fi
echo "Hosted generated-C $id $mode replay passed"
