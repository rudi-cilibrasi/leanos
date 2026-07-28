#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
id="${LEANOS_HOSTED_BOUNDARY_ID:-boot-handoff}"
manifest=scripts/hosted-generated-boundaries.tsv
row="$(awk -F '\t' -v id="$id" '$1 == id { print; found=1 } END { exit !found }' "$manifest")" || {
  echo "error: hosted boundary '$id' is absent from $manifest" >&2
  exit 1
}
IFS=$'\t' read -r _ _ harness generation target modules exports assertion <<<"$row"
source scripts/hosted-boundary-coverage.sh
[[ "$id" == boot-handoff && "$generation" == lake-ir ]] || {
  echo "error: $id is not the lake-ir boot-handoff boundary" >&2
  exit 1
}

if [[ "$mode" == sanitized ]]; then
  source scripts/hosted-sanitizer-config.sh
  leanos_assert_pinned_toolchain
  build=build/boot-handoff-host-sanitized
  cc_command="$leanos_host_cc"
  cflags=("${leanos_host_sanitizer_flags[@]}" -finstrument-functions)
  run=(leanos_run_sanitized)
elif [[ "$mode" == ordinary ]]; then
  build=build/boot-handoff-host
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
lake build "$target"
prefix="$(lake env lean --print-prefix)"
objects=()
IFS=',' read -ra module_names <<<"$modules"
if [[ "$mode" == sanitized ]]; then
  mapfile -t compiled_modules < <(
    leanos_project_module_closure "${module_names[@]}"
  )
else
  compiled_modules=("${module_names[@]}")
fi
for module in "${compiled_modules[@]}"; do
  source=".lake/build/ir/LeanOS/$module.c"
  object_name="${module//\//_}"
  [[ -f "$source" ]] || {
    echo "error: generated module inventory is missing $source" >&2
    exit 1
  }
  if [[ "$mode" == sanitized ]]; then
    "$cc_command" -std=c11 "${cflags[@]}" -I"$prefix/include" \
      -c "$source" -o "$build/$object_name.o"
    leanos_require_sanitized_object "$build/$object_name.o"
  else
    lake env leanc "${cflags[@]}" -I"$prefix/include" \
      -c "$source" -o "$build/$object_name.o"
  fi
  objects+=("$build/$object_name.o")
done
"$cc_command" -std=c11 -Wall -Wextra -Werror -I"$prefix/include" \
  "${cflags[@]}" -c "$harness" -o "$build/host.o"
"$cc_command" -std=c11 -Wall -Wextra -Werror \
  -c "$build/boundary-coverage.c" -o "$build/boundary-coverage.o"
if [[ "$mode" == sanitized ]]; then
  leanos_link_sanitized_host "$build/host" "$build/host.o" \
    "$build/boundary-coverage.o" "${objects[@]}"
else
  lake env leanc -Wl,--gc-sections "${cflags[@]}" \
    "$build/host.o" "$build/boundary-coverage.o" "${objects[@]}" -o "$build/host"
fi
LEANOS_BOUNDARY_COVERAGE_FILE="$build/boundary-coverage.actual" \
  "${run[@]}" "$build/host" | tee "$build/results.txt"
leanos_check_boundary_coverage "$build"
expected="${assertion#contains=}"
expected="${expected//_/ }"
[[ "$assertion" == contains=* ]] && grep -Fq "$expected" "$build/results.txt" || {
  echo "error: hosted boot-handoff replay lacked '$expected'" >&2
  exit 1
}
if [[ "$mode" == sanitized ]]; then
  ordinary=build/boot-handoff-host/results.txt
  [[ -f "$ordinary" ]] || {
    echo "error: ordinary boot-handoff results are required before sanitized replay" >&2
    exit 1
  }
  if ! cmp -s "$ordinary" "$build/results.txt"; then
    first="$(
      paste "$ordinary" "$build/results.txt" |
        awk -F '\t' '$1 != $2 { print NR; exit }'
    )"
    field="$(sed -n "${first}p" "$ordinary" | awk '{print $2}')"
    echo "error: boot-handoff replay first diverged at field $field (row $first)" >&2
    sed -n "${first}p" "$ordinary" | sed 's/^/ordinary: /' >&2
    sed -n "${first}p" "$build/results.txt" |
      sed 's/^/sanitized: /' >&2
    exit 1
  fi
fi
echo "Hosted generated-C boot-handoff $mode replay passed"
