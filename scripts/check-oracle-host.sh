#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
id="${LEANOS_HOSTED_BOUNDARY_ID:-oracle}"
manifest=scripts/hosted-generated-boundaries.tsv
row="$(awk -F '\t' -v id="$id" '$1 == id { print; found=1 } END { exit !found }' "$manifest")" || {
  echo "error: hosted boundary '$id' is absent from $manifest" >&2
  exit 1
}
IFS=$'\t' read -r _ _ harness generation _ modules assertion <<<"$row"
[[ "$id" == oracle && "$generation" == direct ]] || {
  echo "error: $id is not the direct oracle boundary" >&2
  exit 1
}

if [[ "$mode" == sanitized ]]; then
  source scripts/hosted-sanitizer-config.sh
  build=build/oracle-sanitized
  cc_command="$leanos_host_cc"
  cflags=("${leanos_host_sanitizer_flags[@]}")
  run=(leanos_run_sanitized)
elif [[ "$mode" == ordinary ]]; then
  build=build/oracle
  cc_command="${LEANOS_HOST_CC:-cc}"
  cflags=(-ffunction-sections -fdata-sections)
  run=()
else
  echo "usage: $0 [ordinary|sanitized]" >&2
  exit 2
fi

rm -rf "$build"
mkdir -p "$build"
./scripts/generate-oracle.sh "$build"
prefix="$(lake env lean --print-prefix)"
objects=()
root_modules=()
IFS=',' read -ra module_specs <<<"$modules"
for spec in "${module_specs[@]}"; do
  module="${spec%%=*}"
  source="${spec#*=}"
  [[ "$module" != "$source" && -f "$source" ]] || {
    echo "error: invalid direct generated-module inventory '$spec'" >&2
    exit 1
  }
  root_modules+=("$module")
  if [[ "$mode" == ordinary ]]; then
    lake env lean --c="$build/$module.c" "$source"
    "$cc_command" -std=c11 -I"$prefix/include" -I"$build" "${cflags[@]}" \
      -c "$build/$module.c" -o "$build/$module.o"
    objects+=("$build/$module.o")
  fi
done
if [[ "$mode" == sanitized ]]; then
  while IFS= read -r module; do
    source=".lake/build/ir/LeanOS/$module.c"
    object_name="${module//\//_}"
    [[ -f "$source" ]] || {
      echo "error: generated dependency inventory is missing $source" >&2
      exit 1
    }
    "$cc_command" -std=c11 -I"$prefix/include" -I"$build" "${cflags[@]}" \
      -c "$source" -o "$build/$object_name.o"
    leanos_require_sanitized_object "$build/$object_name.o"
    objects+=("$build/$object_name.o")
  done < <(leanos_project_module_closure "${root_modules[@]}")
fi
"$cc_command" -std=c11 -Wall -Wextra -Werror -I"$build" "${cflags[@]}" \
  -c "$harness" -o "$build/host.o"
if [[ "$mode" == sanitized ]]; then
  # ASan registers generated globals and therefore retains initialization
  # sections that the ordinary allocation-free replay garbage-collects. Link
  # the hosted sanitizer replay against the pinned Lean runtime.
  leanos_link_sanitized_host "$build/host" "$build/host.o" "${objects[@]}"
else
  "$cc_command" -Wl,--gc-sections "${cflags[@]}" \
    "$build/host.o" "${objects[@]}" -o "$build/host"
fi
"${run[@]}" "$build/host" >"$build/host-results.txt"
expected_lines="${assertion#lines=}"
[[ "$assertion" == lines=* && \
    "$(wc -l < "$build/host-results.txt")" -eq "$expected_lines" ]] || {
  echo "error: hosted oracle did not produce $expected_lines per-vector results" >&2
  exit 1
}
if [[ "$mode" == sanitized ]]; then
  ordinary=build/oracle/host-results.txt
  [[ -f "$ordinary" ]] || {
    echo "error: ordinary oracle results are required before sanitized replay" >&2
    exit 1
  }
  if ! cmp -s "$ordinary" "$build/host-results.txt"; then
    first="$(
      paste "$ordinary" "$build/host-results.txt" |
        awk -F '\t' '$1 != $2 { print NR; exit }'
    )"
    echo "error: oracle replay first diverged at vector $first" >&2
    sed -n "${first}p" "$ordinary" | sed 's/^/ordinary: /' >&2
    sed -n "${first}p" "$build/host-results.txt" |
      sed 's/^/sanitized: /' >&2
    exit 1
  fi
fi
echo "Hosted generated-code oracle $mode replay passed ($expected_lines vectors)"
