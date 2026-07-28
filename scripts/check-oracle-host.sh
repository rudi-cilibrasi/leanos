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
IFS=$'\t' read -r _ _ harness generation _ modules exports assertion <<<"$row"
[[ "$id" == oracle && "$generation" == direct ]] || {
  echo "error: $id is not the direct oracle boundary" >&2
  exit 1
}
source scripts/hosted-sanitizer-config.sh
source scripts/hosted-boundary-coverage.sh

if [[ "$mode" == sanitized ]]; then
  build=build/oracle-sanitized
  cc_command="$leanos_host_cc"
  cflags=("${leanos_host_sanitizer_flags[@]}" -finstrument-functions)
  run=(leanos_run_sanitized)
elif [[ "$mode" == ordinary ]]; then
  build=build/oracle
  cc_command="${LEANOS_HOST_CC:-cc}"
  cflags=(-ffunction-sections -fdata-sections -finstrument-functions)
  run=()
else
  echo "usage: $0 [ordinary|sanitized]" >&2
  exit 2
fi

rm -rf "$build"
mkdir -p "$build"
leanos_prepare_boundary_coverage "$build" "$exports"
./scripts/generate-oracle.sh "$build"
prefix="$(lake env lean --print-prefix)"
generated=build/hosted-generated-sources/oracle
objects=()
generated_sources=()
root_modules=()
declare -A root_module_set=()
IFS=',' read -ra module_specs <<<"$modules"
for spec in "${module_specs[@]}"; do
  module="${spec%%=*}"
  source="${spec#*=}"
  [[ "$module" != "$source" && -f "$source" ]] || {
    echo "error: invalid direct generated-module inventory '$spec'" >&2
    exit 1
  }
  root_modules+=("$module")
  root_module_set["$module"]=1
done
if [[ "$mode" == ordinary ]]; then
  rm -rf "$generated"
  mkdir -p "$generated"
else
  leanos_assert_pinned_toolchain
  [[ -d "$generated" ]] || {
    echo "error: ordinary replay must generate $generated first" >&2
    exit 1
  }
fi
for module in "${root_modules[@]}"; do
  object_name="${module//\//_}"
  generated_source="$generated/$object_name.c"
  source="LeanOS/$module.lean"
  if [[ "$mode" == ordinary ]]; then
    lake env lean --c="$generated_source" "$source"
  elif [[ ! -f "$generated_source" ]]; then
    echo "error: ordinary replay did not generate $generated_source" >&2
    exit 1
  fi
  generated_sources+=("$generated_source")
done
source_hashes="$generated/SHA256SUMS"
if [[ "$mode" == ordinary ]]; then
  sha256sum "${generated_sources[@]}" >"$source_hashes"
else
  [[ -f "$source_hashes" ]] || {
    echo "error: ordinary replay did not record $source_hashes" >&2
    exit 1
  }
  sha256sum --check --status "$source_hashes" || {
    echo "error: direct-generated oracle sources changed after ordinary replay" >&2
    exit 1
  }
fi
for module in "${root_modules[@]}"; do
  object_name="${module//\//_}"
  generated_source="$generated/$object_name.c"
  "$cc_command" -std=c11 -I"$prefix/include" -I"$build" "${cflags[@]}" \
    -c "$generated_source" -o "$build/$object_name.o"
  if [[ "$mode" == sanitized ]]; then
    leanos_require_sanitized_object "$build/$object_name.o"
  fi
  objects+=("$build/$object_name.o")
done
if [[ "$mode" == sanitized ]]; then
  # The direct-generated root files above are the exact production oracle
  # sources used by the ordinary replay. Their retained initialization
  # sections reference imported module symbols that ordinary --gc-sections
  # discards, so provide only those transitive dependencies from Lake's IR.
  # Package-scoped copies of root modules are also needed because roots import
  # one another under the package prefix. Rename only their duplicate public
  # definitions so calls from the harness still select the exact direct files.
  direct_symbols="$build/direct-defined-symbols.txt"
  nm -g --defined-only "${objects[@]}" |
    awk 'NF >= 3 { print $3 }' | sort -u >"$direct_symbols"
  mapfile -t dependency_modules < <(
    leanos_project_module_closure "${root_modules[@]}"
  )
  for module in "${dependency_modules[@]}"; do
    object_name="${module//\//_}"
    dependency_source=".lake/build/ir/LeanOS/$module.c"
    [[ -f "$dependency_source" ]] || {
      echo "error: generated dependency inventory is missing $dependency_source" >&2
      exit 1
    }
    "$cc_command" -std=c11 -I"$prefix/include" -I"$build" "${cflags[@]}" \
      -c "$dependency_source" -o "$build/dependency_$object_name.o"
    leanos_require_sanitized_object "$build/dependency_$object_name.o"
    if [[ -n "${root_module_set[$module]+x}" ]]; then
      redefine="$build/dependency_$object_name.redefine"
      comm -12 "$direct_symbols" <(
        nm -g --defined-only "$build/dependency_$object_name.o" |
          awk 'NF >= 3 { print $3 }' | sort -u
      ) | while IFS= read -r symbol; do
        printf '%s %s\n' "$symbol" \
          "__leanos_dependency_${object_name}_${symbol}"
      done >"$redefine"
      if [[ -s "$redefine" ]]; then
        objcopy --redefine-syms="$redefine" \
          "$build/dependency_$object_name.o"
      fi
    fi
    objects+=("$build/dependency_$object_name.o")
  done
fi
"$cc_command" -std=c11 -Wall -Wextra -Werror -I"$build" -Iinclude "${cflags[@]}" \
  -c "$harness" -o "$build/host.o"
"$cc_command" -std=c11 -Wall -Wextra -Werror \
  -c "$build/boundary-coverage.c" -o "$build/boundary-coverage.o"
if [[ "$mode" == sanitized ]]; then
  # ASan registers generated globals and therefore retains initialization
  # sections that the ordinary allocation-free replay garbage-collects. Link
  # the hosted sanitizer replay against the pinned Lean runtime.
  leanos_link_sanitized_host "$build/host" "$build/host.o" \
    "$build/boundary-coverage.o" "${objects[@]}"
else
  "$cc_command" -Wl,--gc-sections "${cflags[@]}" \
    "$build/host.o" "$build/boundary-coverage.o" "${objects[@]}" -o "$build/host"
fi
LEANOS_BOUNDARY_COVERAGE_FILE="$build/boundary-coverage.actual" \
  "${run[@]}" "$build/host" >"$build/host-results.txt"
leanos_check_boundary_coverage "$build"
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
else
  compile_fixture() {
    local name="$1"
    local define="$2"
    "$cc_command" -std=c11 -Wall -Wextra -Werror -I"$build" -Iinclude \
      "${cflags[@]}" "-D$define" -c "$harness" -o "$build/host-$name.o"
    "$cc_command" -Wl,--gc-sections "${cflags[@]}" "$build/host-$name.o" \
      "$build/boundary-coverage.o" "${objects[@]}" -o "$build/host-$name"
  }
  fixtures=(
    "truncated:LEANOS_FIXTURE_COMPOSITE_TRUNCATED:oracle malformed arity"
    "output-corruption:LEANOS_FIXTURE_COMPOSITE_OUTPUT_CORRUPTION:oracle mismatch"
    "old-stateless:LEANOS_FIXTURE_COMPOSITE_OLD_STATELESS:oracle mismatch"
    "wrong-version:LEANOS_FIXTURE_COMPOSITE_WRONG_VERSION:field=reply"
    "reserved-bits:LEANOS_FIXTURE_COMPOSITE_RESERVED_BITS:field=reply"
    "stale-replay:LEANOS_FIXTURE_COMPOSITE_STALE_REPLAY:field=reply"
    "forged-context:LEANOS_FIXTURE_COMPOSITE_FORGED_CONTEXT:field=reply"
    "handle-corruption:LEANOS_FIXTURE_COMPOSITE_HANDLE_CORRUPTION:field=reply"
  )
  : >"$build/negative-fixtures.tsv"
  for fixture in "${fixtures[@]}"; do
    IFS=: read -r name define diagnostic <<<"$fixture"
    compile_fixture "$name" "$define"
    if "$build/host-$name" >"$build/host-$name.txt" 2>&1; then
      echo "error: composite oracle fixture '$name' unexpectedly passed" >&2
      exit 1
    fi
    grep -q "$diagnostic" "$build/host-$name.txt" || {
      echo "error: composite oracle fixture '$name' lacked '$diagnostic'" >&2
      exit 1
    }
    printf '%s\t%s\t%s\n' "$name" "$define" "$diagnostic" \
      >>"$build/negative-fixtures.tsv"
  done
  {
    printf 'schema\tleanos-oracle-evidence-v1\n'
    printf 'source_revision\t%s\n' "$(git rev-parse HEAD)"
    printf 'generated_c_flags\t%s\n' \
      "-std=c11 -I<lean-prefix>/include -Ibuild/oracle -ffunction-sections -fdata-sections"
    printf 'host_c_flags\t%s\n' \
      "-std=c11 -Wall -Wextra -Werror -Ibuild/oracle -Iinclude"
    printf 'link_flags\t%s\n' "-Wl,--gc-sections"
    printf 'lean_version\t%s\n' "$(lake env lean --version | head -n 1)"
    printf 'cc_version\t%s\n' "$("$cc_command" --version | head -n 1)"
  } >"$build/toolchain-and-flags.tsv"
  {
    printf 'schema\tleanos-oracle-manifest-v1\n'
    printf 'source_revision\t%s\n' "$(git rev-parse HEAD)"
    sha256sum \
      LeanOS/CompositeDispatcher.lean \
      "$generated/CompositeDispatcher.c" \
      include/leanos/composite-dispatcher.h \
      "$build/corpus.tsv" \
      "$build/host-results.txt" \
      "$build/negative-fixtures.tsv" \
      "$build/toolchain-and-flags.tsv"
  } >"$build/manifest.tsv"
fi
echo "Hosted generated-code oracle $mode replay passed ($expected_lines vectors)"
