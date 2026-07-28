#!/usr/bin/env bash

# This file is sourced by the hosted generated-boundary runners. Keep the
# configuration literal so local runs and CI exercise the same instrumentation.
leanos_host_cc="${LEANOS_HOST_CC:-gcc}"
leanos_host_sanitizer_flags=(
  -O1
  -g3
  -fno-omit-frame-pointer
  -fno-optimize-sibling-calls
  -ffunction-sections
  -fdata-sections
  -frecord-gcc-switches
  -fsanitize=address,undefined
  -fsanitize-address-use-after-scope
  -fno-sanitize-recover=all
)
leanos_host_asan_options="abort_on_error=1:detect_leaks=0:halt_on_error=1:symbolize=1"
leanos_host_ubsan_options="halt_on_error=1:print_stacktrace=1"

leanos_require_sanitized_object() {
  local object="$1"
  local switches
  switches="$(readelf --string-dump=.GCC.command.line "$object" 2>/dev/null)" || {
    echo "error: generated object lacks recorded compiler switches: $object" >&2
    return 1
  }
  grep -Fq -- '-fsanitize=address,undefined' <<<"$switches" || {
    echo "error: generated object was compiled without pinned sanitizers: $object" >&2
    return 1
  }
  grep -Fq -- '-fno-sanitize-recover=all' <<<"$switches" || {
    echo "error: generated object permits sanitizer recovery: $object" >&2
    return 1
  }
}

leanos_run_sanitized() {
  ASAN_OPTIONS="$leanos_host_asan_options" \
    UBSAN_OPTIONS="$leanos_host_ubsan_options" "$@"
}

# Print the transitive project-module closure for the supplied root module
# names. Lean's dependency output is authoritative for imports; toolchain
# modules are provided by the hosted Lean runtime and are intentionally omitted.
leanos_project_module_closure() {
  local -a queue=("$@")
  local index=0
  local module source dependency
  declare -A seen=()
  while ((index < ${#queue[@]})); do
    module="${queue[$index]}"
    index=$((index + 1))
    [[ -z "${seen[$module]+x}" ]] || continue
    seen["$module"]=1
    source="LeanOS/$module.lean"
    [[ -f "$source" ]] || {
      echo "error: generated dependency has no project source: $module" >&2
      return 1
    }
    printf '%s\n' "$module"
    while IFS= read -r dependency; do
      dependency="${dependency#*/.lake/build/lib/lean/LeanOS/}"
      dependency="${dependency%.olean}"
      [[ "$dependency" != *"/.lake/build/lib/lean/LeanOS/"* ]] || continue
      queue+=("$dependency")
    done < <(
      lake env lean --deps "$source" |
        sed -n 's#^.*/\.lake/build/lib/lean/LeanOS/\(.*\)\.olean$#\1#p'
    )
  done
}

leanos_link_sanitized_host() {
  local output="$1"
  shift
  local asan_runtime ubsan_runtime
  asan_runtime="$("$leanos_host_cc" -print-file-name=libasan.so)"
  ubsan_runtime="$("$leanos_host_cc" -print-file-name=libubsan.so)"
  [[ -f "$asan_runtime" && -f "$ubsan_runtime" ]] || {
    echo "error: pinned compiler sanitizer runtime is unavailable" >&2
    return 1
  }
  lake env leanc -Wl,--gc-sections "$@" \
    "$asan_runtime" "$ubsan_runtime" -o "$output"
}
