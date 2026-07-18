#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

report_dir="${LEANOS_STACK_USAGE_DIR:-build/boot}"
manifest="${LEANOS_ENTRY_STACK_MANIFEST:-scripts/entry-stack-callgraph.tsv}"
usable_bytes="${LEANOS_ENTRY_STACK_USABLE_BYTES:-16384}"

[[ "$usable_bytes" =~ ^[0-9]+$ && "$usable_bytes" -gt 0 ]] || {
  echo "error: entry-stack usable byte budget must be a positive integer" >&2; exit 1;
}
[[ -f "$manifest" ]] || { echo "error: missing entry-stack call graph '$manifest'" >&2; exit 1; }
mapfile -t reports < <(find "$report_dir" -maxdepth 1 -type f -name '*.su' -print | sort)
[[ ${#reports[@]} -gt 0 ]] || {
  echo "error: no compiler stack-usage reports in '$report_dir'" >&2; exit 1;
}

declare -A usage=()
declare -A usage_kind=()
while IFS=$'\t' read -r location bytes qualifier extra; do
  [[ -n "$location" ]] || continue
  function_name="${location##*:}"
  [[ "$bytes" =~ ^[0-9]+$ ]] || continue
  if [[ -n "${usage[$function_name]+set}" && "${usage[$function_name]}" != "$bytes" ]]; then
    echo "error: function=$function_name has variant stack usage ${usage[$function_name]} and $bytes" >&2
    exit 1
  fi
  usage[$function_name]="$bytes"
  usage_kind[$function_name]="${qualifier:-unknown}${extra:+,$extra}"
done < <(cat "${reports[@]}")

paths=0
while IFS=$'\t' read -r path prefix safety functions extra; do
  [[ -n "$path" && "${path:0:1}" != '#' ]] || continue
  [[ -z "${extra:-}" && "$prefix" =~ ^[0-9]+$ && "$safety" =~ ^[0-9]+$ ]] || {
    echo "error: path=$path malformed entry-stack manifest row" >&2; exit 1;
  }
  total=$((prefix + safety))
  IFS=';' read -ra chain <<<"$functions"
  [[ ${#chain[@]} -gt 0 ]] || { echo "error: path=$path has empty call graph" >&2; exit 1; }
  declare -A seen=()
  for function_name in "${chain[@]}"; do
    [[ "$function_name" =~ ^[A-Za-z_][A-Za-z0-9_.]*$ ]] || {
      echo "error: path=$path unresolved-indirect-edge=$function_name" >&2; exit 1;
    }
    [[ -z "${seen[$function_name]+set}" ]] || {
      echo "error: path=$path recursion=$function_name" >&2; exit 1;
    }
    seen[$function_name]=1
    [[ -n "${usage[$function_name]+set}" ]] || {
      echo "error: path=$path missing-stack-usage=$function_name" >&2; exit 1;
    }
    [[ "${usage_kind[$function_name]}" == static ]] || {
      echo "error: path=$path function=$function_name stack-usage=${usage_kind[$function_name]}" >&2
      exit 1
    }
    total=$((total + usage[$function_name]))
  done
  margin=$((usable_bytes - total))
  (( margin >= 0 )) || {
    echo "error: path=$path entry-stack over budget by $((-margin)) byte(s) total=$total usable=$usable_bytes" >&2
    exit 1
  }
  printf 'path=%s prefix=%s compiler=%s safety=%s total=%s usable=%s margin=%s\n' \
    "$path" "$prefix" "$((total - prefix - safety))" "$safety" "$total" "$usable_bytes" "$margin"
  paths=$((paths + 1))
done < "$manifest"
(( paths > 0 )) || { echo "error: entry-stack call graph has no paths" >&2; exit 1; }
