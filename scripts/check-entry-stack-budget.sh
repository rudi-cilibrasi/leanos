#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

report_dir="${LEANOS_STACK_USAGE_DIR:-build/boot}"
manifest="${LEANOS_ENTRY_STACK_MANIFEST:-scripts/entry-stack-callgraph.tsv}"
usable_bytes="${LEANOS_ENTRY_STACK_USABLE_BYTES:-16384}"
assembly_source="${LEANOS_ENTRY_ASSEMBLY_SOURCE:-boot/boot.S}"
elf="${1:-}"
elf_edges_output="${LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT:-}"

[[ "$usable_bytes" =~ ^[0-9]+$ && "$usable_bytes" -gt 0 ]] || {
  echo "error: entry-stack usable byte budget must be a positive integer" >&2; exit 1;
}
[[ -f "$manifest" ]] || { echo "error: missing entry-stack call graph '$manifest'" >&2; exit 1; }
[[ -f "$assembly_source" ]] || {
  echo "error: missing entry-stack assembly source '$assembly_source'" >&2; exit 1;
}
save_body="$(awk '/^[.]macro SAVE$/ { inside = 1; next } inside && /^[.]endm$/ { exit } inside' \
  "$assembly_source")"
save_count="$(grep -Eo '\bpush(q)?\b' <<<"$save_body" | wc -l)"
[[ "$save_count" -eq 15 ]] || {
  echo "error: assembly-save-register-count=$save_count expected=15" >&2; exit 1;
}
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
while IFS=$'\t' read -r path origin hardware_error safety elf_root functions extra; do
  [[ -n "$path" && "${path:0:1}" != '#' ]] || continue
  [[ -z "${extra:-}" && ( "$origin" == user || "$origin" == kernel ) && \
     ( "$hardware_error" == 0 || "$hardware_error" == 1 ) && "$safety" =~ ^[0-9]+$ && \
     "$elf_root" =~ ^[A-Za-z_][A-Za-z0-9_.]*$ ]] || {
    echo "error: path=$path malformed entry-stack manifest row" >&2; exit 1;
  }
  hardware_frame=24
  [[ "$origin" == user ]] && hardware_frame=40
  error_bytes=$((hardware_error * 8))
  normalization_bytes=16
  [[ "$hardware_error" == 1 ]] && normalization_bytes=8
  prefix=$((hardware_frame + error_bytes + save_count * 8 + normalization_bytes))
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

[[ -n "$elf" ]] || exit 0
[[ -f "$elf" ]] || { echo "error: missing final entry-stack ELF '$elf'" >&2; exit 1; }
command -v nm >/dev/null 2>&1 || { echo "error: missing required tool 'nm'" >&2; exit 1; }
command -v objdump >/dev/null 2>&1 || { echo "error: missing required tool 'objdump'" >&2; exit 1; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
nm -n "$elf" | awk 'NF >= 3 { print $3 }' | sort -u >"$tmp/symbols"
objdump -d --no-show-raw-insn "$elf" | awk \
    -v indirect="$tmp/indirect" -v pushes="$tmp/pushes" '
  /^[[:xdigit:]]+[[:space:]]+<[^>]+>:/ {
    caller = $2; gsub(/[<>:]/, "", caller); next
  }
  caller != "" && $2 ~ /^push(q)?$/ { count[caller]++ }
  caller != "" && $2 ~ /^(callq?|jmpq?)$/ {
    target = $NF
    if (target ~ /^<[^>]+>$/) {
      gsub(/[<>]/, "", target); sub(/\+0x.*/, "", target)
      # Ignore jumps to a local basic block in the same symbol, but retain a
      # direct self-call: the former is ordinary control flow and the latter
      # is recursion that invalidates finite stack accounting.
      if (caller != target || $2 ~ /^callq?$/) print caller "\t" target
    } else if ($3 ~ /^\*/) {
      print caller "\t" $2 "\t" $3 >> indirect
    }
  }
  END { for (function_name in count) print function_name "\t" count[function_name] > pushes }
' | sort -u >"$tmp/edges"
touch "$tmp/indirect"
touch "$tmp/pushes"
if [[ -n "$elf_edges_output" ]]; then
  cp "$tmp/edges" "$elf_edges_output"
fi

while IFS=$'\t' read -r path _origin _hardware_error _safety elf_root functions _extra; do
  [[ -n "$path" && "${path:0:1}" != '#' ]] || continue
  grep -Fxq "$elf_root" "$tmp/symbols" || {
    echo "error: path=$path final-elf-missing-root=$elf_root" >&2; exit 1;
  }
  elf_save_count="$(awk -F '\t' -v root="$elf_root" \
    '$1 == root { print $2; found = 1 } END { if (!found) print 0 }' "$tmp/pushes")"
  [[ "$elf_save_count" -eq "$save_count" ]] || {
    echo "error: path=$path final-elf-save-register-count=$elf_save_count expected=$save_count root=$elf_root" >&2
    exit 1
  }
  printf '%s\n' "$elf_root" >"$tmp/reachable"
  : >"$tmp/reachable.next"
  while :; do
    before="$(wc -l <"$tmp/reachable")"
    awk 'NR == FNR { reached[$1] = 1; next }
         reached[$1] { print $2 }' "$tmp/reachable" "$tmp/edges" \
      >>"$tmp/reachable.next"
    cat "$tmp/reachable" "$tmp/reachable.next" | sort -u >"$tmp/reachable.new"
    mv "$tmp/reachable.new" "$tmp/reachable"
    : >"$tmp/reachable.next"
    [[ "$(wc -l <"$tmp/reachable")" -eq "$before" ]] && break
  done
  cycle_node="$(awk -F '\t' '
    function visit(node, count, child_index, target, children) {
      state[node] = 1
      count = split(outgoing[node], children, "\034")
      for (child_index = 1; child_index <= count; child_index++) {
        target = children[child_index]
        if (target == "") continue
        if (state[target] == 1) { cycle = target; return 1 }
        if (state[target] == 0 && visit(target)) return 1
      }
      state[node] = 2
      return 0
    }
    NR == FNR { reached[$1] = 1; next }
    ($1 in reached) && ($2 in reached) {
      outgoing[$1] = outgoing[$1] "\034" $2
    }
    END {
      for (node in reached) {
        if (state[node] == 0 && visit(node)) { print cycle; exit }
      }
    }
  ' "$tmp/reachable" "$tmp/edges")"
  [[ -z "$cycle_node" ]] || {
    echo "error: path=$path final-elf-recursion-cycle=$cycle_node root=$elf_root" >&2
    exit 1
  }
  IFS=';' read -ra chain <<<"$functions"
  declare -A reviewed=()
  reviewed[$elf_root]=1
  for function_name in "${chain[@]}"; do
    reviewed[$function_name]=1
  done
  while IFS=$'\t' read -r function_name instruction operand; do
    echo "error: path=$path final-elf-indirect-edge=$function_name:$instruction $operand" >&2
    exit 1
  done < <(awk -F '\t' 'NR == FNR { reached[$1] = 1; next }
      reached[$1] { print }' "$tmp/reachable" "$tmp/indirect")
  while IFS= read -r function_name; do
    if [[ -n "${usage[$function_name]+set}" && -z "${reviewed[$function_name]+set}" ]]; then
      echo "error: path=$path final-elf-unreviewed-stack-usage=$function_name" >&2
      exit 1
    fi
  done <"$tmp/reachable"
  for function_name in "$elf_root" "${chain[@]}"; do
    grep -Fxq "$function_name" "$tmp/symbols" || {
      echo "error: path=$path final-elf-missing-function=$function_name" >&2; exit 1;
    }
    grep -Fxq "$function_name" "$tmp/reachable" || {
      echo "error: path=$path final-elf-unreachable-function=$function_name root=$elf_root" >&2
      exit 1
    }
  done
  printf 'path=%s final-elf-root=%s save-register-pushes=%s reviewed-functions=%s reachable-functions=%s extracted-edges=%s result=PASS\n' \
    "$path" "$elf_root" "$elf_save_count" "${#chain[@]}" "$(wc -l <"$tmp/reachable")" \
    "$(wc -l <"$tmp/edges")"
done < "$manifest"
