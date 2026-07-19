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
declare -A static_total=()
while IFS=$'\t' read -r location bytes qualifier extra; do
  [[ -n "$location" ]] || continue
  function_name="${location##*:}"
  [[ "$bytes" =~ ^[0-9]+$ ]] || continue
  if [[ -n "${usage[$function_name]+set}" && "${usage[$function_name]}" -gt "$bytes" ]]; then
    bytes="${usage[$function_name]}"
  fi
  usage[$function_name]="$bytes"
  report_kind="${qualifier:-unknown}${extra:+,$extra}"
  if [[ -n "${usage_kind[$function_name]+set}" &&
        "${usage_kind[$function_name]}" != "$report_kind" ]]; then
    usage_kind[$function_name]="variant"
  else
    usage_kind[$function_name]="$report_kind"
  fi
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
  static_total[$path]="$total"
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
    -v indirect="$tmp/indirect" -v pushes="$tmp/pushes" \
    -v assembly="$tmp/assembly" -v unsupported="$tmp/unsupported" \
    -v calls="$tmp/calls" '
  function unsigned_immediate(value, index_, digit, result) {
    if (value !~ /^0[xX]/) return value + 0
    result = 0
    value = tolower(substr(value, 3))
    for (index_ = 1; index_ <= length(value); index_++) {
      digit = index("0123456789abcdef", substr(value, index_, 1)) - 1
      if (digit < 0) return -1
      result = result * 16 + digit
    }
    return result
  }
  /^[[:xdigit:]]+[[:space:]]+<[^>]+>:/ {
    caller = $2; gsub(/[<>:]/, "", caller); present[caller] = 1; next
  }
  caller != "" && $2 ~ /^push/ { count[caller]++; allocation[caller] += 8 }
  caller != "" && $2 ~ /^sub(q)?$/ && $3 ~ /^\$(0[xX][[:xdigit:]]+|[0-9]+),%rsp$/ {
    operand = $3; sub(/^\$/, "", operand); sub(/,%rsp$/, "", operand)
    allocation[caller] += unsigned_immediate(operand)
  }
  caller != "" && $2 ~ /^(and|andq|enter|lea|leaq|mov|movq)$/ && $3 ~ /,%rsp$/ {
    print caller "\t" $2 "\t" $3 >> unsupported
  }
  caller != "" && $2 ~ /^(callq?|jmpq?)$/ {
    target = $NF
    if (target ~ /^<[^>]+>$/) {
      gsub(/[<>]/, "", target); sub(/\+0x.*/, "", target)
      # Ignore jumps to a local basic block in the same symbol, but retain a
      # direct self-call: the former is ordinary control flow and the latter
      # is recursion that invalidates finite stack accounting.
      if (caller != target || $2 ~ /^callq?$/) {
        print caller "\t" target
        if ($2 ~ /^callq?$/) print caller "\t" target >> calls
      }
    } else if ($3 ~ /^\*/) {
      print caller "\t" $2 "\t" $3 >> indirect
    }
  }
  END {
    for (function_name in count) print function_name "\t" count[function_name] > pushes
    for (function_name in present)
      print function_name "\t" (allocation[function_name] + 0) > assembly
  }
' | sort -u >"$tmp/edges"
touch "$tmp/indirect"
touch "$tmp/pushes"
touch "$tmp/assembly"
touch "$tmp/unsupported"
touch "$tmp/calls"
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
  assembly_bytes=0
  assembly_functions=0
  root_assembly_bytes=0
  while IFS= read -r function_name; do
    [[ -z "${usage[$function_name]+set}" ]] || continue
    assembly_cost="$(awk -F '\t' -v name="$function_name" \
      '$1 == name { print $2; found = 1 } END { if (!found) exit 1 }' "$tmp/assembly")" || {
      echo "error: path=$path final-elf-unaccounted-assembly=$function_name" >&2
      exit 1
    }
    unsupported_instruction="$(awk -F '\t' -v name="$function_name" \
      '$1 == name { print $2 " " $3; exit }' "$tmp/unsupported")"
    [[ -z "$unsupported_instruction" ]] || {
      echo "error: path=$path final-elf-unsupported-stack-mutation=$function_name:$unsupported_instruction" >&2
      exit 1
    }
    if [[ "$function_name" == "$elf_root" ]]; then
      modeled_root_bytes=$((save_count * 8 + normalization_bytes))
      root_assembly_bytes="$assembly_cost"
      (( assembly_cost >= modeled_root_bytes )) || {
        echo "error: path=$path final-elf-root-stack-allocation=$assembly_cost expected-at-least=$modeled_root_bytes root=$elf_root" >&2
        exit 1
      }
      assembly_cost=$((assembly_cost - modeled_root_bytes))
    fi
    assembly_bytes=$((assembly_bytes + assembly_cost))
    assembly_functions=$((assembly_functions + 1))
  done <"$tmp/reachable"
  reachable_calls="$(awk -F '\t' 'NR == FNR { reached[$1] = 1; next }
      reached[$1] && reached[$2] { count++ } END { print count + 0 }' \
      "$tmp/reachable" "$tmp/calls")"
  call_bytes=$((reachable_calls * 8))
  final_total=$((static_total[$path] + assembly_bytes + call_bytes))
  final_margin=$((usable_bytes - final_total))
  (( final_margin >= 0 )) || {
    echo "error: path=$path final-elf-entry-stack over budget by $((-final_margin)) byte(s) total=$final_total usable=$usable_bytes assembly=$assembly_bytes call-returns=$call_bytes" >&2
    exit 1
  }
  for function_name in "$elf_root" "${chain[@]}"; do
    grep -Fxq "$function_name" "$tmp/symbols" || {
      echo "error: path=$path final-elf-missing-function=$function_name" >&2; exit 1;
    }
    grep -Fxq "$function_name" "$tmp/reachable" || {
      echo "error: path=$path final-elf-unreachable-function=$function_name root=$elf_root" >&2
      exit 1
    }
  done
  printf 'path=%s final-elf-root=%s save-register-pushes=%s reviewed-functions=%s reachable-functions=%s assembly-functions=%s root-assembly-bytes=%s assembly-bytes=%s call-return-bytes=%s total=%s margin=%s extracted-edges=%s result=PASS\n' \
    "$path" "$elf_root" "$elf_save_count" "${#chain[@]}" "$(wc -l <"$tmp/reachable")" \
    "$assembly_functions" "$root_assembly_bytes" "$assembly_bytes" "$call_bytes" "$final_total" "$final_margin" \
    "$(wc -l <"$tmp/edges")"
done < "$manifest"
