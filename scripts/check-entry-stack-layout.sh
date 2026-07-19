#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
[[ -f "$elf" ]] || { echo "error: missing ELF: $elf" >&2; exit 1; }

symbol_address() {
  nm -n "$elf" | awk -v name="$1" '$3 == name { print "0x" $1 }'
}

for symbol in entry_stack __entry_stack_guard_start __entry_stack_guard_end \
  __entry_stack_start __entry_stack_end; do
  [[ -n "$(symbol_address "$symbol")" ]] || {
    echo "error: ordinary-entry layout symbol missing: $symbol" >&2
    exit 1
  }
done

section_property() {
  local section="$1" offset="$2"
  readelf -SW "$elf" | awk -v section="$section" -v offset="$offset" '
    { for (field = 1; field <= NF; field++)
        if ($field == section) print $(field + offset) }'
}

for section in .entry_stack_guard .entry_stack; do
  type="$(section_property "$section" 1)"
  flags="$(section_property "$section" 6)"
  [[ "$type" == NOBITS ]] || {
    echo "error: ordinary-entry section $section must be NOBITS, found ${type:-missing}" >&2
    exit 1
  }
  [[ "$flags" == *A* && "$flags" == *W* && "$flags" != *X* ]] || {
    echo "error: ordinary-entry section $section must be allocated, writable, and non-executable" >&2
    exit 1
  }
done

guard_start="$(symbol_address __entry_stack_guard_start)"
guard_end="$(symbol_address __entry_stack_guard_end)"
stack_start="$(symbol_address __entry_stack_start)"
stack_end="$(symbol_address __entry_stack_end)"
stack_symbol="$(symbol_address entry_stack)"

[[ $((guard_start % 4096)) -eq 0 ]] || {
  echo "error: ordinary-entry guard start is not page aligned" >&2; exit 1;
}
[[ $((stack_end % 16)) -eq 0 ]] || {
  echo "error: ordinary-entry canonical top is not 16-byte aligned" >&2; exit 1;
}
[[ $((guard_end - guard_start)) -eq 4096 ]] || {
  echo "error: ordinary-entry guard is not exactly one page" >&2; exit 1;
}
[[ $((guard_end)) -eq $((stack_start)) ]] || {
  echo "error: ordinary-entry guard is not adjacent to the usable stack" >&2; exit 1;
}
[[ $((stack_end - stack_start)) -eq 16384 ]] || {
  echo "error: ordinary-entry usable stack is not exactly 16 KiB" >&2; exit 1;
}
[[ $((stack_symbol)) -eq $((stack_start)) ]] || {
  echo "error: entry_stack does not identify the usable interval start" >&2; exit 1;
}

echo "ordinary-entry final-ELF layout passed"
