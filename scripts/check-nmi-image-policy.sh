#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos-nmi.elf}"
source_root="${LEANOS_SOURCE_ROOT:-.}"
[[ -f "$elf" ]] || { echo "error: missing NMI ELF: $elf" >&2; exit 1; }
symbols="$(nm "$elf")"

require_source_text() {
  local file="$1"
  local expected="$2"
  local normalized
  [[ -f "$file" ]] || {
    echo "error: missing NMI policy source: $file" >&2
    exit 1
  }
  normalized="$(tr '\n' ' ' <"$file")"
  grep -Fq "$expected" <<<"$normalized" || {
    echo "error: NMI policy text missing from $file: $expected" >&2
    exit 1
  }
}

for symbol in isr2 isr2_clac isr2_cld __nmi_ist_guard_start \
  __nmi_ist_guard_end nmi_ist_guard __nmi_ist_stack_start \
  __nmi_ist_stack_end nmi_ist_stack nmi_ist_stack_top ordinary_entry_active; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: NMI terminal policy symbol missing: $symbol" >&2
    exit 1
  }
done

section_property() {
  local section="$1" offset="$2"
  readelf -SW "$elf" | awk -v section="$section" -v offset="$offset" '
    { for (field = 1; field <= NF; field++)
        if ($field == section) print $(field + offset) }'
}
for section in .nmi_ist_guard .nmi_ist_stack; do
  type="$(section_property "$section" 1)"
  flags="$(section_property "$section" 6)"
  [[ "$type" == NOBITS ]] || {
    echo "error: NMI section $section must be NOBITS, found ${type:-missing}" >&2
    exit 1
  }
  [[ "$flags" == *A* && "$flags" == *W* && "$flags" != *X* ]] || {
    echo "error: NMI section $section must be allocated, writable, and non-executable" >&2
    exit 1
  }
done
address() { nm -n "$elf" | awk -v name="$1" '$3 == name { print "0x" $1 }'; }
guard_start="$(address __nmi_ist_guard_start)"
guard_end="$(address __nmi_ist_guard_end)"
start="$(address __nmi_ist_stack_start)"
end="$(address __nmi_ist_stack_end)"
df_end="$(address __df_ist_stack_end)"
[[ $((guard_end - guard_start)) -eq 4096 &&
    $((guard_start % 4096)) -eq 0 && $((guard_end)) -eq $((start)) &&
    $((df_end)) -eq $((guard_start)) &&
    $((end - start)) -eq 16384 && $((start % 4096)) -eq 0 &&
    $((end % 16)) -eq 0 && $(((end - 40) % 16)) -eq 8 ]] || {
  echo "error: NMI guard/IST2 bounds are not one absent page plus a distinct aligned 16 KiB interval" >&2
  exit 1
}
guard_constructor="$(sed -n '/mov \$__nmi_ist_guard_start, %eax/,/movl \$0, page_table_b+4(%eax)/p' \
  "$source_root/boot/boot.S")"
[[ "$(grep -Fc 'mov $__nmi_ist_guard_start, %eax' "$source_root/boot/boot.S")" -eq 1 &&
   "$(grep -Fxc '    movl $0, page_table_a(%eax)' <<<"$guard_constructor")" -eq 1 &&
   "$(grep -Fxc '    movl $0, page_table_a+4(%eax)' <<<"$guard_constructor")" -eq 1 &&
   "$(grep -Fxc '    movl $0, page_table_b(%eax)' <<<"$guard_constructor")" -eq 1 &&
   "$(grep -Fxc '    movl $0, page_table_b+4(%eax)' <<<"$guard_constructor")" -eq 1 ]] || {
  echo "error: NMI guard must be cleared exactly once in both early address spaces" >&2
  exit 1
}
require_source_text "$source_root/boot/kernel.c" \
  'tss.ist[1] = (uint64_t)__nmi_ist_stack_end;'
require_source_text "$source_root/boot/kernel.c" 'set_gate(2, isr2, 2, 0x8e);'
require_source_text "$source_root/docs/interrupt-model.md" \
  'firmware does not deliver NMI before'
require_source_text "$source_root/docs/interrupt-model.md" \
  'which begins only after `NMI-READY`'
stub="$(objdump -d "$elf" | sed -n '/<isr2>:/,/<isr13>:/p')"
[[ -n "$stub" ]] || { echo "error: could not isolate vector-2 disassembly" >&2; exit 1; }
if grep -Eq '\<push[qwl]?\>' <<<"$stub"; then
  echo "error: vector-2 terminal stub pushes on the bounded IST2 frame" >&2
  exit 1
fi
./scripts/check-terminal-cfg.py "$elf" isr2 isr13
grep -Eq '[[:space:]]cli$' <<<"$stub"
grep -Eq '[[:space:]]clac$' <<<"$stub"
grep -Eq '[[:space:]]cld$' <<<"$stub"

echo "NMI final-ELF gate, IST2, frame, cleanup, and terminal CFG policy passed"
