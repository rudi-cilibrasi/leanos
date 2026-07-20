#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos-nmi.elf}"
[[ -f "$elf" ]] || { echo "error: missing NMI ELF: $elf" >&2; exit 1; }
symbols="$(nm "$elf")"

for symbol in isr2 isr2_clac isr2_cld __nmi_ist_stack_start \
  __nmi_ist_stack_end nmi_ist_stack nmi_ist_stack_top ordinary_entry_active; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: NMI terminal policy symbol missing: $symbol" >&2
    exit 1
  }
done

flags="$(readelf -SW "$elf" | awk \
  '{ for (field = 1; field <= NF; field++) if ($field == ".nmi_ist_stack") print $(field + 6) }')"
[[ "$flags" == *A* && "$flags" == *W* && "$flags" != *X* ]] || {
  echo "error: .nmi_ist_stack must be allocated, writable, and non-executable" >&2
  exit 1
}
address() { nm -n "$elf" | awk -v name="$1" '$3 == name { print "0x" $1 }'; }
start="$(address __nmi_ist_stack_start)"
end="$(address __nmi_ist_stack_end)"
[[ $((end - start)) -eq 16384 && $((start % 4096)) -eq 0 ]] || {
  echo "error: NMI IST2 bounds are not an aligned 16 KiB interval" >&2
  exit 1
}
grep -Fq 'tss.ist[1] = (uint64_t)__nmi_ist_stack_end;' boot/kernel.c
grep -Fq 'set_gate(2, isr2, 2, 0x8e);' boot/kernel.c
grep -Fq 'firmware does not deliver NMI before' docs/interrupt-model.md
grep -Fq 'which begins only after `NMI-READY`' docs/interrupt-model.md
stub="$(objdump -d "$elf" | sed -n '/<isr2>:/,/<isr13>:/p')"
[[ -n "$stub" ]] || { echo "error: could not isolate vector-2 disassembly" >&2; exit 1; }
if grep -Eq '\<(call|iretq|push)\>' <<<"$stub"; then
  echo "error: vector-2 terminal stub calls, pushes, or returns with iretq" >&2
  exit 1
fi
grep -Eq '[[:space:]]cli$' <<<"$stub"
grep -Eq '[[:space:]]clac$' <<<"$stub"
grep -Eq '[[:space:]]cld$' <<<"$stub"

echo "NMI final-ELF gate, IST2, frame, cleanup, and terminal CFG policy passed"
