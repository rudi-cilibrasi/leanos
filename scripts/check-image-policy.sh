#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
[[ -f "$elf" ]] || { echo "error: missing ELF: $elf" >&2; exit 1; }

flags() { readelf -SW "$elf" | awk -v section="$1" '$3 == section { print $9 }'; }
[[ "$(flags .text)" == *A* && "$(flags .text)" == *X* && "$(flags .text)" != *W* ]]
[[ "$(flags .user_text)" == *A* && "$(flags .user_text)" == *X* && "$(flags .user_text)" != *W* ]]
[[ "$(flags .user_bss)" == *A* && "$(flags .user_bss)" == *W* && "$(flags .user_bss)" != *X* ]]

for symbol in __kernel_text_start __kernel_text_end __user_text_start \
  __user_text_end __user_stack_start __user_stack_end entry_stack page_table; do
  nm "$elf" | grep -Eq "[[:space:]]${symbol}$" || {
    echo "error: image policy symbol missing: $symbol" >&2; exit 1;
  }
done

# The runtime page-table constructor must keep U/S limited to the two reviewed
# leaves, make instruction leaves read-only, and enable NX for all other leaves.
grep -Fq 'orl $4, page_table(%eax)' boot/boot.S
[[ "$(grep -Fc 'orl $4, page_table(%eax)' boot/boot.S)" -eq 2 ]]
grep -Fq 'andl $~2, page_table(%eax)' boot/boot.S
grep -Fq 'movl $0x80000000, 4(%edi)' boot/boot.S
grep -Fq 'or $((1 << 8) | (1 << 11)), %eax' boot/boot.S

echo "ELF sections, policy symbols, and constructed page-table policy passed"
