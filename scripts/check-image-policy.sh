#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
[[ -f "$elf" ]] || { echo "error: missing ELF: $elf" >&2; exit 1; }

flags() { readelf -SW "$elf" | awk -v section="$1" '$3 == section { print $9 }'; }
[[ "$(flags .text)" == *A* && "$(flags .text)" == *X* && "$(flags .text)" != *W* ]]
for section in .user_a_text .user_b_text; do
  [[ "$(flags "$section")" == *A* && "$(flags "$section")" == *X* && "$(flags "$section")" != *W* ]]
done
for section in .user_a_bss .user_b_bss; do
  [[ "$(flags "$section")" == *A* && "$(flags "$section")" == *W* && "$(flags "$section")" != *X* ]]
done

for symbol in __kernel_text_start __kernel_text_end __user_a_text_start \
  __user_a_text_end __user_a_stack_start __user_a_stack_end \
  __user_b_text_start __user_b_text_end __user_b_stack_start \
  __user_b_stack_end entry_stack page_table_a page_table_b \
  page_map_level_4_a page_map_level_4_b; do
  nm "$elf" | grep -Eq "[[:space:]]${symbol}$" || {
    echo "error: image policy symbol missing: $symbol" >&2; exit 1;
  }
done

# These named instructions make ordering reviewable in both the ELF symbol table
# and disassembly: WP is set in the final CR0 paging write, while SMEP is enabled
# by a distinct routine invoked only after privilege_init installs vector 14.
for symbol in enable_smep run_wp_probe wp_probe_instruction wp_probe_recovered \
  wp_probe_target run_smep_probe smep_probe_instruction smep_probe_recovered; do
  nm "$elf" | grep -Eq "[[:space:]]${symbol}$" || {
    echo "error: supervisor-control evidence symbol missing: $symbol" >&2; exit 1;
  }
done
grep -Fq 'or $((1 << 31) | (1 << 16)), %eax' boot/boot.S
grep -Fq 'bts $20, %rax' boot/boot.S
grep -Fq 'fault_address == (uint64_t)wp_probe_target' boot/kernel.c
grep -Fq 'fault_address == (uint64_t)user_a_entry' boot/kernel.c
grep -Fq 'if (supervisor_probe != 2) fail("wp-no-fault")' boot/kernel.c
grep -Fq 'if (supervisor_probe != 4) fail("smep-no-fault")' boot/kernel.c

for suffix in a b; do
  page_table_start="$(nm -n "$elf" | awk -v name="page_table_$suffix" '$3 == name { print "0x" $1 }')"
  page_table_end="$(nm -n "$elf" | awk -v name="page_table_${suffix}_end" '$3 == name { print "0x" $1 }')"
  [[ $((page_table_end - page_table_start)) -eq $((8 * 4096)) ]] || {
    echo "error: address-space $suffix storage does not match eight installed tables" >&2
    exit 1
  }
done

# The runtime page-table constructor must keep U/S limited to the two reviewed
# leaves, make instruction leaves read-only, and enable NX for all other leaves.
[[ "$(grep -Fc 'orl $4, page_table_a(%eax)' boot/boot.S)" -eq 2 ]]
[[ "$(grep -Fc 'orl $4, page_table_b(%eax)' boot/boot.S)" -eq 2 ]]
grep -Fq 'andl $~2, page_table_a(%eax)' boot/boot.S
grep -Fq 'andl $~2, page_table_b(%eax)' boot/boot.S
grep -Fq 'movl $0x80000000, 4(%edi)' boot/boot.S
grep -Fq 'or $((1 << 8) | (1 << 11)), %eax' boot/boot.S

# Each address space grants U/S only to its own text and stack symbols.
! grep -Fq '__user_b_text_start' <(sed -n '/__user_a_text_start/,/__user_b_text_start/{p}' boot/boot.S | head -n -1)
nm "$elf" | grep -q ' T leanos_ipc_demo$'

echo "ELF sections, policy symbols, and constructed page-table policy passed"
