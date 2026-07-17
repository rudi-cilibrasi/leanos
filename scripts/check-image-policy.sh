#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
[[ -f "$elf" ]] || { echo "error: missing ELF: $elf" >&2; exit 1; }
symbols="$(nm "$elf")"

flags() {
  readelf -SW "$elf" | awk -v section="$1" \
    '{ for (field = 1; field <= NF; field++) if ($field == section) print $(field + 6) }'
}
[[ "$(flags .text)" == *A* && "$(flags .text)" == *X* && "$(flags .text)" != *W* ]]
for section in .user_a_text .user_b_text; do
  [[ "$(flags "$section")" == *A* && "$(flags "$section")" == *X* && "$(flags "$section")" != *W* ]]
done
for section in .user_a_bss .user_b_bss; do
  [[ "$(flags "$section")" == *A* && "$(flags "$section")" == *W* && "$(flags "$section")" != *X* ]]
done

for symbol in __boot_image_start __boot_image_end __kernel_text_start __kernel_text_end __user_a_text_start \
  __user_a_text_end __user_a_stack_start __user_a_stack_end \
  __user_b_text_start __user_b_text_end __user_b_stack_start \
  __user_b_stack_end entry_stack page_table_a page_table_b \
  page_map_level_4_a page_directory_pointer_a page_directory_a \
  page_map_level_4_b page_directory_pointer_b page_directory_b; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: image policy symbol missing: $symbol" >&2; exit 1;
  }
done

for symbol in isr8 isr8_clac isr8_cld isr13 run_double_fault_probe \
  __df_ist_guard_start __df_ist_guard_end __df_ist_stack_start \
  __df_ist_stack_end df_ist_guard df_ist_stack df_ist_stack_top; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: double-fault policy symbol missing: $symbol" >&2
    exit 1
  }
done
for section in .df_ist_guard .df_ist_stack; do
  [[ "$(flags "$section")" == *A* && "$(flags "$section")" == *W* && \
     "$(flags "$section")" != *X* ]] || {
    echo "error: $section must be allocated, writable, and non-executable" >&2
    exit 1
  }
done

symbol_address() { nm -n "$elf" | awk -v name="$1" '$3 == name { print "0x" $1 }'; }
image_start="$(symbol_address __boot_image_start)"
image_end="$(symbol_address __boot_image_end)"
[[ -n "$image_start" && -n "$image_end" && $((image_start)) -lt $((image_end)) ]] || {
  echo "error: invalid half-open boot image boundaries" >&2; exit 1;
}
[[ $((image_start % 4096)) -eq 0 && $((image_end % 4096)) -eq 0 ]] || {
  echo "error: boot image boundaries must be page aligned" >&2; exit 1;
}

guard_start="$(symbol_address __df_ist_guard_start)"
guard_end="$(symbol_address __df_ist_guard_end)"
stack_start="$(symbol_address __df_ist_stack_start)"
stack_end="$(symbol_address __df_ist_stack_end)"
[[ $((guard_end - guard_start)) -eq 4096 && $((guard_end)) -eq $((stack_start)) && \
   $((stack_end - stack_start)) -eq 16384 && $((stack_start % 4096)) -eq 0 ]] || {
  echo "error: double-fault guard/IST1 bounds are not one page plus 16 KiB" >&2
  exit 1
}
grep -Fq 'tss.ist[0] = (uint64_t)__df_ist_stack_end;' boot/kernel.c
[[ "$(grep -Ec 'set_gate\([^,]+,[^,]+, 1,' boot/kernel.c)" -eq 1 ]]
grep -Fq 'set_gate(8, isr8, 1, 0x8e);' boot/kernel.c
grep -Fq 'set_gate(13, isr13, 0, 0x8e);' boot/kernel.c
grep -Fq 'movl $0, page_table_a(%eax)' boot/boot.S
grep -Fq 'movl $0, page_table_b(%eax)' boot/boot.S
stub_disassembly="$(objdump -d "$elf" | sed -n '/<isr8>:/,/<isr80>:/p')"
[[ -n "$stub_disassembly" ]] || {
  echo "error: could not isolate vector-8 disassembly" >&2
  exit 1
}
if grep -Eq '\<(call|iretq|push)\>' <<<"$stub_disassembly"; then
  echo "error: vector-8 terminal stub calls, pushes, or returns with iretq" >&2
  exit 1
fi

check_range() {
  local start_name="$1" end_name="$2" start end
  start="$(symbol_address "$start_name")"
  end="$(symbol_address "$end_name")"
  [[ -n "$start" && -n "$end" && $((image_start)) -le $((start)) &&
      $((start)) -lt $((end)) && $((end)) -le $((image_end)) ]] || {
    echo "error: invalid or out-of-image range: $start_name..$end_name" >&2
    exit 1
  }
}
check_range __kernel_text_start __kernel_text_end
check_range __user_a_text_start __user_a_text_end
check_range __user_a_stack_start __user_a_stack_end
check_range __user_b_text_start __user_b_text_end
check_range __user_b_stack_start __user_b_stack_end

while read -r address _ symbol; do
  [[ $((16#$address)) -ge $((image_start)) && $((16#$address)) -lt $((image_end)) ]] || {
    echo "error: boot artifact $symbol lies outside boot image manifest" >&2; exit 1;
  }
done < <(nm -n "$elf" | awk '$3 ~ /^(page_map_level_4_[ab]|page_table_[ab]|gdt64|idt|tss|entry_stack|user_[ab]_stack)$/ { print }')

# These named instructions make ordering reviewable in both the ELF symbol table
# and disassembly: WP is set in the final CR0 paging write, while SMEP is enabled
# by a distinct routine invoked only after privilege_init installs vector 14.
for symbol in enable_smep run_wp_probe wp_probe_instruction wp_probe_recovered \
  wp_probe_target run_smep_probe smep_probe_instruction smep_probe_recovered; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: supervisor-control evidence symbol missing: $symbol" >&2; exit 1;
  }
done
grep -Fq 'or $((1 << 31) | (1 << 16)), %eax' boot/boot.S
grep -Fq 'bts $20, %rax' boot/boot.S
grep -Fq 'bts $21, %rax' boot/boot.S
[[ "$(grep -Ec '^[[:space:]]+stac$' boot/boot.S)" -eq 3 ]]
[[ "$(grep -Ec '^[[:space:]]+clac$' boot/boot.S)" -eq 9 ]]
[[ "$(grep -Ec '^[[:space:]]+cld$' boot/boot.S)" -eq 10 ]]
for symbol in smap_copy_from_cld smap_copy_from_stac smap_copy_from_clac \
  smap_copy_to_cld smap_copy_to_stac \
  smap_copy_to_clac smap_omit_cleanup_probe_stac smap_force_clac \
  isr80_clac isr80_cld isr14_clac isr14_cld isr32_clac isr32_cld \
  run_smap_probe; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || { echo "error: SMAP evidence symbol missing: $symbol" >&2; exit 1; }
done
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
[[ "$(grep -Fc 'orl $4, page_table_a+8(%eax)' boot/boot.S)" -eq 1 ]]
[[ "$(grep -Fc 'orl $4, page_table_b(%eax)' boot/boot.S)" -eq 2 ]]
grep -Fq 'andl $~2, page_table_a(%eax)' boot/boot.S
grep -Fq 'andl $~2, page_table_b(%eax)' boot/boot.S
grep -Fq 'movl $0x80000000, 4(%edi)' boot/boot.S
grep -Fq 'or $((1 << 8) | (1 << 11)), %eax' boot/boot.S
grep -Fq 'LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS' boot/kernel.c
grep -Fq 'LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS' boot/kernel.c
grep -Fq 'LEANOS/8 PAGING root=B selected=1 result=PASS' boot/kernel.c
grep -Fq 'check_live_page_table_mutations();' boot/kernel.c
grep -Fq 'fixture=wrong-cr3 root=A level=cr3' boot/kernel.c

# Each address space grants U/S only to its own text and stack symbols.
! grep -Fq '__user_b_text_start' <(sed -n '/__user_a_text_start/,/__user_b_text_start/{p}' boot/boot.S | head -n -1)
grep -q ' T leanos_ipc_demo$' <<<"$symbols"
grep -q ' T leanos_preemption_demo$' <<<"$symbols"
grep -q ' B saved_context_a$' <<<"$symbols"
grep -q ' B saved_context_b$' <<<"$symbols"
grep -q ' R initial_context_b$' <<<"$symbols"
saved_a="$(nm -n "$elf" | awk '$3 == "saved_context_a" { print "0x" $1 }')"
saved_b="$(nm -n "$elf" | awk '$3 == "saved_context_b" { print "0x" $1 }')"
[[ $((saved_b - saved_a)) -eq 160 ]] || {
  echo "error: resumable context A does not occupy the reviewed 160-byte image" >&2
  exit 1
}
[[ "$(grep -Fc 'rep movsq' boot/boot.S)" -eq 4 ]]
grep -Fq 'lea initial_context_b(%rip), %rsi' boot/boot.S
[[ "$(grep -Ec 'cmp \$B_INITIAL_R[A-Z0-9]+, %r' boot/boot.S)" -eq 13 ]]
[[ "$(grep -Fc 'movabs $B_INITIAL_R' boot/boot.S)" -eq 2 ]]
grep -Fq 'check_initial_b_frame(target);' boot/kernel.c
grep -Fq 'initial_context_b[17] = 0x206;' boot/kernel.c
grep -Fq 'if (initial_b_frame_valid(initial_context_b)) fail("initial-flags-negative");' boot/kernel.c
grep -Fq 'saved_context_a[16] != 0x23' boot/kernel.c
grep -Fq 'saved_context_b[19] != 0x1b' boot/kernel.c

# All CPL3 transitions converge on one validator call and consume the validated
# frame without an intervening call, write, or context switch. The sole other
# iretq belongs to the explicitly separate supervisor diagnostic recovery path.
for symbol in user_return_epilogue user_return_iretq validate_user_return; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: user-return policy symbol missing: $symbol" >&2; exit 1;
  }
done
[[ "$(objdump -d "$elf" | grep -c '[[:space:]]iretq')" -eq 2 ]] || {
  echo "error: expected one validated user iretq and one diagnostic kernel iretq" >&2; exit 1;
}
return_disassembly="$(objdump -d "$elf" | sed -n '/<user_return_epilogue>:/,/<user_return_iretq>:/p')"
grep -Eq 'call.*<validate_user_return>' <<<"$return_disassembly" || {
  echo "error: user-return epilogue does not call validator" >&2; exit 1;
}
post_validation="$(objdump -d "$elf" | sed -n '/call.*<validate_user_return>/,/<user_return_iretq>:/p')"
if grep -Eq '\<(call|mov .*%cr3)\>' <<<"${post_validation#*$'\n'}"; then
  echo "error: validated return frame/context changes before iretq" >&2; exit 1
fi
[[ "$(grep -Ec '^[[:space:]]+iretq$' boot/boot.S)" -eq 2 ]] || {
  echo "error: raw iretq added outside classified return sites" >&2; exit 1;
}

echo "ELF sections, policy symbols, and constructed page-table policy passed"
