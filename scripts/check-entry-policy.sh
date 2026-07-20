#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
kernel_source="${LEANOS_ENTRY_KERNEL_SOURCE:-boot/kernel.c}"
boot_source="${LEANOS_ENTRY_BOOT_SOURCE:-boot/boot.S}"
[[ -f "$elf" ]] || { echo "error: missing entry-policy ELF: $elf" >&2; exit 1; }
[[ -f "$kernel_source" && -f "$boot_source" ]] || {
  echo "error: missing entry-policy source snapshot" >&2; exit 1;
}

symbols="$(nm "$elf")"
control_disassembly="$(objdump -d --no-show-raw-insn "$elf")"
for symbol in isr2 isr6 isr7 isr13 isr14 isr32 isr80 authorize_interrupt_entry \
  complete_interrupt_entry extended_state_denial_handler syscall_handler \
  page_fault_handler timer_handler entry_stack boot_stack boot_stack_top \
  normalize_fast_entry_msrs read_fast_entry_msrs check_fast_entry_cpuid; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: entry manifest symbol missing: $symbol" >&2; exit 1;
  }
done

require_fast_entry_site() {
  local symbol="$1" opcode="$2" source_site elf_site
  source_site="$(sed -n "/^${symbol}:$/{n;p;q;}" "$boot_source")"
  [[ "$source_site" =~ ^[[:space:]]*${opcode}[[:space:]]*$ ]] || {
    echo "error: fast-entry ${opcode} site drifted: ${symbol}" >&2
    exit 1
  }
  elf_site="$(sed -n "/<${symbol}>:/{n;p;q;}" <<<"$control_disassembly")"
  [[ "$elf_site" =~ ^[[:space:]]*[[:xdigit:]]+:[[:space:]]+${opcode}([[:space:]]|$) ]] || {
    echo "error: fast-entry final-ELF ${opcode} site drifted: ${symbol}" >&2
    exit 1
  }
}

# Fast-entry state must be produced by the reviewed early writes and consumed
# by one explicit read-back inventory before any user return.  The labels keep
# each privileged instruction reviewable in the final ELF.
for symbol in normalize_fast_entry_efer_write normalize_fast_entry_star_write \
  normalize_fast_entry_lstar_write normalize_fast_entry_cstar_write \
  normalize_fast_entry_sfmask_write normalize_fast_entry_sysenter_cs_write \
  normalize_fast_entry_sysenter_esp_write normalize_fast_entry_sysenter_eip_write \
  read_fast_entry_efer read_fast_entry_star read_fast_entry_lstar \
  read_fast_entry_cstar read_fast_entry_sfmask read_fast_entry_sysenter_cs \
  read_fast_entry_sysenter_esp read_fast_entry_sysenter_eip; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: fast-entry control symbol missing: $symbol" >&2; exit 1;
  }
done
for symbol in normalize_fast_entry_efer_write normalize_fast_entry_star_write \
  normalize_fast_entry_lstar_write normalize_fast_entry_cstar_write \
  normalize_fast_entry_sfmask_write normalize_fast_entry_sysenter_cs_write \
  normalize_fast_entry_sysenter_esp_write normalize_fast_entry_sysenter_eip_write; do
  require_fast_entry_site "$symbol" wrmsr
done
for symbol in read_fast_entry_efer read_fast_entry_star read_fast_entry_lstar \
  read_fast_entry_cstar read_fast_entry_sfmask read_fast_entry_sysenter_cs \
  read_fast_entry_sysenter_esp read_fast_entry_sysenter_eip; do
  require_fast_entry_site "$symbol" rdmsr
done
[[ "$(grep -Ec '^[[:space:]]+wrmsr$' "$boot_source")" -eq 8 ]] || {
  echo "error: fast-entry control write inventory drifted" >&2; exit 1;
}
[[ "$(grep -Ec '^[[:space:]]+rdmsr$' "$boot_source")" -eq 9 ]] || {
  echo "error: fast-entry control read inventory drifted" >&2; exit 1;
}
grep -Fq 'and $~1, %eax' "$boot_source" || {
  echo "error: fast-entry control does not clear EFER.SCE" >&2; exit 1;
}
# After the EFER write, EAX/EDX must remain the reviewed zero pair through the
# STAR/LSTAR/CSTAR/SFMASK and every SYSENTER write.  This source
# gate complements the final-ELF instruction count by rejecting a stale,
# noncanonical, or merely nonzero target value without pretending to execute
# privileged MSR accesses on the host.
target_write_recipe="$(sed -n \
  '/^\.global normalize_fast_entry_efer_write$/,/^\.global normalize_extended_state_cr0$/p' \
  "$boot_source")"
[[ -n "$target_write_recipe" ]] || {
  echo "error: fast-entry target write recipe is missing" >&2; exit 1;
}
unexpected_target_value_write="$(
  grep -E '^[[:space:]]*[[:alnum:]]+[[:space:]].*,[[:space:]]*%(e|r)(ax|dx)[[:space:]]*$' \
    <<<"$target_write_recipe" \
  | grep -Ev '^[[:space:]]*xor %eax, %eax$|^[[:space:]]*xor %edx, %edx$' \
  || true
)"
[[ -z "$unexpected_target_value_write" ]] || {
  echo "error: fast-entry target write recipe can introduce nonzero state" >&2
  echo "$unexpected_target_value_write" >&2
  exit 1
}
grep -Fq 'check_fast_entry_control();' "$kernel_source" || {
  echo "error: fast-entry control read-back is not boot-reachable" >&2; exit 1;
}
grep -Fq 'check_fast_entry_cpuid();' "$kernel_source" || {
  echo "error: fast-entry CPUID contract is not boot-reachable" >&2; exit 1;
}
for contract in \
  'vendor_b != UINT32_C(0x68747541)' \
  'vendor_d != UINT32_C(0x69746e65)' \
  'vendor_c != UINT32_C(0x444d4163)' \
  '((leaf_d >> 11) & 1u) == 0u' \
  'max_extended < UINT32_C(0x80000001)' \
  '((leaf_d >> 29) & 1u) == 0u'; do
  grep -Fq "$contract" "$kernel_source" || {
    echo "error: fast-entry CPUID contract drifted field=$contract" >&2; exit 1;
  }
done
[[ "$(grep -Ec '[[:space:]]cpuid([[:space:]]|$)' <<<"$control_disassembly")" -ge 6 ]] || {
  echo "error: fast-entry CPUID snapshot missing from final ELF" >&2; exit 1;
}
[[ "$(grep -Ec '[[:space:]]wrmsr$' <<<"$control_disassembly")" -eq 8 ]] || {
  echo "error: fast-entry final-ELF write inventory drifted" >&2; exit 1;
}
[[ "$(grep -Ec '[[:space:]]rdmsr$' <<<"$control_disassembly")" -eq 9 ]] || {
  echo "error: fast-entry final-ELF read inventory drifted" >&2; exit 1;
}
fast_probe="${LEANOS_FAST_ENTRY_PROBE:-}"
if [[ -z "$fast_probe" ]]; then
  if grep -Eq '[[:space:]](syscall|sysenter|sysretq?|sysexit)([[:space:]]|$)' \
      <<<"$control_disassembly"; then
    echo "error: unauthorized fast-entry opcode in final ELF" >&2; exit 1
  fi
elif [[ "$fast_probe" == syscall || "$fast_probe" == sysenter ]]; then
  [[ "$(grep -Ec "[[:space:]]${fast_probe}([[:space:]]|$)" <<<"$control_disassembly")" -eq 1 ]] || {
    echo "error: deliberate $fast_probe probe inventory drifted" >&2; exit 1;
  }
  other=syscall; [[ "$fast_probe" == syscall ]] && other=sysenter
  if grep -Eq "[[:space:]](${other}|sysretq?|sysexit)([[:space:]]|$)" \
      <<<"$control_disassembly"; then
    echo "error: unauthorized fast-entry opcode in probe ELF" >&2; exit 1
  fi
  probe_dis="$(objdump -d --no-show-raw-insn "$elf" | sed -n \
    '/<user_a_extended_state_probe>:/,/^$/p')"
  grep -Eq "[[:space:]]${fast_probe}([[:space:]]|$)" <<<"$probe_dis" || {
    echo "error: deliberate $fast_probe opcode is outside its reviewed probe site" >&2; exit 1;
  }
else
  echo "error: unknown LEANOS_FAST_ENTRY_PROBE '$fast_probe'" >&2; exit 1
fi

[[ "$(grep -Ec 'set_gate\(' "$kernel_source")" -eq 9 ]] || {
  echo "error: vector=77 field=present violated=unexpected-installed-gate-count" >&2; exit 1;
}
grep -Fq 'set_gate(2, isr2, 2, 0x8e);' "$kernel_source" || {
  echo "error: vector=2 field=target-ist-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(6, isr6, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=6 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(7, isr7, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=7 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(13, isr13, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=13 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(14, isr14, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=14 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(32, isr32, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=32 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(0x80, isr80, 0, 0xee);' "$kernel_source" || {
  echo "error: vector=128 field=target-or-dpl" >&2; exit 1;
}
[[ "$(grep -Ec 'set_gate\([^,]+,[^,]+,[^,]+, 0xee\)' "$kernel_source")" -eq 1 ]] || {
  echo "error: vector=128 field=dpl expected=3 violated=extra-dpl3-gate" >&2; exit 1;
}
grep -Fq 'tss.rsp0 = (uint64_t)__entry_stack_end;' "$kernel_source" || {
  echo "error: vector=128 field=tss.rsp0" >&2; exit 1;
}
grep -Fq 'tss.ist[1] = (uint64_t)__nmi_ist_stack_end;' "$kernel_source" || {
  echo "error: vector=2 field=tss.ist2" >&2; exit 1;
}
privilege_source="$(sed -n '/^static void privilege_init(void) {$/,/^}$/p' "$kernel_source")"
tss_load_line="$(grep -n -m1 '^[[:space:]]*load_tss();$' <<<"$privilege_source" | cut -d: -f1 || true)"
nmi_gate_line="$(grep -n -m1 'set_gate(2, isr2, 2, 0x8e);' <<<"$privilege_source" | cut -d: -f1 || true)"
idt_load_line="$(grep -n -m1 '__asm__ volatile ("lidt %0"' <<<"$privilege_source" | cut -d: -f1 || true)"
[[ -n "$tss_load_line" && -n "$nmi_gate_line" && -n "$idt_load_line" &&
   "$tss_load_line" -lt "$nmi_gate_line" && "$nmi_gate_line" -lt "$idt_load_line" ]] || {
  echo "error: vector=2 field=publication-order expected=tss-before-ist2-gate-before-lidt" >&2
  exit 1
}
grep -Fq 'if (leanos_entry_demo(descriptor, frame, 0x800000, context, 3) == 0)' \
    "$kernel_source" || {
  echo "error: vector=13 path=generated-model" >&2; exit 1;
}

source_path="$(sed -n '/^isr80:/,/^\.global isr14/p' "$boot_source")"
source_cleanup="$(grep -n -m1 '^[[:space:]]*clac$' <<<"$source_path" | cut -d: -f1)"
source_normalize="$(grep -n -m1 'NORMALIZE_ENTRY 128, 0' <<<"$source_path" | cut -d: -f1)"
source_handler="$(grep -n -m1 'call syscall_handler' <<<"$source_path" | cut -d: -f1)"
[[ -n "$source_cleanup" && -n "$source_normalize" && -n "$source_handler" &&
   "$source_cleanup" -lt "$source_normalize" && "$source_normalize" -lt "$source_handler" ]] || {
  echo "error: vector=128 path=normalization" >&2; exit 1;
}
source_path="$(sed -n '/^isr32:/,/^\/\* The only boot-reachable CPL3 return/p' "$boot_source")"
grep -q '^[[:space:]]*clac$' <<<"$source_path" || {
  echo "error: vector=32 path=cleanup" >&2; exit 1;
}
source_path="$(sed -n '/^isr14:/,/^\.global isr32/p' "$boot_source")"
grep -q 'mov \$1, %esi' <<<"$source_path" || {
  echo "error: vector=14 field=error-shape" >&2; exit 1;
}
for vector in 6 7; do
  if [[ "$vector" == 6 ]]; then
    source_path="$(sed -n '/^isr6:/,/^\.global isr7/p' "$boot_source")"
  else
    source_path="$(sed -n '/^isr7:/,/^\.global isr80/p' "$boot_source")"
  fi
  source_cleanup="$(grep -n -m1 '^[[:space:]]*clac$' <<<"$source_path" | cut -d: -f1 || true)"
  source_normalize="$(grep -n -m1 "NORMALIZE_ENTRY $vector, 0" <<<"$source_path" | cut -d: -f1 || true)"
  source_handler="$(grep -n -m1 'call extended_state_denial_handler' <<<"$source_path" | cut -d: -f1 || true)"
  [[ -n "$source_cleanup" && -n "$source_normalize" && -n "$source_handler" &&
     "$source_cleanup" -lt "$source_normalize" && "$source_normalize" -lt "$source_handler" ]] || {
    echo "error: vector=$vector path=denial" >&2; exit 1;
  }
done

source_path="$(sed -n '/^isr13:/,/^\/\* Vector 8 has/p' "$boot_source")"
source_cleanup="$(grep -n -m1 '^[[:space:]]*clac$' <<<"$source_path" | cut -d: -f1 || true)"
source_normalize="$(grep -n -m1 'call authorize_interrupt_entry' <<<"$source_path" | cut -d: -f1 || true)"
source_handler="$(grep -n -m1 'call entry_adversarial_gp_handler' <<<"$source_path" | cut -d: -f1 || true)"
[[ -n "$source_cleanup" && -n "$source_normalize" && -n "$source_handler" &&
   "$source_cleanup" -lt "$source_normalize" && "$source_normalize" -lt "$source_handler" ]] || {
  echo "error: vector=13 path=normalization" >&2; exit 1;
}

address() { nm -n "$elf" | awk -v name="$1" '$3 == name { print "0x" $1 }'; }
check_path() {
  local vector="$1" start_symbol="$2" stop_symbol="$3" handler="$4"
  local start stop dis cleanup normalize operation
  start="$(address "$start_symbol")"; stop="$(address "$stop_symbol")"
  dis="$(objdump -d --no-show-raw-insn --start-address="$start" --stop-address="$stop" "$elf")"
  cleanup="$(grep -n -m1 -E '[[:space:]]clac$' <<<"$dis" | cut -d: -f1)"
  grep -n -m1 -E '[[:space:]]cld$' <<<"$dis" >/dev/null || {
    echo "error: vector=$vector path=cleanup field=df" >&2; exit 1;
  }
  normalize="$(grep -n -m1 'call.*<authorize_interrupt_entry>' <<<"$dis" | cut -d: -f1)"
  operation="$(grep -n -m1 "call.*<${handler}>" <<<"$dis" | cut -d: -f1)"
  [[ -n "$cleanup" && -n "$normalize" && -n "$operation" &&
     "$cleanup" -lt "$normalize" && "$normalize" -lt "$operation" ]] || {
    echo "error: vector=$vector path=stub violated=handler-before-cleanup-or-normalization" >&2
    exit 1
  }
  grep -Eq '(<complete_interrupt_entry>|user_return_epilogue)' <<<"$dis" || {
    echo "error: vector=$vector path=stub violated=entry-latch-not-completed" >&2; exit 1;
  }
  echo "ENTRY-POLICY vector=$vector target=$start_symbol cleanup=AC,DF normalize=shared handler=$handler result=PASS"
}

check_path 128 isr80 isr14 syscall_handler
check_path 14 isr14 isr32 page_fault_handler
check_path 32 isr32 user_return_epilogue timer_handler

check_denial_path() {
  local vector="$1" start_symbol="$2" stop_symbol="$3"
  local start stop dis cleanup normalize operation
  start="$(address "$start_symbol")"; stop="$(address "$stop_symbol")"
  dis="$(objdump -d --no-show-raw-insn --start-address="$start" --stop-address="$stop" "$elf")"
  cleanup="$(grep -n -m1 -E '[[:space:]]clac$' <<<"$dis" | cut -d: -f1)"
  normalize="$(grep -n -m1 'call.*<authorize_interrupt_entry>' <<<"$dis" | cut -d: -f1)"
  operation="$(grep -n -m1 'call.*<extended_state_denial_handler>' <<<"$dis" | cut -d: -f1)"
  grep -n -m1 -E '[[:space:]]cld$' <<<"$dis" >/dev/null || {
    echo "error: vector=$vector path=cleanup field=df" >&2; exit 1;
  }
  [[ -n "$cleanup" && -n "$normalize" && -n "$operation" &&
     "$cleanup" -lt "$normalize" && "$normalize" -lt "$operation" ]] || {
    echo "error: vector=$vector path=denial violated=handler-before-cleanup-or-normalization" >&2
    exit 1
  }
  echo "ENTRY-POLICY vector=$vector target=$start_symbol cleanup=AC,DF normalize=shared handler=fail-stop result=PASS"
}

check_denial_path 6 isr6 isr7
check_denial_path 7 isr7 isr80
epilogue_dis="$(objdump -d --no-show-raw-insn --start-address="$(address user_return_epilogue)" \
  --stop-address="$(address user_return_iretq)" "$elf")"
grep -q 'call.*<validate_user_return>' <<<"$epilogue_dis" || {
  echo "error: ordinary entry path does not reach the reviewed return gate" >&2; exit 1;
}
grep -Fq 'if (ordinary_entry_active) ordinary_entry_active = 0;' "$kernel_source" || {
  echo "error: reviewed return gate does not consume the entry latch" >&2; exit 1;
}
return_source="$(sed -n '/^void validate_user_return/,/^}/p' "$kernel_source")"
grep -Fq 'check_fast_entry_control();' <<<"$return_source" || {
  echo "error: reviewed return gate omits live fast-entry read-back" >&2; exit 1;
}

echo "Entry manifest, TSS snapshot, and final-ELF paths passed"
