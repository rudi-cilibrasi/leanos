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
for symbol in isr0 isr2 isr3 isr6 isr7 isr13 isr14 isr32 isr80 \
  authorize_interrupt_entry integer_fault_restore_peer \
  divide_error_handler breakpoint_handler \
  complete_interrupt_entry extended_state_denial_handler syscall_handler \
  authorize_page_fault_snapshot page_fault_handler page_fault_diagnostic_handler \
  leanos_authorize_page_fault_snapshot leanos_page_fault_dispatch_transition \
  page_fault_provenance_efer_read invalidate_fixed_fault_page \
  timer_handler entry_stack boot_stack boot_stack_top \
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
grep -Fq '"page_fault_provenance_efer_read:\n"' "$kernel_source" &&
  grep -Fq '"rdmsr" : "=a"(provenance_efer_low)' "$kernel_source" || {
  echo "error: page-fault-provenance EFER source site drifted" >&2; exit 1;
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
page_fault_efer_site="$(
  sed -n '/<page_fault_provenance_efer_read>:/{n;p;q;}' <<<"$control_disassembly"
)"
[[ "$page_fault_efer_site" =~ ^[[:space:]]*[[:xdigit:]]+:[[:space:]]+rdmsr([[:space:]]|$) ]] || {
  echo "error: page-fault-provenance EFER final-ELF site drifted" >&2; exit 1;
}
page_fault_start="$(nm -n "$elf" | awk '$3 == "page_fault_handler" { print "0x" $1 }')"
page_fault_stop="$(nm -n "$elf" | awk '$3 == "divide_error_handler" { print "0x" $1 }')"
page_fault_disassembly="$(
  objdump -d --no-show-raw-insn --start-address="$page_fault_start" \
    --stop-address="$page_fault_stop" "$elf"
)"
[[ "$(grep -Ec '[[:space:]]rdmsr$' <<<"$page_fault_disassembly")" -eq 1 ]] || {
  echo "error: page-fault-provenance EFER final-ELF inventory drifted" >&2; exit 1;
}
final_rdmsr_count="$(grep -Ec '[[:space:]]rdmsr$' <<<"$control_disassembly")"
[[ "$((final_rdmsr_count - 1))" -eq 9 ]] || {
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

[[ "$(grep -Ec 'set_gate\(' "$kernel_source")" -eq 11 ]] || {
  echo "error: vector=77 field=present violated=unexpected-installed-gate-count" >&2; exit 1;
}
grep -Fq 'set_gate(0, isr0, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=0 field=target-ist-or-dpl violated=divide-error-gate" >&2; exit 1;
}
grep -Fq 'set_gate(3, isr3, 0, 0xee);' "$kernel_source" || {
  echo "error: vector=3 field=target-ist-or-dpl violated=breakpoint-gate" >&2; exit 1;
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
# Exactly two DPL3 (0xee) gates are reviewed: the syscall gate (vector 128) and
# the CPL3 software-breakpoint gate (vector 3).  Every other gate stays DPL0.
[[ "$(grep -Ec 'set_gate\([^,]+,[^,]+,[^,]+, 0xee\)' "$kernel_source")" -eq 2 ]] || {
  echo "error: vector=3,128 field=dpl expected=3 violated=extra-or-missing-dpl3-gate" >&2; exit 1;
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
source_capture="$(grep -n -m1 '^[[:space:]]*mov %cr2, %rax$' <<<"$source_path" | cut -d: -f1 || true)"
source_preserve="$(grep -n -m1 '^[[:space:]]*push %rax$' <<<"$source_path" | cut -d: -f1 || true)"
source_normalize="$(grep -n -m1 '^[[:space:]]*call authorize_interrupt_entry$' <<<"$source_path" | cut -d: -f1 || true)"
source_restore="$(grep -n -m1 '^[[:space:]]*mov %rsp, %rdi$' <<<"$source_path" | cut -d: -f1 || true)"
source_handler="$(grep -n -m1 '^[[:space:]]*call authorize_page_fault_snapshot$' <<<"$source_path" | cut -d: -f1 || true)"
source_first_call="$(grep -n -m1 '^[[:space:]]*call ' <<<"$source_path" | cut -d: -f1 || true)"
for symbol in isr14_capture_cr2 isr14_preserve_cr2 isr14_restore_cr2; do
  grep -Fq "${symbol}:" <<<"$source_path" || {
    echo "error: vector=14 field=cr2-sampling-order source" >&2; exit 1;
  }
done
[[ -n "$source_capture" && -n "$source_preserve" && -n "$source_normalize" &&
   -n "$source_restore" && -n "$source_handler" && -n "$source_first_call" &&
   "$source_capture" -lt "$source_preserve" &&
   "$source_preserve" -lt "$source_normalize" &&
   "$source_normalize" -eq "$source_first_call" &&
   "$source_normalize" -lt "$source_restore" &&
   "$source_restore" -lt "$source_handler" ]] || {
  echo "error: vector=14 field=cr2-sampling-order source" >&2; exit 1;
}
[[ "$(grep -Ec '^[[:space:]]*mov %cr2,' "$boot_source")" -eq 1 ]] || {
  echo "error: vector=14 field=cr2-single-sample source" >&2; exit 1;
}
page_fault_adapter_source="$(
  sed -n '/^uint64_t authorize_page_fault_snapshot(/,/^}$/p' "$kernel_source"
)"
source_generated="$(grep -n -m1 'leanos_authorize_page_fault_snapshot(' \
  <<<"$page_fault_adapter_source" | cut -d: -f1 || true)"
source_invalidation="$(grep -n -m1 'invalidate_fixed_fault_page();' \
  <<<"$page_fault_adapter_source" | cut -d: -f1 || true)"
source_agreement="$(grep -n -m1 'leanos_page_fault_dispatch_transition(' \
  <<<"$page_fault_adapter_source" | cut -d: -f1 || true)"
source_operation="$(grep -n -m1 'page_fault_handler(&transition)' \
  <<<"$page_fault_adapter_source" | cut -d: -f1 || true)"
source_diagnostic_operation="$(grep -n -m1 'page_fault_diagnostic_handler(&transition)' \
  <<<"$page_fault_adapter_source" | cut -d: -f1 || true)"
grep -Fq 'const struct page_fault_entry_record snapshot = {' \
  <<<"$page_fault_adapter_source" || {
  echo "error: vector=14 field=immutable-snapshot source" >&2; exit 1;
}
grep -Fq 'const struct page_fault_transition transition = {' \
  <<<"$page_fault_adapter_source" &&
  grep -Fq '.kind = (enum page_fault_transition_kind)(route >> 56)' \
    <<<"$page_fault_adapter_source" &&
  grep -Fq '.result = route & UINT64_C(0x00ffffffffffffff)' \
    <<<"$page_fault_adapter_source" &&
  grep -Fq '.snapshot = &snapshot' <<<"$page_fault_adapter_source" &&
  grep -Fq 'switch (transition.kind) {' <<<"$page_fault_adapter_source" &&
  grep -Fq 'case PAGE_FAULT_TRANSITION_FATAL:' <<<"$page_fault_adapter_source" &&
  grep -Fq 'fail("page-fault-fatal");' <<<"$page_fault_adapter_source" &&
  grep -Fq 'case PAGE_FAULT_TRANSITION_REJECTED:' <<<"$page_fault_adapter_source" &&
  grep -Fq 'fail("page-fault-rejected");' \
    <<<"$page_fault_adapter_source" || {
  echo "error: vector=14 field=typed-generated-route source" >&2; exit 1;
}
generated_arguments="$(
  sed -n '/leanos_authorize_page_fault_snapshot(/,/trusted_stack_identity)/p' \
    <<<"$page_fault_adapter_source" | tr -d '[:space:]' |
    sed 's/^.*leanos_authorize/leanos_authorize/'
)"
expected_arguments='leanos_authorize_page_fault_snapshot(snapshot.version,snapshot.vector,snapshot.error,snapshot.fault_address,snapshot.fault_page,snapshot.access,snapshot.protection,snapshot.user,snapshot.current_subject,snapshot.active_address_space,snapshot.active_cr3,snapshot.paging_controls,snapshot.rip,snapshot.saved_cs,snapshot.rflags,snapshot.user_rsp,snapshot.user_ss,snapshot.stack_identity,snapshot.reserved,trusted_subject,active_address_space,cr3,paging_controls,trusted_stack_identity);'
[[ "$generated_arguments" == "$expected_arguments" ]] || {
  echo "error: vector=14 field=generated-full-record-binding source" >&2; exit 1;
}
agreement_arguments="$(
  sed -n '/leanos_page_fault_dispatch_transition(/,/saved_context_owner_b);/p' \
    <<<"$page_fault_adapter_source" | tr -d '[:space:]' |
    sed 's/^.*leanos_page/leanos_page/'
)"
invalidation_helper_source="$(
  sed -n '/^static void invalidate_fixed_fault_page(void) {/,/^}/p' \
    "$kernel_source"
)"
expected_agreement_arguments='leanos_page_fault_dispatch_transition(snapshot.version,snapshot.vector,snapshot.error,snapshot.fault_address,snapshot.fault_page,snapshot.access,snapshot.protection,snapshot.user,snapshot.current_subject,snapshot.active_address_space,snapshot.active_cr3,snapshot.paging_controls,snapshot.rip,snapshot.saved_cs,snapshot.rflags,snapshot.user_rsp,snapshot.user_ss,snapshot.stack_identity,snapshot.reserved,trusted_subject,active_address_space,cr3,paging_controls,trusted_stack_identity,canonical,supervisor_probe,(uint64_t)wp_probe_instruction,(uint64_t)wp_probe_target,(uint64_t)wp_probe_recovered,(uint64_t)user_a_entry,(uint64_t)user_a_entry,(uint64_t)smep_probe_recovered,(uint64_t)smap_probe_instruction,(uint64_t)user_a_stack,(uint64_t)smap_probe_recovered,active_address_space,(uint64_t)root,active_address_space,(uint64_t)root,report_agrees,expected_leaf,live_leaf,current_subject==snapshot.current_subject,1,current_subject,active_address_space,active_address_space,active_address_space,0,0,checked_exact_fault_page_invalidation,current_subject,active_address_space,saved_context_owner_b,saved_context_owner_b);'
[[ "$agreement_arguments" == "$expected_agreement_arguments" ]] || {
  echo "error: vector=14 field=diagnostic-and-strengthened-agreement-inputs source" >&2; exit 1;
}
grep -Fq 'user && snapshot.fault_address == 0 && snapshot.fault_page == 0 &&' \
    <<<"$page_fault_adapter_source" &&
  grep -Fq 'snapshot.error == 5 && snapshot.access == 0 &&' \
    <<<"$page_fault_adapter_source" &&
  grep -Fq 'snapshot.protection == 1;' <<<"$page_fault_adapter_source" &&
  grep -Fq 'invalidate_fixed_fault_page();' <<<"$page_fault_adapter_source" &&
  grep -Fq 'static void invalidate_fixed_fault_page(void)' \
    <<<"$invalidation_helper_source" &&
  grep -Fq 'const uint64_t fixed_page_address = 0;' \
    <<<"$invalidation_helper_source" &&
  grep -Fq '"invlpg (%0)" : : "r"(fixed_page_address) : "memory");' \
    <<<"$invalidation_helper_source" &&
  ! grep -Fq 'page_fault_tlb_flush_cr3' "$kernel_source" || {
  echo "error: vector=14 field=exact-fault-page-invalidation source" >&2; exit 1;
}
snapshot_mutations="$(
  grep -E 'snapshot\.(version|vector|error|fault_address|fault_page|access|protection|user|current_subject|active_address_space|active_cr3|paging_controls|rip|saved_cs|rflags|user_rsp|user_ss|stack_identity|reserved)[[:space:]]*(\\+\\+|--|[+*/%^|&-]?=)' \
    <<<"$page_fault_adapter_source" | grep -Ev '==|!=|<=|>=' || true
)"
if [[ -n "$snapshot_mutations" ]]; then
  echo "error: vector=14 field=immutable-snapshot source" >&2; exit 1
fi
[[ -n "$source_generated" && -n "$source_invalidation" && -n "$source_agreement" &&
   -n "$source_operation" && -n "$source_diagnostic_operation" &&
   "$source_generated" -lt "$source_agreement" &&
   "$source_generated" -lt "$source_invalidation" &&
   "$source_invalidation" -lt "$source_agreement" &&
   "$source_agreement" -lt "$source_operation" &&
   "$source_agreement" -lt "$source_diagnostic_operation" ]] || {
  echo "error: vector=14 path=generated-agreement-before-handler source" >&2
  exit 1
}
[[ "$(grep -Fc 'page_fault_handler(&transition)' "$kernel_source")" -eq 1 ]] || {
  echo "error: vector=14 path=raw-or-direct-handler source" >&2; exit 1;
}
[[ "$(grep -Fc 'page_fault_diagnostic_handler(&transition)' "$kernel_source")" -eq 1 ]] || {
  echo "error: vector=14 path=raw-or-direct-diagnostic-handler source" >&2; exit 1;
}
page_fault_diagnostic_source="$(
  sed -n '/^uint64_t page_fault_diagnostic_handler(/,/^}$/p' "$kernel_source"
)"
grep -Fq 'const uint64_t recovery = transition->result &' \
    <<<"$page_fault_diagnostic_source" &&
  grep -Fq 'const uint64_t completed_state = transition->result >> 48;' \
    <<<"$page_fault_diagnostic_source" &&
  grep -Fq 'supervisor_probe = (unsigned)completed_state;' \
    <<<"$page_fault_diagnostic_source" &&
  grep -Fq 'return recovery;' <<<"$page_fault_diagnostic_source" &&
  ! grep -Fq 'transition->snapshot' <<<"$page_fault_diagnostic_source" || {
  echo "error: vector=14 field=typed-diagnostic-recovery source" >&2; exit 1;
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
check_path 14 isr14 isr32 authorize_page_fault_snapshot
check_path 32 isr32 user_return_epilogue timer_handler

page_fault_disassembly="$(
  objdump -d --no-show-raw-insn \
    --start-address="$(address isr14)" --stop-address="$(address isr32)" "$elf"
)"
elf_capture="$(grep -n -m1 '<isr14_capture_cr2>:' \
  <<<"$page_fault_disassembly" | cut -d: -f1 || true)"
elf_preserve="$(grep -n -m1 '<isr14_preserve_cr2>:' \
  <<<"$page_fault_disassembly" | cut -d: -f1 || true)"
elf_normalize="$(grep -n -m1 'call.*<authorize_interrupt_entry>' \
  <<<"$page_fault_disassembly" | cut -d: -f1 || true)"
elf_restore="$(grep -n -m1 '<isr14_restore_cr2>:' \
  <<<"$page_fault_disassembly" | cut -d: -f1 || true)"
elf_handler="$(grep -n -m1 'call.*<authorize_page_fault_snapshot>' \
  <<<"$page_fault_disassembly" | cut -d: -f1 || true)"
elf_first_call="$(grep -n -m1 -E '[[:space:]]call[[:space:]]' \
  <<<"$page_fault_disassembly" | cut -d: -f1 || true)"
elf_capture_site="$(sed -n '/<isr14_capture_cr2>:/{n;p;q;}' \
  <<<"$page_fault_disassembly")"
elf_preserve_site="$(sed -n '/<isr14_preserve_cr2>:/{n;p;q;}' \
  <<<"$page_fault_disassembly")"
elf_restore_site="$(sed -n '/<isr14_restore_cr2>:/{n;p;q;}' \
  <<<"$page_fault_disassembly")"
[[ "$elf_capture_site" =~ [[:space:]]mov[[:space:]]+%cr2,[[:space:]]*%rax$ &&
   "$elf_preserve_site" =~ [[:space:]]push[[:space:]]+%rax$ &&
   "$elf_restore_site" =~ [[:space:]]mov[[:space:]]+%rsp,[[:space:]]*%rdi$ ]] || {
  echo "error: vector=14 field=cr2-sampling-order final-elf" >&2; exit 1;
}
for symbol in isr14_capture_cr2 isr14_preserve_cr2 isr14_restore_cr2; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: vector=14 field=cr2-sampling-order final-elf" >&2; exit 1;
  }
done
[[ -n "$elf_capture" && -n "$elf_preserve" && -n "$elf_normalize" &&
   -n "$elf_restore" && -n "$elf_handler" && -n "$elf_first_call" &&
   "$elf_capture" -lt "$elf_preserve" && "$elf_preserve" -lt "$elf_normalize" &&
   "$elf_normalize" -eq "$elf_first_call" && "$elf_normalize" -lt "$elf_restore" &&
   "$elf_restore" -lt "$elf_handler" ]] || {
  echo "error: vector=14 field=cr2-sampling-order final-elf" >&2; exit 1;
}
[[ "$(grep -Ec '[[:space:]]mov[[:space:]]+%cr2,' <<<"$page_fault_disassembly")" -eq 1 ]] || {
  echo "error: vector=14 field=cr2-single-sample final-elf" >&2; exit 1;
}
page_fault_adapter_disassembly="$(
  objdump -d --no-show-raw-insn \
    --start-address="$(address authorize_page_fault_snapshot)" \
    --stop-address="$(address divide_error_handler)" "$elf"
)"
elf_generated="$(grep -n -m1 'call.*<leanos_authorize_page_fault_snapshot>' \
  <<<"$page_fault_adapter_disassembly" | cut -d: -f1 || true)"
elf_invalidation="$(grep -n -m1 'call.*<invalidate_fixed_fault_page>' \
  <<<"$page_fault_adapter_disassembly" | cut -d: -f1 || true)"
elf_agreement="$(grep -n -m1 'call.*<leanos_page_fault_dispatch_transition>' \
  <<<"$page_fault_adapter_disassembly" | cut -d: -f1 || true)"
elf_operation="$(grep -n -m1 'call.*<page_fault_handler>' \
  <<<"$page_fault_adapter_disassembly" | cut -d: -f1 || true)"
elf_diagnostic_operation="$(grep -n -m1 'call.*<page_fault_diagnostic_handler>' \
  <<<"$page_fault_adapter_disassembly" | cut -d: -f1 || true)"
invalidation_start="$(address invalidate_fixed_fault_page)"
invalidation_stop="$(nm -n "$elf" | awk -v start="${invalidation_start#0x}" '
  $1 == start { found = 1; next }
  found && NF >= 3 { print "0x" $1; exit }
')"
[[ -n "$invalidation_stop" ]] || {
  echo "error: vector=14 field=exact-fault-page-invalidation final-elf" >&2
  exit 1
}
elf_invalidation_disassembly="$(
  objdump -d --no-show-raw-insn \
    --start-address="$invalidation_start" \
    --stop-address="$invalidation_stop" "$elf"
)"
elf_invalidation_site="$(grep -m1 -E '[[:space:]]invlpg[[:space:]]' \
  <<<"$elf_invalidation_disassembly")"
mapfile -t elf_invalidation_instructions < <(
  awk '/^[[:space:]]*[[:xdigit:]]+:/ {
    sub(/^[[:space:]]*[[:xdigit:]]+:[[:space:]]*/, "")
    print
  }' <<<"$elf_invalidation_disassembly"
)
elf_invalidation_zero_bound=0
for ((i = 1; i < ${#elf_invalidation_instructions[@]}; i++)); do
  if [[ "${elf_invalidation_instructions[$i]}" == 'invlpg (%rax)' &&
        "${elf_invalidation_instructions[$((i - 1))]}" == 'xor    %eax,%eax' ]]; then
    elf_invalidation_zero_bound=1
  fi
done
[[ "$elf_invalidation_site" =~ [[:space:]]invlpg[[:space:]]+\(%rax\)$ &&
   "$elf_invalidation_zero_bound" -eq 1 ]] || {
  echo "error: vector=14 field=exact-fault-page-invalidation final-elf" >&2
  exit 1
}
[[ -n "$elf_generated" && -n "$elf_invalidation" && -n "$elf_agreement" &&
   -n "$elf_operation" && -n "$elf_diagnostic_operation" &&
   "$elf_generated" -lt "$elf_invalidation" &&
   "$elf_invalidation" -lt "$elf_agreement" &&
   "$elf_agreement" -lt "$elf_operation" &&
   "$elf_agreement" -lt "$elf_diagnostic_operation" ]] || {
  echo "error: vector=14 path=generated-agreement-before-handler final-elf" >&2
  exit 1
}
[[ "$(grep -Ec 'call.*<page_fault_handler>' <<<"$control_disassembly")" -eq 1 ]] || {
  echo "error: vector=14 path=raw-or-direct-handler final-elf" >&2; exit 1;
}
[[ "$(grep -Ec 'call.*<page_fault_diagnostic_handler>' <<<"$control_disassembly")" -eq 1 ]] || {
  echo "error: vector=14 path=raw-or-direct-diagnostic-handler final-elf" >&2
  exit 1
}
for generated_symbol in leanos_authorize_page_fault_snapshot \
    leanos_page_fault_dispatch_transition; do
  generated_start="$(address "$generated_symbol")"
  generated_stop="$(nm -n "$elf" | awk -v start="${generated_start#0x}" '
    $1 == start { found = 1; next }
    found && NF >= 3 { print "0x" $1; exit }
  ')"
  [[ -n "$generated_stop" ]] || {
    echo "error: vector=14 field=allocation-free-generated final-elf symbol=$generated_symbol" >&2
    exit 1
  }
  generated_disassembly="$(
    objdump -d --no-show-raw-insn --start-address="$generated_start" \
      --stop-address="$generated_stop" "$elf"
  )"
  if grep -Eq 'call.*<lean_(alloc|box|ctor|mk|inc|dec)' \
      <<<"$generated_disassembly"; then
    echo "error: vector=14 field=allocation-free-generated final-elf symbol=$generated_symbol" >&2
    exit 1
  fi
done

# The contained integer-fault stubs clear AC/DF, normalize through the shared
# manifest adapter, then call only the generated typed dispatcher before the
# shared cleanup/return path.  Neither reaches an operation-specific handler or
# returns before cleanup and normalization, and both converge on the single
# validated epilogue via the shared restore.
check_contained_path() {
  local vector="$1" start_symbol="$2" stop_symbol="$3" handler="$4"
  local start stop dis cleanup normalize operation restore
  start="$(address "$start_symbol")"; stop="$(address "$stop_symbol")"
  dis="$(objdump -d --no-show-raw-insn --start-address="$start" --stop-address="$stop" "$elf")"
  cleanup="$(grep -n -m1 -E '[[:space:]]clac$' <<<"$dis" | cut -d: -f1)"
  grep -n -m1 -E '[[:space:]]cld$' <<<"$dis" >/dev/null || {
    echo "error: vector=$vector path=cleanup field=df" >&2; exit 1;
  }
  normalize="$(grep -n -m1 'call.*<authorize_interrupt_entry>' <<<"$dis" | cut -d: -f1)"
  operation="$(grep -n -m1 "call.*<${handler}>" <<<"$dis" | cut -d: -f1)"
  restore="$(grep -n -m1 'jmp.*<integer_fault_restore_peer>' <<<"$dis" | cut -d: -f1)"
  [[ -n "$cleanup" && -n "$normalize" && -n "$operation" && -n "$restore" &&
     "$cleanup" -lt "$normalize" && "$normalize" -lt "$operation" &&
     "$operation" -lt "$restore" ]] || {
    echo "error: vector=$vector path=stub violated=handler-before-cleanup-or-normalization" >&2
    exit 1
  }
  echo "ENTRY-POLICY vector=$vector target=$start_symbol cleanup=AC,DF normalize=shared handler=$handler result=PASS"
}
check_contained_path 0 isr0 isr3 divide_error_handler
check_contained_path 3 isr3 integer_fault_restore_peer breakpoint_handler
restore_dis="$(objdump -d --no-show-raw-insn \
  --start-address="$(address integer_fault_restore_peer)" \
  --stop-address="$(address user_a_entry)" "$elf")"
grep -Eq 'call.*<complete_interrupt_entry>' <<<"$restore_dis" || {
  echo "error: vector=0,3 path=restore violated=entry-latch-not-completed" >&2; exit 1;
}
grep -Eq 'jmp.*<user_return_epilogue>' <<<"$restore_dis" || {
  echo "error: vector=0,3 path=restore violated=return-not-validated" >&2; exit 1;
}

# Source-ordering gate for the two contained integer-fault stubs: each must
# clear AC before it normalizes through the shared manifest adapter, and it must
# not reach its operation-specific handler until after that normalization.  This
# rejects a source-level handler-before-cleanup or direct-called handler that a
# final-ELF disassembly of the shipped image would otherwise not exhibit.
for vector in 0 3; do
  if [[ "$vector" == 0 ]]; then
    source_path="$(sed -n '/^isr0:/,/^\.global isr3/p' "$boot_source")"
    handler=divide_error_handler
  else
    source_path="$(sed -n '/^isr3:/,/^\.global integer_fault_restore_peer/p' "$boot_source")"
    handler=breakpoint_handler
  fi
  source_cleanup="$(grep -n -m1 '^[[:space:]]*clac$' <<<"$source_path" | cut -d: -f1 || true)"
  source_normalize="$(grep -n -m1 "NORMALIZE_ENTRY $vector, 0" <<<"$source_path" | cut -d: -f1 || true)"
  source_handler="$(grep -n -m1 "call $handler" <<<"$source_path" | cut -d: -f1 || true)"
  [[ -n "$source_cleanup" && -n "$source_normalize" && -n "$source_handler" &&
     "$source_cleanup" -lt "$source_normalize" && "$source_normalize" -lt "$source_handler" ]] || {
    echo "error: vector=$vector path=contained" >&2; exit 1;
  }
done

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
