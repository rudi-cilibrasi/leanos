#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
nx_elf="${2:-build/boot/leanos-fault-nx-execute.elf}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp boot/kernel.c "$tmp/kernel.c"
  cp boot/boot.S "$tmp/boot.S"
  "$@"
  if LEANOS_ENTRY_KERNEL_SOURCE="$tmp/kernel.c" \
      LEANOS_ENTRY_BOOT_SOURCE="$tmp/boot.S" \
      ./scripts/check-entry-policy.sh "$elf" >"$tmp/$name.log" 2>&1; then
    echo "error: entry-policy fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: entry-policy fixture '$name' lacked '$expected'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
  echo "ENTRY-POLICY fixture=$name $expected result=REJECTED"
}

run_page_fault_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp boot/kernel.c "$tmp/kernel.c"
  cp boot/boot.S "$tmp/boot.S"
  "$@"
  if LEANOS_PAGE_FAULT_PROBE=supervisor-read \
      LEANOS_ENTRY_KERNEL_SOURCE="$tmp/kernel.c" \
      LEANOS_ENTRY_BOOT_SOURCE="$tmp/boot.S" \
      ./scripts/check-entry-policy.sh "$elf" >"$tmp/$name.log" 2>&1; then
    echo "error: page-fault site fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: page-fault site fixture '$name' lacked '$expected'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
  echo "ENTRY-POLICY fixture=$name $expected result=REJECTED"
}

run_nx_page_fault_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp boot/kernel.c "$tmp/kernel.c"
  cp boot/boot.S "$tmp/boot.S"
  "$@"
  if LEANOS_PAGE_FAULT_PROBE=nx-execute \
      LEANOS_ENTRY_KERNEL_SOURCE="$tmp/kernel.c" \
      LEANOS_ENTRY_BOOT_SOURCE="$tmp/boot.S" \
      ./scripts/check-entry-policy.sh "$nx_elf" >"$tmp/$name.log" 2>&1; then
    echo "error: NX page-fault site fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: NX page-fault site fixture '$name' lacked '$expected'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
  echo "ENTRY-POLICY fixture=$name $expected result=REJECTED"
}

wrong_target() { sed -i 's/set_gate(14, isr14,/set_gate(14, isr32,/' "$tmp/kernel.c"; }
ambient_initial_rflags() {
  sed -i 's/pushq \$0x216/pushfq/' "$tmp/boot.S"
}
nmi_wrong_target() { sed -i 's/set_gate(2, isr2,/set_gate(2, isr8,/' "$tmp/kernel.c"; }
nmi_wrong_ist() { sed -i 's/set_gate(2, isr2, 2,/set_gate(2, isr2, 1,/' "$tmp/kernel.c"; }
nmi_dpl3() { sed -i 's/set_gate(2, isr2, 2, 0x8e)/set_gate(2, isr2, 2, 0xee)/' "$tmp/kernel.c"; }
nmi_wrong_tss() { sed -i 's/tss.ist\[1\] = (uint64_t)__nmi_ist_stack_end;/tss.ist[1] = (uint64_t)__df_ist_stack_end;/' "$tmp/kernel.c"; }
nmi_late_tss() {
  sed -i '/^[[:space:]]*load_tss();$/d; /__asm__ volatile ("lidt %0"/a\    load_tss();' "$tmp/kernel.c"
}
wrong_ud_target() { sed -i 's/set_gate(6, isr6,/set_gate(6, isr7,/' "$tmp/kernel.c"; }
wrong_nm_target() { sed -i 's/set_gate(7, isr7,/set_gate(7, isr6,/' "$tmp/kernel.c"; }
wrong_gp_target() { sed -i 's/set_gate(13, isr13,/set_gate(13, isr14,/' "$tmp/kernel.c"; }
page_fault_dpl3() { sed -i 's/set_gate(14, isr14, 0, 0x8e)/set_gate(14, isr14, 0, 0xee)/' "$tmp/kernel.c"; }
timer_dpl3() { sed -i 's/set_gate(32, isr32, 0, 0x8e)/set_gate(32, isr32, 0, 0xee)/' "$tmp/kernel.c"; }
extra_present() { sed -i '/set_gate(13, isr13/a\    set_gate(77, isr13, 0, 0x8e);' "$tmp/kernel.c"; }
swapped_error_shape() { sed -i '/^isr14:/,/^\.global isr32/ s/mov \$1, %esi/mov $0, %esi/' "$tmp/boot.S"; }
branch_cleanup() { sed -i '/^isr32_clac:/,/^isr32_cld:/ s/^[[:space:]]*clac$/    nop/' "$tmp/boot.S"; }
branch_nm_cleanup() { sed -i '/^isr7:/,/^\.global isr80/ s/^[[:space:]]*clac$/    nop/' "$tmp/boot.S"; }
branch_ud_cleanup() { sed -i '/^isr6:/,/^\.global isr7/ s/^[[:space:]]*clac$/    nop/' "$tmp/boot.S"; }
ud_before_normalize() { sed -i '/NORMALIZE_ENTRY 6, 0/i\    call extended_state_denial_handler' "$tmp/boot.S"; }
nm_before_normalize() { sed -i '/NORMALIZE_ENTRY 7, 0/i\    call extended_state_denial_handler' "$tmp/boot.S"; }
c_before_normalize() { sed -i '/NORMALIZE_ENTRY 128, 0/i\    call syscall_handler' "$tmp/boot.S"; }
gp_before_normalize() {
  sed -i '/^isr13:/,/^\.global isr8/{
    /call authorize_interrupt_entry/i\    call entry_adversarial_gp_handler
  }' "$tmp/boot.S"
}
gp_model_bypass() {
  sed -i 's/if (leanos_entry_demo(descriptor/if (vector != 13 \&\& leanos_entry_demo(descriptor/' "$tmp/kernel.c"
}
wrong_tss_stack() { sed -i 's/tss.rsp0 = (uint64_t)__entry_stack_end;/tss.rsp0 = (uint64_t)boot_stack_top;/' "$tmp/kernel.c"; }
inherited_sce() { sed -i 's/and \$~1, %eax/nop/' "$tmp/boot.S"; }
omitted_fast_entry_readback() { sed -i 's/check_fast_entry_control();/\/\* omitted fixture \*\//' "$tmp/kernel.c"; }
omitted_fast_entry_cpuid() { sed -i 's/check_fast_entry_cpuid();/\/\* omitted fixture \*\//' "$tmp/kernel.c"; }
wrong_fast_entry_vendor() { sed -i 's/0x68747541/0x68747542/' "$tmp/kernel.c"; }
missing_fast_entry_long_mode() { sed -i 's/(leaf_d >> 29)/(leaf_d >> 28)/' "$tmp/kernel.c"; }
extra_fast_entry_write() { sed -i '/normalize_fast_entry_sysenter_eip_write:/a\    wrmsr' "$tmp/boot.S"; }
relocated_fast_entry_write() {
  sed -i '/normalize_fast_entry_lstar_write:/{n;s/wrmsr/nop/}; /normalize_fast_entry_sysenter_eip_write:/i\    wrmsr' "$tmp/boot.S"
}
relocated_fast_entry_read() {
  sed -i '/read_fast_entry_lstar:/{n;s/rdmsr/nop/}; /\.global enable_smep/i\    rdmsr' "$tmp/boot.S"
}
extra_fast_entry_read() {
  sed -i '/\.global enable_smep/i\    rdmsr' "$tmp/boot.S"
}
unlabeled_page_fault_efer_read() {
  sed -i 's/page_fault_provenance_efer_read/page_fault_provenance_efer_unreviewed/g' \
    "$tmp/kernel.c"
}
late_page_fault_cr2_capture() {
  sed -i '/^isr14:/,/^\\.global isr32/{
    /mov %cr2, %rax/s//nop/
    /call authorize_interrupt_entry/a\    mov %cr2, %rax
  }' "$tmp/boot.S"
}
second_page_fault_cr2_capture() {
  sed -i '/^isr14:/,/^\\.global isr32/{
    /call authorize_page_fault_snapshot/i\    mov %cr2, %rax
  }' "$tmp/boot.S"
}
direct_page_fault_handler() {
  sed -i 's/call authorize_page_fault_snapshot/call page_fault_handler/' "$tmp/boot.S"
}
page_fault_handler_before_generated() {
  sed -i '/const uint64_t route = leanos_page_fault_dispatch_transition(/i\
    page_fault_handler(&transition);' "$tmp/kernel.c"
}
page_fault_fatal_route_to_handler() {
  sed -i '/case PAGE_FAULT_TRANSITION_FATAL:/,/case PAGE_FAULT_TRANSITION_REJECTED:/s/fail("page-fault-fatal");/return page_fault_handler(\&transition);/' \
    "$tmp/kernel.c"
}
page_fault_live_leaf_bypass() {
  sed -i '/expected_leaf, live_leaf,/s/expected_leaf, live_leaf/expected_leaf, expected_leaf/' \
    "$tmp/kernel.c"
}
page_fault_exact_invalidation_bypass() {
  sed -i '/0, 0, checked_exact_fault_page_invalidation,/s/checked_exact_fault_page_invalidation/1/' \
    "$tmp/kernel.c"
}
page_fault_forged_diagnostic_purpose() {
  sed -i 's/canonical, supervisor_probe,/canonical, 1,/' "$tmp/kernel.c"
}
page_fault_wrong_invalidation_target() {
  sed -i 's/invalidate_snapshot_fault_page(&snapshot);/invalidate_snapshot_fault_page((const struct page_fault_entry_record *)((const char *)\&snapshot + 8));/' \
    "$tmp/kernel.c"
}
page_fault_reserved_wrong_error() {
  sed -i \
    '/page_fault_probe_class == 3/,/: page_fault_probe_class == 4/s/snapshot.error == 12/snapshot.error == 13/' \
    "$tmp/kernel.c"
}
page_fault_reserved_wrong_rip() {
  sed -i \
    '/page_fault_probe_class == 3/,/: page_fault_probe_class == 4/s/user_a_reserved_fault_instruction/user_a_nx_fault_instruction/' \
    "$tmp/kernel.c"
}
page_fault_refilled_after_recorded_reload() {
  sed -i '/const uint64_t route = leanos_page_fault_dispatch_transition(/i\
    const uint64_t recorded_reload_cr3 = cr3;\
    const uint64_t translation_refilled_after_reload = 1;\
    const uint64_t stale_reload_claim =\
        recorded_reload_cr3 == cr3 && translation_refilled_after_reload;' \
    "$tmp/kernel.c"
  sed -i '/0, 0, checked_exact_fault_page_invalidation,/s/checked_exact_fault_page_invalidation/stale_reload_claim/' \
    "$tmp/kernel.c"
}
mutate_page_fault_rip_after_authorization() {
  sed -i '/if (snapshot.active_address_space == 0/i\
    snapshot.rip ^= 1;' "$tmp/kernel.c"
}
page_fault_wrong_instruction() {
  sed -i '/^user_a_fault_instruction:$/{n;s/mov 0, %rax/mov 8, %rax/}' \
    "$tmp/boot.S"
}
page_fault_indirect_entry() {
  sed -i '0,/jmp user_a_fault_instruction/s//jmp *%rax/' "$tmp/boot.S"
}
page_fault_wrong_handler_binding() {
  sed -i \
    's/page_fault_probe_class == 1 ? 7u : 5u/page_fault_probe_class == 1 ? 5u : 5u/' \
    "$tmp/kernel.c"
}
page_fault_nx_wrong_payload() {
  sed -i \
    's/movl \$0x000000ff, user_a_nx_fault_instruction+1/movl $0x000000fe, user_a_nx_fault_instruction+1/' \
    "$tmp/boot.S"
}
page_fault_nx_indirect_branch() {
  sed -i 's/jmp user_a_nx_fault_instruction/jmp *%rax/' "$tmp/boot.S"
}
page_fault_nx_wrong_handler_binding() {
  sed -i \
    's/page_fault_probe_class == 2 ? 21u/page_fault_probe_class == 2 ? 5u/' \
    "$tmp/kernel.c"
}
page_fault_c_only_snapshot_route() {
  sed -i \
    's/&snapshot, canonical, route, expected_leaf, live_leaf);/\&snapshot, 1, UINT64_C(0x01000000ff020202), expected_leaf, live_leaf);/' \
    "$tmp/kernel.c"
}
stale_lstar() { sed -i '/normalize_fast_entry_lstar_write:/i\    mov $user_a_text, %eax' "$tmp/boot.S"; }
noncanonical_lstar() { sed -i '/normalize_fast_entry_lstar_write:/i\    mov $0x00008000, %edx' "$tmp/boot.S"; }
non_denying_sysenter() { sed -i '/normalize_fast_entry_sysenter_cs_write:/i\    mov $1, %eax' "$tmp/boot.S"; }
omitted_return_readback() { sed -i '/^void validate_user_return/,/^}/ s/check_fast_entry_control();/\/\* omitted return fixture \*\//' "$tmp/kernel.c"; }
missing_de_gate() { sed -i '/set_gate(0, isr0, 0, 0x8e);/d' "$tmp/kernel.c"; }
missing_bp_gate() { sed -i '/set_gate(3, isr3, 0, 0xee);/d' "$tmp/kernel.c"; }
de_extra_gate() { sed -i '/set_gate(0, isr0, 0, 0x8e);/a\    set_gate(1, isr0, 0, 0x8e);' "$tmp/kernel.c"; }
swap_de_bp_targets() {
  sed -i -e 's/set_gate(0, isr0, 0, 0x8e);/set_gate(0, isr3, 0, 0x8e);/' \
    -e 's/set_gate(3, isr3, 0, 0xee);/set_gate(3, isr0, 0, 0xee);/' "$tmp/kernel.c"
}
de_user_callable() { sed -i 's/set_gate(0, isr0, 0, 0x8e);/set_gate(0, isr0, 0, 0xee);/' "$tmp/kernel.c"; }
de_wrong_ist() { sed -i 's/set_gate(0, isr0, 0, 0x8e);/set_gate(0, isr0, 1, 0x8e);/' "$tmp/kernel.c"; }
de_wrong_type() { sed -i 's/set_gate(0, isr0, 0, 0x8e);/set_gate(0, isr0, 0, 0x8f);/' "$tmp/kernel.c"; }
bp_wrong_dpl() { sed -i 's/set_gate(3, isr3, 0, 0xee);/set_gate(3, isr3, 0, 0x8e);/' "$tmp/kernel.c"; }
de_before_normalize() { sed -i '/NORMALIZE_ENTRY 0, 0/i\    call divide_error_handler' "$tmp/boot.S"; }
bp_before_normalize() { sed -i '/NORMALIZE_ENTRY 3, 0/i\    call breakpoint_handler' "$tmp/boot.S"; }
de_branch_cleanup() { sed -i '/^isr0:/,/^\.global isr3/ s/^[[:space:]]*clac$/    nop/' "$tmp/boot.S"; }

run_fixture wrong-target 'vector=14 field=target-or-dpl' wrong_target
run_fixture ambient-initial-rflags \
  'initial-user-rflags source is not the canonical 0x216 word' \
  ambient_initial_rflags
run_fixture nmi-wrong-target 'vector=2 field=target-ist-or-dpl' nmi_wrong_target
run_fixture nmi-wrong-ist 'vector=2 field=target-ist-or-dpl' nmi_wrong_ist
run_fixture nmi-dpl3 'vector=2 field=target-ist-or-dpl' nmi_dpl3
run_fixture nmi-wrong-tss 'vector=2 field=tss.ist2' nmi_wrong_tss
run_fixture nmi-late-tss 'vector=2 field=publication-order expected=tss-before-ist2-gate-before-lidt' nmi_late_tss
run_fixture wrong-ud-target 'vector=6 field=target-or-dpl' wrong_ud_target
run_fixture wrong-nm-target 'vector=7 field=target-or-dpl' wrong_nm_target
run_fixture wrong-gp-target 'vector=13 field=target-or-dpl' wrong_gp_target
run_fixture page-fault-dpl3 'vector=14 field=target-or-dpl' page_fault_dpl3
run_fixture timer-dpl3 'vector=32 field=target-or-dpl' timer_dpl3
run_fixture extra-present 'vector=77 field=present' extra_present
run_fixture swapped-error-shape 'vector=14 field=error-shape' swapped_error_shape
run_fixture branch-around-cleanup 'vector=32 path=cleanup' branch_cleanup
run_fixture branch-around-ud-cleanup 'vector=6 path=denial' branch_ud_cleanup
run_fixture branch-around-nm-cleanup 'vector=7 path=denial' branch_nm_cleanup
run_fixture ud-handler-before-normalize 'vector=6 path=denial' ud_before_normalize
run_fixture nm-handler-before-normalize 'vector=7 path=denial' nm_before_normalize
run_fixture c-before-normalize 'vector=128 path=normalization' c_before_normalize
run_fixture gp-handler-before-normalize 'vector=13 path=normalization' gp_before_normalize
run_fixture gp-generated-model-bypass 'vector=13 path=generated-model' gp_model_bypass
run_fixture wrong-tss-stack 'vector=128 field=tss.rsp0' wrong_tss_stack
run_fixture inherited-sce 'fast-entry control does not clear EFER.SCE' inherited_sce
run_fixture omitted-fast-entry-readback 'fast-entry control read-back is not boot-reachable' omitted_fast_entry_readback
run_fixture omitted-fast-entry-cpuid 'fast-entry CPUID contract is not boot-reachable' omitted_fast_entry_cpuid
run_fixture wrong-fast-entry-vendor 'fast-entry CPUID contract drifted' wrong_fast_entry_vendor
run_fixture missing-fast-entry-long-mode 'fast-entry CPUID contract drifted' missing_fast_entry_long_mode
run_fixture extra-fast-entry-write 'fast-entry control write inventory drifted' extra_fast_entry_write
run_fixture relocated-fast-entry-write 'fast-entry wrmsr site drifted' relocated_fast_entry_write
run_fixture relocated-fast-entry-read 'fast-entry rdmsr site drifted' relocated_fast_entry_read
run_fixture extra-fast-entry-read 'fast-entry control read inventory drifted' extra_fast_entry_read
run_fixture unlabeled-page-fault-efer-read \
  'page-fault-provenance EFER source site drifted' unlabeled_page_fault_efer_read
run_fixture late-page-fault-cr2-capture \
  'vector=14 field=cr2-sampling-order source' late_page_fault_cr2_capture
run_fixture second-page-fault-cr2-capture \
  'vector=14 field=cr2-single-sample source' second_page_fault_cr2_capture
run_fixture direct-page-fault-handler \
  'vector=14 field=cr2-sampling-order source' direct_page_fault_handler
run_fixture page-fault-handler-before-generated \
  'vector=14 path=generated-agreement-before-handler source' \
  page_fault_handler_before_generated
run_fixture page-fault-fatal-route-to-handler \
  'vector=14 field=typed-generated-route source' \
  page_fault_fatal_route_to_handler
run_fixture page-fault-live-leaf-bypass \
  'vector=14 field=diagnostic-and-strengthened-agreement-inputs source' \
  page_fault_live_leaf_bypass
run_fixture page-fault-exact-invalidation-bypass \
  'vector=14 field=diagnostic-and-strengthened-agreement-inputs source' \
  page_fault_exact_invalidation_bypass
run_fixture page-fault-forged-diagnostic-purpose \
  'vector=14 field=diagnostic-and-strengthened-agreement-inputs source' \
  page_fault_forged_diagnostic_purpose
run_fixture page-fault-wrong-invalidation-target \
  'vector=14 field=terminal-reviewed-binding source' \
  page_fault_wrong_invalidation_target
run_fixture page-fault-reserved-wrong-error \
  'vector=14 field=terminal-reviewed-binding source' \
  page_fault_reserved_wrong_error
run_fixture page-fault-reserved-wrong-rip \
  'vector=14 field=terminal-reviewed-binding source' \
  page_fault_reserved_wrong_rip
run_fixture page-fault-refilled-after-recorded-reload \
  'vector=14 field=diagnostic-and-strengthened-agreement-inputs source' \
  page_fault_refilled_after_recorded_reload
run_fixture page-fault-rip-post-authorization-mutation \
  'vector=14 field=immutable-snapshot source' \
  mutate_page_fault_rip_after_authorization
run_page_fault_fixture page-fault-wrong-instruction \
  'vector=14 field=deliberate-cpl3-site source' \
  page_fault_wrong_instruction
run_page_fault_fixture page-fault-indirect-entry \
  'vector=14 field=deliberate-cpl3-entry source' \
  page_fault_indirect_entry
run_page_fault_fixture page-fault-wrong-handler-binding \
  'vector=14 field=deliberate-cpl3-handler-binding source' \
  page_fault_wrong_handler_binding
run_nx_page_fault_fixture page-fault-nx-wrong-payload \
  'vector=14 field=deliberate-cpl3-site source' \
  page_fault_nx_wrong_payload
run_nx_page_fault_fixture page-fault-nx-indirect-branch \
  'vector=14 field=deliberate-cpl3-site source' \
  page_fault_nx_indirect_branch
run_nx_page_fault_fixture page-fault-nx-wrong-handler-binding \
  'vector=14 field=deliberate-cpl3-handler-binding source' \
  page_fault_nx_wrong_handler_binding
run_fixture page-fault-c-only-snapshot-route \
  'vector=14 field=canonical-snapshot-binding source' \
  page_fault_c_only_snapshot_route
run_fixture stale-lstar 'fast-entry target write recipe can introduce nonzero state' stale_lstar
run_fixture noncanonical-lstar 'fast-entry target write recipe can introduce nonzero state' noncanonical_lstar
run_fixture non-denying-sysenter 'fast-entry target write recipe can introduce nonzero state' non_denying_sysenter
run_fixture omitted-return-readback 'reviewed return gate omits live fast-entry read-back' omitted_return_readback
run_fixture missing-de-gate 'vector=77 field=present' missing_de_gate
run_fixture missing-bp-gate 'vector=77 field=present' missing_bp_gate
run_fixture de-extra-gate 'vector=77 field=present' de_extra_gate
run_fixture swap-de-bp-targets 'vector=0 field=target-ist-or-dpl violated=divide-error-gate' swap_de_bp_targets
run_fixture de-user-callable 'vector=0 field=target-ist-or-dpl violated=divide-error-gate' de_user_callable
run_fixture de-wrong-ist 'vector=0 field=target-ist-or-dpl violated=divide-error-gate' de_wrong_ist
run_fixture de-wrong-type 'vector=0 field=target-ist-or-dpl violated=divide-error-gate' de_wrong_type
run_fixture bp-wrong-dpl 'vector=3 field=target-ist-or-dpl violated=breakpoint-gate' bp_wrong_dpl
run_fixture de-handler-before-normalize 'vector=0 path=contained' de_before_normalize
run_fixture bp-handler-before-normalize 'vector=3 path=contained' bp_before_normalize
run_fixture de-branch-around-cleanup 'vector=0 path=contained' de_branch_cleanup

echo "Controlled entry descriptor, TSS, and path fixtures passed"
