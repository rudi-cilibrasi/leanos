#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
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

wrong_target() { sed -i 's/set_gate(14, isr14,/set_gate(14, isr32,/' "$tmp/kernel.c"; }
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
gp_before_normalize() { sed -i '/call authorize_interrupt_entry/i\    call entry_adversarial_gp_handler' "$tmp/boot.S"; }
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
stale_lstar() { sed -i '/normalize_fast_entry_lstar_write:/i\    mov $user_a_text, %eax' "$tmp/boot.S"; }
noncanonical_lstar() { sed -i '/normalize_fast_entry_lstar_write:/i\    mov $0x00008000, %edx' "$tmp/boot.S"; }
non_denying_sysenter() { sed -i '/normalize_fast_entry_sysenter_cs_write:/i\    mov $1, %eax' "$tmp/boot.S"; }
omitted_return_readback() { sed -i '/^void validate_user_return/,/^}/ s/check_fast_entry_control();/\/\* omitted return fixture \*\//' "$tmp/kernel.c"; }

run_fixture wrong-target 'vector=14 field=target-or-dpl' wrong_target
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
run_fixture stale-lstar 'fast-entry target write recipe can introduce nonzero state' stale_lstar
run_fixture noncanonical-lstar 'fast-entry target write recipe can introduce nonzero state' noncanonical_lstar
run_fixture non-denying-sysenter 'fast-entry target write recipe can introduce nonzero state' non_denying_sysenter
run_fixture omitted-return-readback 'reviewed return gate omits live fast-entry read-back' omitted_return_readback

echo "Controlled entry descriptor, TSS, and path fixtures passed"
