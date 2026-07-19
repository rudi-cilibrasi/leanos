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
wrong_tss_stack() { sed -i 's/tss.rsp0 = (uint64_t)(entry_stack + sizeof(entry_stack));/tss.rsp0 = (uint64_t)boot_stack_top;/' "$tmp/kernel.c"; }

run_fixture wrong-target 'vector=14 field=target-or-dpl' wrong_target
run_fixture wrong-ud-target 'vector=6 field=target-or-dpl' wrong_ud_target
run_fixture wrong-nm-target 'vector=7 field=target-or-dpl' wrong_nm_target
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
run_fixture wrong-tss-stack 'vector=128 field=tss.rsp0' wrong_tss_stack

echo "Controlled entry descriptor, TSS, and path fixtures passed"
