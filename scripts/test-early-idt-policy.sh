#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build="${LEANOS_BOOT_DIR:-build/boot}"
cc="${LEANOS_CC:-gcc}"
elf="${1:-$build/leanos.elf}"
[[ -f "$elf" && -f "$build/kernel.o" ]] || {
  echo "error: build the boot image before running early-IDT policy fixtures" >&2
  exit 1
}
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

link_fixture() {
  local name="$1"
  "$cc" -m64 -ffreestanding -fdebug-prefix-map="$root"=. \
    -ffile-prefix-map="$root"=. -g3 -I"$build" -c "$tmp/$name.S" -o "$tmp/$name.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -o "$tmp/$name.elf" "$tmp/$name.o" \
    "$build/kernel.o" "$build/KernelTransition.o" "$build/Syscall.o" \
    "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
    "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
}

run_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp boot/boot.S "$tmp/$name.S"
  "$@"
  link_fixture "$name"
  if ./scripts/check-early-idt-policy.py "$tmp/$name.elf" \
      >"$tmp/$name.log" 2>&1; then
    echo "error: early-IDT fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: early-IDT fixture '$name' lacked '$expected'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
  echo "EARLY-IDT-POLICY fixture=$name result=REJECTED"
}

missing_first_lidt() {
  sed -i '/^    lidt boot_idt32_pointer$/d' "$tmp/missing-first-lidt.S"
}
work_before_first_lidt() {
  sed -i '/^    lidt boot_idt32_pointer$/i\    movl $0, page_table_a' \
    "$tmp/work-before-first-lidt.S"
}
swapped_tables() {
  sed -i 's/lidt boot_idt32_pointer/lidt SWAPPED_POINTER/; s/lidt boot_idt64_pointer/lidt boot_idt32_pointer/; s/lidt SWAPPED_POINTER/lidt boot_idt64_pointer/' \
    "$tmp/swapped-tables.S"
}
dpl3_gate32() {
  sed -i '/^\.macro EARLY_GATE32 target$/,/^\.endm$/ s/\.byte 0x8e/.byte 0xee/' \
    "$tmp/dpl3-gate32.S"
}
premature_ist64() {
  sed -i '/^\.macro EARLY_GATE64 target$/,/^\.endm$/ s/^    \.byte 0$/    .byte 1/' \
    "$tmp/premature-ist64.S"
}
vector2_ordinary_target() {
  sed -i 's/^    EARLY_GATE64 LEANOS_EARLY_ISR2_64$/    EARLY_GATE64 LEANOS_EARLY_CATCHALL_64/' \
    "$tmp/vector2-ordinary-target.S"
}
stub_iretq() {
  sed -i '/^boot_early_isr2_64:$/a\    iretq' "$tmp/stub-iretq.S"
}
stub_call_c() {
  sed -i '/^boot_early_catchall_64:$/a\    call kernel_main' "$tmp/stub-call-c.S"
}
stub_branch_escape() {
  sed -i '/^boot_early_isr2_64:$/a\    jmp long_mode_entry' \
    "$tmp/stub-branch-escape.S"
}
early_sti() {
  sed -i '/^boot_idt32_published:$/a\    sti' "$tmp/early-sti.S"
}
early_pic_unmask() {
  sed -i '/^boot_idt32_published:$/a\    mov $0xff, %al\n    outb %al, $0x21' \
    "$tmp/early-pic-unmask.S"
}

run_fixture missing-first-lidt \
  'expected two bootstrap lidt publications' missing_first_lidt
run_fixture work-before-first-lidt \
  'unreviewed instruction before first kernel lidt' work_before_first_lidt
run_fixture swapped-tables \
  'first kernel lidt must publish boot_idt32_pointer' swapped_tables
run_fixture dpl3-gate32 'bootstrap32 gate attributes drifted' dpl3_gate32
run_fixture premature-ist64 \
  'bootstrap64 gate uses IST before the TSS exists' premature_ist64
run_fixture vector2-ordinary-target \
  'bootstrap64 vector-2 gate target drifted' vector2_ordinary_target
run_fixture stub-iretq 'terminal CFG contains a return' stub_iretq
run_fixture stub-call-c 'terminal CFG contains a call' stub_call_c
run_fixture stub-branch-escape 'terminal CFG branch escapes' stub_branch_escape
run_fixture early-sti \
  'forbidden instruction in the boot-entry interval' early_sti
run_fixture early-pic-unmask \
  'forbidden instruction in the boot-entry interval' early_pic_unmask

echo "Early-IDT publication, descriptor, terminal-CFG, and interval fixtures rejected"
