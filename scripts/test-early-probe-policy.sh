#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build="${LEANOS_BOOT_DIR:-build/boot}"
cc="${LEANOS_CC:-gcc}"
[[ -f "$build/kernel.o" ]] || {
  echo "error: build the boot image before running early-probe policy fixtures" >&2
  exit 1
}
tmp="$(mktemp -d)"
./scripts/generate-oracle.sh "$tmp/oracle" > /dev/null
export LEANOS_SERIAL_PROTOCOL_TSV="$tmp/oracle/serial-protocol.tsv"
trap 'rm -rf "$tmp"' EXIT

link_fixture() {
  local name="$1"
  shift
  "$cc" -m64 -ffreestanding -fdebug-prefix-map="$root"=. \
    -ffile-prefix-map="$root"=. -g3 -I"$tmp/oracle" "$@" -c "$tmp/$name.S" -o "$tmp/$name.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -o "$tmp/$name.elf" "$tmp/$name.o" \
    "$build/kernel.o" "$build/KernelTransition.o" "$build/Syscall.o" \
    "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
    "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
}

run_fixture() {
  local name="$1" probe="$2" define="$3" expected="$4"
  shift 4
  cp boot/boot.S "$tmp/$name.S"
  "$@"
  link_fixture "$name" $define
  if ./scripts/check-early-probe-policy.py "$tmp/$name.elf" "$probe" \
      >"$tmp/$name.log" 2>&1; then
    echo "error: early-probe fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: early-probe fixture '$name' lacked '$expected'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
  echo "EARLY-PROBE-POLICY fixture=$name result=REJECTED"
}

ud_int_substitute() {
  sed -i '/^boot_bootstrap32_ud_probe:$/{n;s/.*/    int $6/}' \
    "$tmp/ud-int-substitute.S"
}
ud_moved_probe() {
  sed -i '/^boot_idt32_published:$/a\    mov %eax, multiboot_magic' \
    "$tmp/ud-moved-probe.S"
}
ud_before_lidt() {
  sed -i '/^    lidt boot_idt32_pointer$/d' "$tmp/ud-before-lidt.S"
}
ud_frame_check_dropped() {
  sed -i '/^    cmpl \$0x38, 4(%esp)$/d' "$tmp/ud-frame-check-dropped.S"
}
ud_wrong_success_exit() {
  sed -i 's/^    mov \$0x16, %al$/    mov $0x14, %al/' \
    "$tmp/ud-wrong-success-exit.S"
}
ud_wrong_failure_exit() {
  sed -i 's/^    mov \$0x18, %al$/    mov $0x15, %al/' \
    "$tmp/ud-wrong-failure-exit.S"
}
ud_forged_record() {
  sed -i 's/vector=6 reason=invalid-opcode/vector=8 reason=invalid-opcode/' \
    "$tmp/ud-forged-record.S"
}
nmi_ready_before_stack() {
  sed -i '/^    mov \$boot_stack_top, %rsp$/d' "$tmp/nmi-ready-before-stack.S"
}
nmi_moved_ready() {
  sed -i '/^    xor %rbp, %rbp$/a\    nop' "$tmp/nmi-moved-ready.S"
}
nmi_skipped_halt() {
  sed -i '/^4:  hlt$/d;/^    jmp 4b$/d' "$tmp/nmi-skipped-halt.S"
}
nmi_synthetic_int() {
  sed -i '/^4:  hlt$/i\    int $2' "$tmp/nmi-synthetic-int.S"
}
nmi_extra_output_site() {
  sed -i '/^    jmp 4b$/a\    outb %al, %dx' "$tmp/nmi-extra-output-site.S"
}
nmi_frame_check_dropped() {
  sed -i '/^    cmpq \$0x08, 8(%rsp)$/d' "$tmp/nmi-frame-check-dropped.S"
}
nmi_wrong_exit() {
  sed -i 's/^    mov \$0x17, %al$/    mov $0x14, %al/' "$tmp/nmi-wrong-exit.S"
}
nmi_forged_ready_record() {
  sed -i 's/stack=boot if=0 tss=none runtime-idt=unpublished/stack=boot if=1 tss=none runtime-idt=unpublished/' \
    "$tmp/nmi-forged-ready-record.S"
}
cross_probe_contamination() {
  :
}

run_fixture ud-int-substitute bootstrap32-ud -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'bootstrap32 probe requires exactly one prologue ud2' ud_int_substitute
run_fixture ud-moved-probe bootstrap32-ud -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'bootstrap32 ud2 probe site moved from the publication boundary' \
  ud_moved_probe
run_fixture ud-before-lidt bootstrap32-ud -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'bootstrap32 ud2 is not the first instruction after the first bootstrap lidt' \
  ud_before_lidt
run_fixture ud-frame-check-dropped bootstrap32-ud \
  -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'bootstrap32 catch-all stub instruction drifted' ud_frame_check_dropped
run_fixture ud-wrong-success-exit bootstrap32-ud \
  -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'instruction drifted' ud_wrong_success_exit
run_fixture ud-wrong-failure-exit bootstrap32-ud \
  -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'bootstrap32 catch-all stub instruction drifted' ud_wrong_failure_exit
run_fixture ud-forged-record bootstrap32-ud -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  'early-probe record early32_fault_record content drifted' ud_forged_record
run_fixture nmi-ready-before-stack bootstrap64-nmi \
  -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'long-mode entry instruction drifted' nmi_ready_before_stack
run_fixture nmi-moved-ready bootstrap64-nmi -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'long-mode readiness site drifted from its exported symbol' nmi_moved_ready
run_fixture nmi-skipped-halt bootstrap64-nmi -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'long-mode entry instruction drifted' nmi_skipped_halt
run_fixture nmi-synthetic-int bootstrap64-nmi \
  -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'long-mode entry instruction drifted' nmi_synthetic_int
run_fixture nmi-extra-output-site bootstrap64-nmi \
  -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'long-mode entry instruction drifted' nmi_extra_output_site
run_fixture nmi-frame-check-dropped bootstrap64-nmi \
  -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'bootstrap64 vector-2 stub instruction drifted' nmi_frame_check_dropped
run_fixture nmi-wrong-exit bootstrap64-nmi -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'bootstrap64 vector-2 stub instruction drifted' nmi_wrong_exit
run_fixture nmi-forged-ready-record bootstrap64-nmi \
  -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  'early-probe record early64_ready_record content drifted' \
  nmi_forged_ready_record
run_fixture cross-probe-contamination bootstrap32-ud \
  '-DLEANOS_BOOTSTRAP32_UD_PROBE=1 -DLEANOS_BOOTSTRAP64_NMI_PROBE=1' \
  'foreign probe symbol present in this image' cross_probe_contamination

echo "Early-probe placement, frame-guard, exit-code, and record fixtures rejected"
