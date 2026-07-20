#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build="${LEANOS_BOOT_DIR:-build/boot}"
elf="${1:-$build/leanos-nmi.elf}"
[[ -f "$elf" && -f "$build/kernel-nmi.o" ]] || {
  echo "error: build the NMI image before running its policy fixtures" >&2
  exit 1
}
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
./scripts/check-direct-port-sites.py "$elf" scripts/direct-port-sites-nmi.tsv \
  --terminal-before-user
sed '0,/^isr2_cld/{/^isr2_cld/d;}' scripts/direct-port-sites-nmi.tsv \
  >"$tmp/direct-port-sites.tsv"
if ./scripts/check-direct-port-sites.py "$elf" "$tmp/direct-port-sites.tsv" \
    --terminal-before-user \
    >"$tmp/direct-port.log" 2>&1; then
  echo "error: omitted NMI serial site fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: unauthorized final-ELF port-I/O site isr2_cld 0x87' \
  "$tmp/direct-port.log" || {
    cat "$tmp/direct-port.log" >&2
    exit 1
  }
cp boot/boot.S "$tmp/boot.S"
sed -i '/^isr2:$/a\    iretq' "$tmp/boot.S"
gcc -m64 -ffreestanding -fdebug-prefix-map="$root"=. \
  -ffile-prefix-map="$root"=. -g3 -c "$tmp/boot.S" -o "$tmp/boot.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -o "$tmp/nmi-return.elf" "$tmp/boot.o" \
  "$build/kernel-nmi.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
if ./scripts/check-nmi-image-policy.sh "$tmp/nmi-return.elf" \
    >"$tmp/policy.log" 2>&1; then
  echo "error: NMI iretq final-ELF fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'vector-2 terminal stub calls, pushes, or returns with iretq' \
  "$tmp/policy.log" || {
    cat "$tmp/policy.log" >&2
    exit 1
  }

echo "NMI final-ELF return-edge fixture rejected"
