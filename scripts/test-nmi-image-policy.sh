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
mkdir -p "$tmp/source/boot" "$tmp/source/docs"
cp boot/kernel.c "$tmp/source/boot/kernel.c"
cp docs/interrupt-model.md "$tmp/source/docs/interrupt-model.md"
sed -i '/firmware does not deliver$/ { N; s/firmware does not deliver\nNMI before/firmware might deliver\nNMI before/; }' \
  "$tmp/source/docs/interrupt-model.md"
if LEANOS_SOURCE_ROOT="$tmp/source" ./scripts/check-nmi-image-policy.sh "$elf" \
    >"$tmp/policy-text.log" 2>&1; then
  echo "error: missing multiline NMI policy text fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: NMI policy text missing from' "$tmp/policy-text.log" || {
  cat "$tmp/policy-text.log" >&2
  exit 1
}

link_fixture() {
  local name="$1"
  local instruction="$2"
  cp boot/boot.S "$tmp/$name.S"
  sed -i "/^isr2:\$/a\\    $instruction" "$tmp/$name.S"
  gcc -m64 -ffreestanding -fdebug-prefix-map="$root"=. \
    -ffile-prefix-map="$root"=. -g3 -c "$tmp/$name.S" -o "$tmp/$name.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -o "$tmp/$name.elf" "$tmp/$name.o" \
    "$build/kernel-nmi.o" "$build/KernelTransition.o" "$build/Syscall.o" \
    "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
    "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
}

link_fixture nmi-return ret
if ./scripts/check-nmi-image-policy.sh "$tmp/nmi-return.elf" \
    >"$tmp/policy-return.log" 2>&1; then
  echo "error: NMI ret final-ELF fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'terminal CFG contains a return' "$tmp/policy-return.log" || {
  cat "$tmp/policy-return.log" >&2
  exit 1
}

link_fixture nmi-escape 'jmp isr13'
if ./scripts/check-nmi-image-policy.sh "$tmp/nmi-escape.elf" \
    >"$tmp/policy-escape.log" 2>&1; then
  echo "error: NMI branch-escape final-ELF fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'terminal CFG branch escapes isr2..isr13' "$tmp/policy-escape.log" || {
  cat "$tmp/policy-escape.log" >&2
  exit 1
}

echo "NMI policy-text, return-edge, and branch-escape fixtures rejected"
