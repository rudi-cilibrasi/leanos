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
mkdir -p "$tmp/source/boot" "$tmp/source/docs"
cp boot/boot.S "$tmp/source/boot/boot.S"
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

cp -R "$tmp/source" "$tmp/early-map-source"
sed -i '/mov \$__nmi_ist_guard_start, %eax/,/movl \$0, page_table_b+4(%eax)/ {
  /movl \$0, page_table_b+4(%eax)/d
}' "$tmp/early-map-source/boot/boot.S"
if LEANOS_SOURCE_ROOT="$tmp/early-map-source" \
    ./scripts/check-nmi-image-policy.sh "$elf" >"$tmp/early-map.log" 2>&1; then
  echo "error: incomplete early NMI guard unmapping fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: NMI guard must be cleared exactly once in both early address spaces' \
  "$tmp/early-map.log" || {
    cat "$tmp/early-map.log" >&2
    exit 1
  }

plan="$build/boot-page-plan-nmi.final.h"
[[ -f "$plan" ]] || { echo "error: missing final NMI boot plan: $plan" >&2; exit 1; }
./scripts/check-nmi-guard-plan.py "$elf" "$plan" >/dev/null
cp "$plan" "$tmp/mapped-guard-plan.h"
guard_hex="$(nm -n "$elf" | awk '$3 == "__nmi_ist_guard_start" { print $1 }')"
guard_page=$((16#$guard_hex / 4096))
guard_line=$((guard_page + 3))
guard_leaf=$((guard_page * 4096 + 3))
sed -i "${guard_line}c\\  ${guard_leaf}ULL," "$tmp/mapped-guard-plan.h"
if ./scripts/check-nmi-guard-plan.py "$elf" "$tmp/mapped-guard-plan.h" \
    >"$tmp/mapped-guard-plan.log" 2>&1; then
  echo "error: mapped NMI guard plan fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: NMI guard is mapped in leanos_boot_plan_a' \
  "$tmp/mapped-guard-plan.log" || {
    cat "$tmp/mapped-guard-plan.log" >&2
    exit 1
  }

link_fixture() {
  local name="$1"
  local instruction="$2"
  local linker="${3:-boot/linker.ld}"
  cp boot/boot.S "$tmp/$name.S"
  sed -i "/^isr2:\$/a\\    $instruction" "$tmp/$name.S"
  gcc -m64 -ffreestanding -fdebug-prefix-map="$root"=. \
    -ffile-prefix-map="$root"=. -g3 -c "$tmp/$name.S" -o "$tmp/$name.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T "$linker" -o "$tmp/$name.elf" "$tmp/$name.o" \
    "$build/kernel-nmi.o" "$build/KernelTransition.o" "$build/Syscall.o" \
    "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
    "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
}

cp "$elf" "$tmp/nmi-missing-guard.elf"
objcopy --strip-symbol=__nmi_ist_guard_start "$tmp/nmi-missing-guard.elf"
if ./scripts/check-nmi-image-policy.sh "$tmp/nmi-missing-guard.elf" \
    >"$tmp/policy-missing-guard.log" 2>&1; then
  echo "error: missing NMI guard symbol fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: NMI terminal policy symbol missing: __nmi_ist_guard_start' \
  "$tmp/policy-missing-guard.log" || {
    cat "$tmp/policy-missing-guard.log" >&2
    exit 1
  }

cp boot/boot.S "$tmp/nmi-mapped-guard.S"
sed -i 's/\.section \.nmi_ist\.guard,"aw",@nobits/.section .nmi_ist.guard,"aw",@progbits/' \
  "$tmp/nmi-mapped-guard.S"
sed 's/\.nmi_ist_guard (NOLOAD)/.nmi_ist_guard/' boot/linker.ld \
  >"$tmp/nmi-mapped-guard.ld"
gcc -m64 -ffreestanding -fdebug-prefix-map="$root"=. \
  -ffile-prefix-map="$root"=. -g3 -c "$tmp/nmi-mapped-guard.S" \
  -o "$tmp/nmi-mapped-guard.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T "$tmp/nmi-mapped-guard.ld" -o "$tmp/nmi-mapped-guard.elf" \
  "$tmp/nmi-mapped-guard.o" "$build/kernel-nmi.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
if ./scripts/check-nmi-image-policy.sh "$tmp/nmi-mapped-guard.elf" \
    >"$tmp/policy-mapped-guard.log" 2>&1; then
  echo "error: mapped NMI guard section fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: NMI section .nmi_ist_guard must be NOBITS, found PROGBITS' \
  "$tmp/policy-mapped-guard.log" || {
    cat "$tmp/policy-mapped-guard.log" >&2
    exit 1
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

echo "NMI guard-plan, layout, early-map, policy-text, return-edge, and branch-escape fixtures rejected"
