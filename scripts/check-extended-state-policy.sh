#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
probe="${2:-}"
boot_source="${LEANOS_EXTENDED_STATE_BOOT_SOURCE:-boot/boot.S}"
kernel_source="${LEANOS_EXTENDED_STATE_KERNEL_SOURCE:-boot/kernel.c}"
[[ -f "$elf" ]] || { echo "error: missing extended-state-policy ELF: $elf" >&2; exit 1; }
[[ -f "$boot_source" && -f "$kernel_source" ]] || {
  echo "error: missing extended-state-policy source snapshot" >&2; exit 1;
}

symbols="$(nm "$elf")"
for symbol in normalize_extended_state_cr0 normalize_extended_state_cr4; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: extended-state field=symbol missing=$symbol" >&2; exit 1;
  }
done

grep -Fq 'and $~((1 << 9) | (1 << 10) | (1 << 18)), %eax' "$boot_source" || {
  echo "error: extended-state field=cr4-normalization inherited-or-enabled" >&2; exit 1;
}
grep -Fq 'or $((1 << 31) | (1 << 16) | (1 << 3) | (1 << 2) | (1 << 1)), %eax' \
  "$boot_source" || {
  echo "error: extended-state field=cr0-normalization inherited-or-relaxed" >&2; exit 1;
}
grep -Fq 'const uint64_t forbidden_cr4 = (1ull << 18) | (1ull << 10) | (1ull << 9);' \
  "$kernel_source" || {
  echo "error: extended-state field=live-cr4-snapshot missing" >&2; exit 1;
}
grep -Fq 'const uint64_t required_cr0 = (1ull << 16) | (1ull << 3) |' \
  "$kernel_source" || {
  echo "error: extended-state field=live-cr0-snapshot missing" >&2; exit 1;
}
grep -Fq 'cr0.em=1 cr0.mp=1 cr0.ts=1 cr4.osfxsr=0 cr4.osxmmexcpt=0 cr4.osxsave=0' \
  "$kernel_source" || {
  echo "error: extended-state field=evidence-record missing" >&2; exit 1;
}
grep -Fq 'leanos_extended_state_denial_demo(policy, mode, vector, current_subject,' \
  "$kernel_source" || {
  echo "error: extended-state field=runtime-adapter missing" >&2; exit 1;
}
grep -Fq 'uint64_t policy = extended_state_features_accepted &&' "$kernel_source" || {
  echo "error: extended-state field=live-policy-gate missing" >&2; exit 1;
}
grep -Fq ': "a"(1u), "c"(0u));' "$kernel_source" || {
  echo "error: extended-state field=cpuid-leaf1 missing" >&2; exit 1;
}
grep -Fq 'cpuid.1.x87=1 cpuid.1.mmx=1 cpuid.1.sse=1 cpuid.1.sse2=1 cpuid.1.xsave=1 cpuid.1.osxsave=0 cpuid.1.avx=1 cpu=max result=PASS' \
  "$kernel_source" || {
  echo "error: extended-state field=cpuid-evidence missing" >&2; exit 1;
}
grep -Fq 'vxorps %ymm0, %ymm0, %ymm0' "$boot_source" || {
  echo "error: extended-state field=avx-probe source" >&2; exit 1;
}
if grep -Eiq '^[[:space:]]*(clts|fxrstor|xrstor)(64)?([[:space:]]|$)' "$boot_source" ||
   grep -Eiq '"[[:space:]]*(clts|fxrstor|xrstor)(64)?([[:space:]]|"|$)' "$kernel_source"; then
  echo "error: extended-state field=unauthorized-enable-or-restore source" >&2
  exit 1
fi
source_control_writes="$(grep -Ec \
  '^[[:space:]]*mov[qwl]?[[:space:]]+%[[:alnum:]]+,[[:space:]]*%cr(0|4)([[:space:]]|$)' \
  "$boot_source")"
[[ "$source_control_writes" -eq 3 &&
   "$(grep -Fc 'mov %eax, %cr0' "$boot_source")" -eq 1 &&
   "$(grep -Fc 'mov %eax, %cr4' "$boot_source")" -eq 1 &&
   "$(grep -Fc 'mov %rax, %cr4' "$boot_source")" -eq 1 ]] || {
  echo "error: extended-state field=control-write-inventory source" >&2; exit 1;
}
if grep -Eq 'mov[^"]*,[[:space:]]*%%cr(0|4)' "$kernel_source"; then
  echo "error: extended-state field=control-write-inventory source" >&2
  exit 1
fi

disassembly="$(objdump -d --no-show-raw-insn "$elf")"
if [[ "$probe" == x87 ]]; then
  grep -Eq '[[:space:]]fld1([[:space:]]|$)' <<<"$disassembly" || {
    echo "error: extended-state field=x87-probe final-elf" >&2; exit 1;
  }
elif [[ "$probe" == mmx ]]; then
  grep -Eq '[[:space:]]pxor[[:space:]]+%mm0,%mm0([[:space:]]|$)' \
    <<<"$disassembly" || {
    echo "error: extended-state field=mmx-probe final-elf" >&2; exit 1;
  }
elif [[ "$probe" == sse ]]; then
  grep -Eq '[[:space:]]xorps[[:space:]]+%xmm0,%xmm0([[:space:]]|$)' \
    <<<"$disassembly" || {
    echo "error: extended-state field=sse-probe final-elf" >&2; exit 1;
  }
elif [[ "$probe" == sse2 ]]; then
  grep -Eq '[[:space:]]pxor[[:space:]]+%xmm0,%xmm0([[:space:]]|$)' \
    <<<"$disassembly" || {
    echo "error: extended-state field=sse2-probe final-elf" >&2; exit 1;
  }
elif [[ "$probe" == avx ]]; then
  grep -Eq '[[:space:]]vxorps[[:space:]]+%ymm0,%ymm0,%ymm0([[:space:]]|$)' \
    <<<"$disassembly" || {
    echo "error: extended-state field=avx-probe final-elf" >&2; exit 1;
  }
elif [[ -n "$probe" ]]; then
  echo "error: extended-state field=probe-class unsupported=$probe" >&2
  exit 1
fi
grep -Eq '[[:space:]]and[[:space:]]+\$0xfffbf9ff,%eax' <<<"$disassembly" || {
  echo "error: extended-state field=cr4-normalization final-elf" >&2; exit 1;
}
grep -Eq '[[:space:]]or[[:space:]]+\$0x8001000e,%eax' <<<"$disassembly" || {
  echo "error: extended-state field=cr0-normalization final-elf" >&2; exit 1;
}
[[ $(grep -Ec '[[:space:]]cpuid([[:space:]]|$)' <<<"$disassembly") -ge 2 ]] || {
  echo "error: extended-state field=cpuid-snapshot final-elf" >&2; exit 1;
}
if grep -Eiq '[[:space:]](clts|fxrstor|xrstor)(64)?([[:space:]]|$)' <<<"$disassembly"; then
  echo "error: extended-state field=unauthorized-enable-or-restore final-elf" >&2
  exit 1
fi
[[ "$(grep -Ec '[[:space:]]mov[[:space:]]+%[[:alnum:]]+,%cr(0|4)([[:space:]]|$)' \
  <<<"$disassembly")" -eq 3 ]] || {
  echo "error: extended-state field=control-write-inventory final-elf" >&2; exit 1;
}

echo "Extended-state CPUID/CR0/CR4 derivation, live snapshot, and final-ELF policy passed${probe:+ probe=$probe}"
