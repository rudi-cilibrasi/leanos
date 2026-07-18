#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
mmx_elf="${2:-}"
sse_elf="${3:-}"
sse2_elf="${4:-}"
avx_elf="${5:-}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp boot/boot.S "$tmp/boot.S"
  cp boot/kernel.c "$tmp/kernel.c"
  "$@"
  if LEANOS_EXTENDED_STATE_BOOT_SOURCE="$tmp/boot.S" \
      LEANOS_EXTENDED_STATE_KERNEL_SOURCE="$tmp/kernel.c" \
      ./scripts/check-extended-state-policy.sh "$elf" >"$tmp/$name.log" 2>&1; then
    echo "error: extended-state fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: extended-state fixture '$name' lacked '$expected'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
  echo "EXTENDED-STATE fixture=$name $expected result=REJECTED"
}

inherit_cr0() {
  sed -i 's/or $((1 << 31) | (1 << 16) | (1 << 3) | (1 << 2) | (1 << 1)), %eax/or $((1 << 31) | (1 << 16)), %eax/' "$tmp/boot.S"
}
inherit_cr4() {
  sed -i '/and $~((1 << 9) | (1 << 10) | (1 << 18)), %eax/d' "$tmp/boot.S"
}
omit_live_snapshot() {
  sed -i '/const uint64_t forbidden_cr4 =/d' "$tmp/kernel.c"
}
omit_cpuid_snapshot() {
  sed -i 's/: "a"(1u), "c"(0u));/: "a"(2u), "c"(0u));/' "$tmp/kernel.c"
}
bypass_live_policy_gate() {
  sed -i 's/extended_state_features_accepted &&/(1 == 1) \&\&/' "$tmp/kernel.c"
}
add_clts() {
  sed -i '/^normalize_extended_state_cr0:/a\    clts' "$tmp/boot.S"
}
add_fxrstor() {
  sed -i '/^normalize_extended_state_cr0:/a\    fxrstor (%eax)' "$tmp/boot.S"
}
add_xrstor() {
  sed -i '/^normalize_extended_state_cr0:/a\    xrstor (%eax)' "$tmp/boot.S"
}
add_cr0_write() {
  sed -i '/^normalize_extended_state_cr0:/a\    mov %eax, %cr0' "$tmp/boot.S"
}
omit_avx_probe() {
  sed -i 's/vxorps %ymm0, %ymm0, %ymm0/nop/' "$tmp/boot.S"
}

run_fixture inherited-cr0 'field=cr0-normalization' inherit_cr0
run_fixture inherited-cr4 'field=cr4-normalization' inherit_cr4
run_fixture missing-live-snapshot 'field=live-cr4-snapshot' omit_live_snapshot
run_fixture missing-cpuid-snapshot 'field=cpuid-leaf1' omit_cpuid_snapshot
run_fixture bypassed-live-policy-gate 'field=live-policy-gate' bypass_live_policy_gate
run_fixture unauthorized-clts 'field=unauthorized-enable-or-restore source' add_clts
run_fixture unauthorized-fxrstor 'field=unauthorized-enable-or-restore source' add_fxrstor
run_fixture unauthorized-xrstor 'field=unauthorized-enable-or-restore source' add_xrstor
run_fixture unauthorized-cr0-write 'field=control-write-inventory source' add_cr0_write
run_fixture missing-avx-probe 'field=avx-probe source' omit_avx_probe

check_probe_mismatch() {
  local image="$1" actual="$2" expected="$3"
  local log="$tmp/${actual}-as-${expected}.log"
  if ./scripts/check-extended-state-policy.sh "$image" "$expected" \
      >"$log" 2>&1; then
    echo "error: $actual image unexpectedly satisfied the $expected probe policy" >&2
    exit 1
  fi
  grep -Fq "field=${expected}-probe final-elf" "$log" || {
    echo "error: $actual/$expected probe mismatch lacked typed diagnostic" >&2
    exit 1
  }
}

if [[ -n "$mmx_elf" ]]; then
  check_probe_mismatch "$elf" x87 mmx
  check_probe_mismatch "$mmx_elf" mmx x87
fi
if [[ -n "$sse_elf" ]]; then
  check_probe_mismatch "$elf" x87 sse
  check_probe_mismatch "$mmx_elf" mmx sse
  check_probe_mismatch "$sse_elf" sse x87
  check_probe_mismatch "$sse_elf" sse mmx
fi
if [[ -n "$sse2_elf" ]]; then
  check_probe_mismatch "$elf" x87 sse2
  check_probe_mismatch "$mmx_elf" mmx sse2
  check_probe_mismatch "$sse_elf" sse sse2
  check_probe_mismatch "$sse2_elf" sse2 x87
  check_probe_mismatch "$sse2_elf" sse2 mmx
  check_probe_mismatch "$sse2_elf" sse2 sse
fi
if [[ -n "$avx_elf" ]]; then
  check_probe_mismatch "$elf" x87 avx
  check_probe_mismatch "$mmx_elf" mmx avx
  check_probe_mismatch "$sse_elf" sse avx
  check_probe_mismatch "$sse2_elf" sse2 avx
  check_probe_mismatch "$avx_elf" avx x87
  check_probe_mismatch "$avx_elf" avx mmx
  check_probe_mismatch "$avx_elf" avx sse
  check_probe_mismatch "$avx_elf" avx sse2
fi
if [[ -n "$mmx_elf" || -n "$sse_elf" || -n "$sse2_elf" || -n "$avx_elf" ]]; then
  echo "EXTENDED-STATE fixture=probe-class-swap field=probe-class final-elf result=REJECTED"
fi

echo "Controlled extended-state boot-policy fixtures passed"
