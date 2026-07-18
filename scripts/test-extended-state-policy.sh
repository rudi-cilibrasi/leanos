#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
mmx_elf="${2:-}"
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

run_fixture inherited-cr0 'field=cr0-normalization' inherit_cr0
run_fixture inherited-cr4 'field=cr4-normalization' inherit_cr4
run_fixture missing-live-snapshot 'field=live-cr4-snapshot' omit_live_snapshot
run_fixture missing-cpuid-snapshot 'field=cpuid-leaf1' omit_cpuid_snapshot
run_fixture unauthorized-clts 'field=unauthorized-enable-or-restore source' add_clts
run_fixture unauthorized-fxrstor 'field=unauthorized-enable-or-restore source' add_fxrstor
run_fixture unauthorized-xrstor 'field=unauthorized-enable-or-restore source' add_xrstor
run_fixture unauthorized-cr0-write 'field=control-write-inventory source' add_cr0_write

if [[ -n "$mmx_elf" ]]; then
  if ./scripts/check-extended-state-policy.sh "$elf" mmx \
      >"$tmp/x87-as-mmx.log" 2>&1; then
    echo "error: x87 image unexpectedly satisfied the MMX probe policy" >&2
    exit 1
  fi
  grep -Fq 'field=mmx-probe final-elf' "$tmp/x87-as-mmx.log" || {
    echo "error: x87/MMX probe mismatch lacked typed diagnostic" >&2; exit 1;
  }
  if ./scripts/check-extended-state-policy.sh "$mmx_elf" x87 \
      >"$tmp/mmx-as-x87.log" 2>&1; then
    echo "error: MMX image unexpectedly satisfied the x87 probe policy" >&2
    exit 1
  fi
  grep -Fq 'field=x87-probe final-elf' "$tmp/mmx-as-x87.log" || {
    echo "error: MMX/x87 probe mismatch lacked typed diagnostic" >&2; exit 1;
  }
  echo "EXTENDED-STATE fixture=probe-class-swap field=probe-class final-elf result=REJECTED"
fi

echo "Controlled extended-state boot-policy fixtures passed"
