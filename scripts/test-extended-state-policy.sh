#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
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

echo "Controlled extended-state boot-policy fixtures passed"
