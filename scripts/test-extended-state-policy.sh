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
  sed -i '/and $~((1 << 9) | (1 << 10) | (1 << 18) | (1 << 22)), %eax/d' "$tmp/boot.S"
}
inherit_cr4_pke() {
  sed -i 's/ | (1 << 22)//' "$tmp/boot.S"
}
omit_live_snapshot() {
  sed -i '/const uint64_t forbidden_cr4 =/,+1d' "$tmp/kernel.c"
}
omit_cpuid_snapshot() {
  sed -i 's/: "a"(1u), "c"(0u));/: "a"(2u), "c"(0u));/' "$tmp/kernel.c"
}
bypass_live_policy_gate() {
  sed -i 's/extended_state_features_accepted &&/(1 == 1) \&\&/' "$tmp/kernel.c"
}
bypass_handler_origin() {
  sed -i 's/saved_cs != 0x23/0/' "$tmp/kernel.c"
}
bypass_handler_address_space() {
  sed -i 's/expected_cr3 == 0 || cr3 != expected_cr3/0/' "$tmp/kernel.c"
}
bypass_handler_probe_vector() {
  sed -i 's/if (vector != expected_vector)/if (0)/' "$tmp/kernel.c"
}
bypass_handler_probe_rip() {
  sed -i 's/if (saved_rip != (uint64_t)user_a_extended_state_probe)/if (0)/' \
    "$tmp/kernel.c"
}
omit_peer_cr4_pke_validation() {
  sed -i '/const uint64_t forbidden_peer_cr4 =/s/(1ull << 22) | //' \
    "$tmp/kernel.c"
}
omit_final_return_control_validation() {
  sed -i 's/(cr4 & required_cr4) != required_cr4 ||/(1 == 0) ||/' \
    "$tmp/kernel.c"
}
add_clts() {
  sed -i '/^normalize_extended_state_cr0:/a\    clts' "$tmp/boot.S"
}
add_lmsw() {
  sed -i '/^normalize_extended_state_cr0:/a\    lmsw %ax' "$tmp/boot.S"
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
run_fixture inherited-cr4-pke 'field=cr4-normalization' inherit_cr4_pke
run_fixture missing-live-snapshot 'field=live-cr4-snapshot' omit_live_snapshot
run_fixture missing-cpuid-snapshot 'field=cpuid-leaf1' omit_cpuid_snapshot
run_fixture bypassed-live-policy-gate 'field=live-policy-gate' bypass_live_policy_gate
run_fixture bypassed-handler-origin 'field=handler-origin-binding' bypass_handler_origin
run_fixture bypassed-handler-address-space 'field=handler-address-space-binding' bypass_handler_address_space
run_fixture bypassed-handler-probe-vector 'field=handler-probe-vector' bypass_handler_probe_vector
run_fixture bypassed-handler-probe-rip 'field=handler-probe-rip' bypass_handler_probe_rip
run_fixture missing-peer-cr4-pke-validation 'field=peer-cr4-pke-validation' omit_peer_cr4_pke_validation
run_fixture missing-final-return-control-validation 'field=final-return-control-validation' omit_final_return_control_validation
run_fixture unauthorized-clts 'field=unauthorized-enable-or-restore source' add_clts
run_fixture unauthorized-lmsw 'field=unauthorized-enable-or-restore source' add_lmsw
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

if [[ -n "$sse_elf" ]]; then
  objcopy --dump-section .user_a_text="$tmp/user-a.bin" "$sse_elf"
  printf '\x0f\x57\xc9' | dd of="$tmp/user-a.bin" bs=1 seek=0 conv=notrunc status=none
  cp "$sse_elf" "$tmp/extra-simd.elf"
  objcopy --update-section .user_a_text="$tmp/user-a.bin" "$tmp/extra-simd.elf"
  if ./scripts/check-extended-state-policy.sh "$tmp/extra-simd.elf" sse \
      >"$tmp/extra-simd.log" 2>&1; then
    echo "error: extra SIMD final-ELF mutation unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq 'field=denied-family final-elf allowlist' "$tmp/extra-simd.log" || {
    echo "error: extra SIMD mutation lacked denied-family diagnostic" >&2
    cat "$tmp/extra-simd.log" >&2
    exit 1
  }
  echo "EXTENDED-STATE fixture=extra-simd field=denied-family final-elf result=REJECTED"

  check_denied_mutation() {
    local name="$1" bytes="$2"
    objcopy --dump-section .user_a_text="$tmp/$name.bin" "$sse_elf"
    printf '%b' "$bytes" | dd of="$tmp/$name.bin" bs=1 seek=0 conv=notrunc status=none
    cp "$sse_elf" "$tmp/$name.elf"
    objcopy --update-section .user_a_text="$tmp/$name.bin" "$tmp/$name.elf"
    if ./scripts/check-extended-state-policy.sh "$tmp/$name.elf" sse \
        >"$tmp/$name.log" 2>&1; then
      echo "error: $name final-ELF mutation unexpectedly passed" >&2
      exit 1
    fi
    grep -Fq 'field=denied-family final-elf allowlist' "$tmp/$name.log" || {
      echo "error: $name mutation lacked denied-family diagnostic" >&2
      cat "$tmp/$name.log" >&2
      exit 1
    }
    echo "EXTENDED-STATE fixture=$name field=denied-family final-elf result=REJECTED"
  }

  check_denied_mutation extra-vzeroupper '\xc5\xf8\x77'
  check_denied_mutation extra-xsave64 '\x48\x0f\xae\x20'
  check_denied_mutation extra-xsetbv '\x0f\x01\xd1'
  check_denied_mutation extra-vldmxcsr '\xc5\xf8\xae\x10'
  check_denied_mutation extra-lmsw '\x0f\x01\xf0'
  check_denied_mutation extra-rdpkru '\x0f\x01\xee'
  check_denied_mutation extra-wrpkru '\x0f\x01\xef'
fi

echo "Controlled extended-state boot-policy fixtures passed"
