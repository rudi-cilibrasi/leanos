#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
command -v "$qemu" >/dev/null 2>&1 || {
  echo "error: missing required tool '$qemu'" >&2; exit 1;
}
command -v timeout >/dev/null 2>&1 || {
  echo "error: missing required tool 'timeout'" >&2; exit 1;
}
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || {
  echo "error: timeout must be a positive integer" >&2; exit 1;
}
[[ "$memory_mib" =~ ^(64|128)$ ]] || {
  echo "error: memory must be 64 or 128 MiB" >&2; exit 1;
}

specs=(
  'kernel-selector:user-return-selector'
  'wrong-stack-selector:user-return-selector'
  'noncanonical-rip:user-return-noncanonical'
  'noncanonical-rsp:user-return-noncanonical'
  'outside-code:user-return-code'
  'outside-stack:user-return-stack'
  'flags-ac:user-return-flags'
  'flags-df:user-return-flags'
  'stale-cr3:user-return-cr3'
  'stale-context:user-return-code'
  'post-validation-mutation:user-return-noncanonical'
  'blocking-context-canary:register-canary'
)

for spec in "${specs[@]}"; do
  IFS=: read -r fixture reason <<<"$spec"
  image="build/boot/leanos-${version}-x86_64-return-${fixture}.iso"
  log="build/boot/return-corruption-${fixture}.serial.log"
  [[ -f "$image" ]] || {
    echo "error: missing return-corruption image '$image'" >&2; exit 1;
  }
  : > "$log"
  command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1 -m "${memory_mib}M"
    -display none -monitor none -serial "file:$log" -no-reboot -no-shutdown
    -nic none -device isa-debug-exit,iobase=0xf4,iosize=0x04 -cdrom "$image")
  set +e
  timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"
  status=$?
  set -e
  if [[ $status -eq 124 || $status -eq 137 ]]; then
    echo "error: return-corruption fixture '$fixture' timed out" >&2; exit 1
  fi
  [[ $status -eq 35 ]] || {
    echo "error: fixture '$fixture' exited $status instead of typed guest failure 35" >&2
    exit 1
  }
  grep -Fxq "LEANOS/9 RETURN fixture=${fixture} stage=outgoing-frame result=INJECTED" \
    "$log" || {
    echo "error: fixture '$fixture' lacked its outgoing-frame injection record" >&2
    exit 1
  }
  grep -Fxq "LEANOS/3 FINAL status=FAIL reason=${reason}" "$log" || {
    echo "error: fixture '$fixture' lacked typed rejection reason '$reason'" >&2
    exit 1
  }
  if grep -Eq '^LEANOS/5 ENTRY|^LEANOS/5 FINAL status=PASS' "$log"; then
    echo "error: fixture '$fixture' reached CPL3 or normal completion" >&2
    exit 1
  fi
done

echo "Outgoing return-frame corruption QEMU fixtures passed (${#specs[@]} modes)"
