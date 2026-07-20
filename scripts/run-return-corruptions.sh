#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
build="${LEANOS_BOOT_DIR:-build/boot}"
selected="${LEANOS_RETURN_CORRUPTION_FIXTURE:-}"
matrix="${LEANOS_EVIDENCE_MATRIX:-scripts/emulator-evidence-matrix.tsv}"
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

[[ -f "$matrix" ]] || { echo "error: evidence matrix '$matrix' not found" >&2; exit 1; }
specs=()
while IFS=$'\t' read -r _id runner _class _timeout _image _elf _log \
    fixture _mode reason; do
  [[ "$runner" == return ]] || continue
  if [[ -z "$selected" || "$fixture" == "$selected" ]]; then
    specs+=("${fixture}:${reason}")
  fi
done < "$matrix"
if [[ ${#specs[@]} -eq 0 ]]; then
  echo "error: unknown or missing return-corruption fixture '${selected:-<all>}'" >&2
  exit 1
fi

for spec in "${specs[@]}"; do
  IFS=: read -r fixture reason <<<"$spec"
  image="$build/leanos-${version}-x86_64-return-${fixture}.iso"
  if [[ -n "$selected" && -n "${LEANOS_SERIAL_LOG:-}" ]]; then
    log="$LEANOS_SERIAL_LOG"
  else
    log="$build/return-corruption-${fixture}.serial.log"
  fi
  [[ -f "$image" ]] || {
    echo "error: missing return-corruption image '$image'" >&2; exit 1;
  }
  : > "$log"
  command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1 -m "${memory_mib}M"
    -display none -monitor none -serial "file:$log" -no-reboot -no-shutdown
    -nic none -device isa-debug-exit,iobase=0xf4,iosize=0x04 -cdrom "$image")
  qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
  printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2
  printf ' %q' "${command[@]}" >&2
  printf '\nSerial log: %s\n' "$log" >&2
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
  if [[ "$fixture" == capability-reuse-generation ]]; then
    grep -Fxq "LEANOS/9 CAPREUSE fixture=${fixture} stage=word-boundary result=INJECTED" \
      "$log" || {
      echo "error: fixture '$fixture' lacked its word-boundary injection record" >&2
      exit 1
    }
  elif [[ "$fixture" == fast-entry-sce-relaxation ||
      "$fixture" == fast-entry-lstar-relaxation ||
      "$fixture" == fast-entry-sysenter-eip-relaxation ||
      "$fixture" == fast-entry-star-relaxation ||
      "$fixture" == fast-entry-cstar-relaxation ||
      "$fixture" == fast-entry-sfmask-relaxation ||
      "$fixture" == fast-entry-sysenter-cs-relaxation ||
      "$fixture" == fast-entry-sysenter-esp-relaxation ]]; then
    grep -Fxq "LEANOS/9 RETURN fixture=${fixture} stage=machine-control result=INJECTED" \
      "$log" || {
      echo "error: fixture '$fixture' lacked its machine-control injection record" >&2
      exit 1
    }
  else
    grep -Fxq "LEANOS/9 RETURN fixture=${fixture} stage=outgoing-frame result=INJECTED" \
      "$log" || {
      echo "error: fixture '$fixture' lacked its outgoing-frame injection record" >&2
      exit 1
    }
  fi
  grep -Fxq "LEANOS/3 FINAL status=FAIL reason=${reason}" "$log" || {
    echo "error: fixture '$fixture' lacked typed rejection reason '$reason'" >&2
    exit 1
  }
  if [[ "$fixture" != capability-reuse-generation ]] &&
      grep -Eq '^LEANOS/5 ENTRY|^LEANOS/5 FINAL status=PASS' "$log"; then
    echo "error: fixture '$fixture' reached CPL3 or normal completion" >&2
    exit 1
  fi
  if [[ "$fixture" == capability-reuse-generation ]] &&
      grep -Eq '^LEANOS/9 CAPREUSE status=PASS|^LEANOS/10 FINAL status=PASS' "$log"; then
    echo "error: fixture '$fixture' reached capability-reuse completion" >&2
    exit 1
  fi
done

echo "Outgoing return-frame corruption QEMU fixtures passed (${#specs[@]} modes)"
