#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-${LEANOS_BOOT_DIR:-build/boot}/leanos-${version}-x86_64-extended-state-peer-pke.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/extended-state-peer-pke.serial.log}"

for tool in "$qemu" timeout; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing required tool '$tool'" >&2
    exit 1
  }
done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: invalid timeout" >&2; exit 1; }
[[ -f "$image" ]] || { echo "error: missing peer-PKE image '$image'" >&2; exit 1; }
mkdir -p "$(dirname "$log")"
: > "$log"
command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1 -m 128M
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
[[ $status -ne 124 && $status -ne 137 ]] || {
  echo "error: peer-PKE image timed out" >&2; exit 1;
}
[[ $status -eq 35 ]] || {
  echo "error: peer-PKE image exited $status instead of typed guest failure 35" >&2
  exit 1
}
failure='LEANOS/3 FINAL status=FAIL reason=extended-state-denial-peer-controls'
[[ $(grep -Fxc "$failure" "$log") -eq 1 ]] || {
  echo "error: peer-PKE image lacked its exact control-denial result" >&2
  exit 1
}
grep -Fq 'LEANOS/13 EXTENDED-STATE event=deny subject=1' "$log" || {
  echo "error: peer-PKE image did not reach authoritative peer dispatch" >&2
  exit 1
}
if grep -Eq '^LEANOS/13 EXTENDED-STATE event=peer|^LEANOS/13 FINAL status=PASS' "$log"; then
  echo "error: peer-PKE image published peer or final success after forbidden PKE" >&2
  exit 1
fi
echo "Extended-state peer-return PKE rejection passed"
