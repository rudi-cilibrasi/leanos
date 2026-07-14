#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

for tool in qemu-system-x86_64 timeout; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: missing required tool '$tool'; install qemu-system-x86=1:8.2.2+ds-0ubuntu1.17 and coreutils=9.4-3ubuntu6.2" >&2
    exit 1
  fi
done

image="${1:-build/boot/leanos-0.1.0-x86_64.iso}"
if [[ ! -f "$image" ]]; then
  echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2
  exit 1
fi

log="build/boot/serial.log"
rm -f "$log"
set +e
timeout 30s qemu-system-x86_64 \
  -machine q35,accel=tcg -cpu max -smp 1 -m 128M \
  -display none -monitor none -serial "file:$log" -no-reboot \
  -no-shutdown -nic none -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -cdrom "$image"
status=$?
set -e

if [[ $status -ne 33 ]]; then
  echo "error: QEMU exit status $status (expected guest-success status 33)" >&2
  [[ -f "$log" ]] && cat "$log" >&2
  exit 1
fi

expected="$(mktemp)"
trap 'rm -f "$expected"' EXIT
printf '%s\n' \
  'LEANOS/1 BOOT target=x86_64-q35' \
  'LEANOS/1 TRANSITION state=0 command=1 result=1' \
  'LEANOS/1 TRANSITION state=0 command=7 result=0' \
  'LEANOS/1 FINAL status=PASS' > "$expected"
if ! cmp -s "$expected" "$log"; then
  echo "error: serial protocol was incomplete or unexpected" >&2
  diff -u "$expected" "$log" >&2 || true
  exit 1
fi
echo "LeanOS boot smoke test passed; serial log: $log"
