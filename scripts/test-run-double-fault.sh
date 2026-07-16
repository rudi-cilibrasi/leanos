#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"

invoke() {
  LEANOS_QEMU="$root/tests/qemu-double-fault-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    ./scripts/run-double-fault.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
  'missing terminal-record' \
  'duplicate terminal-record' \
  'wrong-vector terminal-record' \
  'wrong-ist terminal-record' \
  'wrong-rsp terminal-record' \
  'ordinary-stack terminal-record' \
  'direct-handler terminal-record' \
  'returned terminal-record' \
  'forged-pass terminal-record' \
  'guest-evidence guest-evidence' \
  'reset qemu-error' \
  'hang timeout'; do
  read -r mode class <<< "$spec"
  set +e
  invoke "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -q "failure_class=$class" "$tmp/$mode.output"; then
    cat "$tmp/$mode.output" >&2
    exit 1
  fi
done

echo "Double-fault runner success and negative fixture checks passed"
