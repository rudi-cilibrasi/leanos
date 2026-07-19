#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"

invoke() {
  LEANOS_QEMU="$root/tests/qemu-entry-stack-overflow-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    ./scripts/run-entry-stack-overflow.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
  'missing terminal-record' \
  'partial terminal-record' \
  'duplicate terminal-record' \
  'reordered terminal-record' \
  'wrong-vector terminal-record' \
  'wrong-ist terminal-record' \
  'wrong-rsp terminal-record' \
  'mapped-guard terminal-record' \
  'stale-rsp0 terminal-record' \
  'adjacent-write terminal-record' \
  'direct-handler terminal-record' \
  'returned terminal-record' \
  'forged-pass terminal-record' \
  'guest-evidence guest-evidence' \
  'reset qemu-error' \
  'triple-fault qemu-error' \
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

echo "Entry-stack overflow runner success and adversarial fixture checks passed"
