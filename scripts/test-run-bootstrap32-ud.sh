#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"

invoke() {
  LEANOS_QEMU="$root/tests/qemu-bootstrap32-ud-fixture.py" \
    LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    ./scripts/run-bootstrap32-ud.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
  'missing-record terminal-record' \
  'wrong-record terminal-record' \
  'duplicate terminal-record' \
  'long-mode-escape terminal-record' \
  'ordinary-boot terminal-record' \
  'reject guest-evidence' \
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

echo "bootstrap32-ud runner success and negative fixture checks passed"
