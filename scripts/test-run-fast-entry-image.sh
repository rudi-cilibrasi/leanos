#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null

invoke() {
  local mechanism="$1" mode="$2"
  LEANOS_BOOT_SCENARIO="fast-entry-${mechanism}" \
    LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
    LEANOS_QEMU="$root/tests/qemu-fast-entry-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$mode" \
    LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/${mechanism}-${mode}.serial" \
    LEANOS_FAST_ENTRY_SNAPSHOT="$tmp/${mechanism}-${mode}.snapshot" \
    ./scripts/run-image.sh "$tmp/image.iso"
}

invoke syscall success >/dev/null 2>&1
invoke sysenter success >/dev/null 2>&1
for mechanism in syscall sysenter; do
  [[ $(wc -l < "$tmp/${mechanism}-success.snapshot") -eq 3 ]] || {
    echo "missing fast-entry snapshot for $mechanism" >&2
    exit 1
  }
done

for spec in \
    'missing-manifest serial-protocol' \
    'missing-control serial-protocol' \
    'wrong-vector serial-protocol' \
    'wrong-error-shape serial-protocol' \
    'stale-binding serial-protocol' \
    'unexpected-target serial-protocol' \
    'policy-relaxation serial-protocol' \
    'attacker-selected-survivor serial-protocol' \
    'kernel-contained serial-protocol' \
    'direct-handler serial-protocol' \
    'partial serial-protocol' \
    'reordered serial-protocol' \
    'reset qemu-error' \
    'triple-fault qemu-error' \
    'hang timeout'; do
  read -r mode class <<< "$spec"
  set +e
  invoke syscall "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -q "failure_class=$class" "$tmp/$mode.output"; then
    cat "$tmp/$mode.output" >&2
    exit 1
  fi
done

echo "Fast-entry QEMU runner success and negative fixture checks passed"
