#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() { LEANOS_BOOT_SCENARIO=preemption LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" LEANOS_QEMU="$root/tests/qemu-fixture.sh" LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$1.serial" ./scripts/run-image.sh "$tmp/image.iso"; }
invoke success >/dev/null 2>&1
for spec in 'interrupts-disabled serial-protocol' 'timer-missing serial-protocol' 'missing-second-tick serial-protocol' 'old-resumed serial-protocol' 'fresh-restart serial-protocol' 'cross-restored serial-protocol' 'stale-resume-cr3 serial-protocol' 'wrong-binding serial-protocol' 'duplicate-tick serial-protocol' 'corrupt-canary serial-protocol' 'corrupt-stack serial-protocol' 'corrupt-flags serial-protocol' 'corrupt-selectors serial-protocol'; do read -r mode class <<< "$spec"; set +e; invoke "$mode" >"$tmp/$mode.output" 2>&1; status=$?; set -e; [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" || { cat "$tmp/$mode.output" >&2; exit 1; }; done
echo "Preemption QEMU runner success and negative fixture checks passed"
