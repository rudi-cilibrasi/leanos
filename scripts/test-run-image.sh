#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() { LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" LEANOS_QEMU="$root/tests/qemu-fixture.sh" LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$1.serial" ./scripts/run-image.sh "$tmp/image.iso"; }
invoke success >/dev/null 2>&1
for spec in 'missing boot-allocation-trace' 'partial boot-allocation-trace' 'missing-scrub boot-allocation-trace' 'wrong-memory-map boot-allocation-trace' 'reordered-allocation boot-allocation-trace' 'missing-paging serial-protocol' 'interrupts-disabled serial-protocol' 'timer-missing serial-protocol' 'old-resumed serial-protocol' 'wrong-binding serial-protocol' 'duplicate-tick serial-protocol' 'corrupt-canary serial-protocol' 'guest-error guest-error' 'hang timeout'; do read -r mode class <<< "$spec"; set +e; invoke "$mode" >"$tmp/$mode.output" 2>&1; status=$?; set -e; [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" && [[ -f "$tmp/$mode.serial" ]] || { cat "$tmp/$mode.output" >&2; exit 1; }; done
echo "QEMU runner success and negative fixture checks passed"
