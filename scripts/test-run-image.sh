#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() { LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" LEANOS_QEMU="$root/tests/qemu-fixture.sh" LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$1.serial" ./scripts/run-image.sh "$tmp/image.iso"; }
invoke success >/dev/null 2>&1
set +e
invoke dma-prestate-forged >"$tmp/dma-prestate-forged.output" 2>&1
status=$?
set -e
[[ $status -ne 0 ]] &&
  grep -q 'failure_class=serial-protocol' "$tmp/dma-prestate-forged.output" || {
    cat "$tmp/dma-prestate-forged.output" >&2
    exit 1
  }
for spec in 'dma-missing serial-protocol' 'dma-forged serial-protocol' 'missing boot-allocation-trace' 'partial boot-allocation-trace' 'missing-scrub boot-allocation-trace' 'wrong-memory-map boot-allocation-trace' 'reordered-allocation boot-allocation-trace' 'missing-paging page-table-fixtures' 'entry-high-water-missing entry-stack-high-water' 'entry-high-water-invalid entry-stack-high-water' 'entry-high-water-duplicate entry-stack-high-water' 'entry-high-water-reordered entry-stack-high-water' 'entry-high-water-wrong-path entry-stack-high-water' 'omit-block serial-protocol' 'old-handoff serial-protocol' 'wrong-context serial-protocol' 'missing-wake serial-protocol' 'duplicate-wake serial-protocol' 'stolen-delivery serial-protocol' 'forged-pass serial-protocol' 'reuse-generation-ignored serial-protocol' 'reuse-truncated-handle serial-protocol' 'reuse-old-acts-replacement serial-protocol' 'reuse-forged-pass serial-protocol' 'reuse-wrong-caller serial-protocol' 'reuse-fresh-omitted serial-protocol' 'reuse-reordered serial-protocol' 'guest-error guest-error' 'hang timeout'; do read -r mode class <<< "$spec"; set +e; invoke "$mode" >"$tmp/$mode.output" 2>&1; status=$?; set -e; [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" && [[ -f "$tmp/$mode.serial" ]] || { cat "$tmp/$mode.output" >&2; exit 1; }; done
echo "QEMU runner success and negative fixture checks passed"
