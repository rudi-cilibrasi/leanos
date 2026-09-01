#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"

invoke() {
  local mode="$1" scenario="${2:-kernel-entry}"
  LEANOS_QEMU="$root/tests/qemu-nmi-fixture.py" \
    LEANOS_QEMU_FIXTURE_MODE="$mode" LEANOS_NMI_SCENARIO="$scenario" \
    LEANOS_QEMU_TIMEOUT_SECONDS=5 \
    LEANOS_SERIAL_LOG="$tmp/$mode-$scenario.serial" \
    LEANOS_QMP_LOG="$tmp/$mode-$scenario.qmp.jsonl" \
    ./scripts/run-nmi.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
invoke success cpl3-spin >/dev/null 2>&1
invoke disconnect-after-inject >/dev/null 2>&1
invoke reset-after-inject >/dev/null 2>&1
python3 - "$tmp/success-kernel-entry.qmp.jsonl" <<'PY'
import json
import sys

records = [json.loads(line) for line in open(sys.argv[1], encoding="utf-8")]
assert [record["message"].get("execute") for record in records
        if record["direction"] == "host-to-qemu"] == [
            "qmp_capabilities", "inject-nmi"
        ]
PY
for mode in disconnect-after-inject reset-after-inject; do
  python3 - "$tmp/$mode-kernel-entry.qmp.jsonl" <<'PY'
import json
import sys

records = [json.loads(line) for line in open(sys.argv[1], encoding="utf-8")]
assert len(records) == 4
assert records[-1] == {
    "direction": "host-to-qemu", "message": {"execute": "inject-nmi"}
}
PY
done
for spec in \
  'missing-ready nmi-ready' \
  'early-terminal injection-boundary' \
  'missing-injection qmp-injection' \
  'qmp-reject qmp-injection' \
  'wrong-record terminal-record' \
  'missing-terminal terminal-record' \
  'disconnect-no-terminal terminal-record' \
  'duplicate-terminal terminal-record' \
  'resumed terminal-record' \
  'corrupt-canary guest-evidence' \
  'reject guest-evidence' \
  'reset qemu-error' \
  'reset-after-inject-wrong-exit qemu-error' \
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

echo "NMI runner success and negative fixture checks passed"
