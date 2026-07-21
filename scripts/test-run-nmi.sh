#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"

invoke() {
  LEANOS_QEMU="$root/tests/qemu-nmi-fixture.py" \
    LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" LEANOS_QMP_LOG="$tmp/$1.qmp.jsonl" \
    ./scripts/run-nmi.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
python3 - "$tmp/success.qmp.jsonl" <<'PY'
import json
import sys

records = [json.loads(line) for line in open(sys.argv[1], encoding="utf-8")]
assert [record["message"].get("execute") for record in records
        if record["direction"] == "host-to-qemu"] == [
            "qmp_capabilities", "inject-nmi"
        ]
PY
for spec in \
  'missing-ready nmi-ready' \
  'early-terminal injection-boundary' \
  'missing-injection qmp-injection' \
  'qmp-reject qmp-injection' \
  'wrong-record terminal-record' \
  'missing-terminal terminal-record' \
  'duplicate-terminal terminal-record' \
  'resumed terminal-record' \
  'corrupt-canary guest-evidence' \
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

echo "NMI runner success and negative fixture checks passed"
