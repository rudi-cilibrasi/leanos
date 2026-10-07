#!/usr/bin/env bash
# Boot one device-service controlled negative (#482). The image enables the
# assigned xHCI function behind live VT-d tables, then a function outside the
# plan regains decode and bus mastering; the outbound gate must stop the image
# before CPL3 with the exact typed reason, after the assignment record passed.
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
reason="${LEANOS_DEVICE_SERVICE_REJECTION_REASON:-}"
image="${1:-}"
log="${LEANOS_SERIAL_LOG:-build/boot/device-service-rejection.serial.log}"

for tool in "$qemu" timeout; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing required tool '$tool'" >&2
    exit 1
  }
done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: invalid timeout" >&2; exit 1; }
[[ "$reason" =~ ^[a-z][a-z0-9-]*$ ]] || {
  echo "error: missing or malformed expected rejection reason" >&2; exit 1;
}
[[ -f "$image" ]] || { echo "error: missing device-service negative image '$image'" >&2; exit 1; }
mkdir -p "$(dirname "$log")"
: > "$log"
qmp_dir="$(mktemp -d)"
trap 'rm -rf "$qmp_dir"' EXIT
command=()
leanos_q35_device_service_command command "$qmp_dir/qmp.sock" "$qemu" 128 "$log" "$image"
qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2
printf ' %q' "${command[@]}" >&2
printf '\nSerial log: %s\n' "$log" >&2
set +e
timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"
status=$?
set -e
[[ $status -ne 124 && $status -ne 137 ]] || {
  echo "failure_class=timeout: device-service negative timed out" >&2; exit 1;
}
[[ $status -eq 35 ]] || {
  echo "error: device-service negative exited $status instead of typed guest failure 35" >&2
  exit 1
}
terminal="${LEANOS_SERIAL_3_FINAL} status=FAIL reason=${reason}"
[[ $(grep -Fxc "$terminal" "$log") -eq 1 &&
   $(grep -c "^${LEANOS_SERIAL_3_FINAL} " "$log") -eq 1 ]] || {
  echo "error: device-service negative lacked its exact rejection '$reason'" >&2
  exit 1
}
[[ $(grep -Ec "^${LEANOS_SERIAL_21_VTD_ASSIGN} .*result=PASS" "$log" || true) -eq 1 ]] || {
  echo "error: device-service negative failed before its assigned tables were live" >&2
  exit 1
}
! grep -Eq "^${LEANOS_SERIAL_10_FINAL} status=PASS" "$log" || {
  echo "error: device-service negative reached a passing final record" >&2
  exit 1
}
echo "LeanOS device-service negative passed: $reason (post-assignment)"
