#!/usr/bin/env bash
# Fake QEMU for run-device-service-rejection.sh (#482): writes a serial log in
# the shape the selected mode names and exits like the guest would.
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

if [[ "${1:-}" == --version ]]; then
  echo "QEMU emulator version 8.2.2 (fixture)"
  exit 0
fi

log=
for argument in "$@"; do
  [[ "$argument" == file:* ]] && log="${argument#file:}"
done
[[ -n "$log" ]] || exit 2

mode="${LEANOS_QEMU_DEVICE_SERVICE_FIXTURE_MODE:-rejected}"
assign="${LEANOS_SERIAL_21_VTD_ASSIGN} bdf=0:2.0 requester=16 stage=post-translation result=PASS"
failure="${LEANOS_SERIAL_3_FINAL} status=FAIL reason=dma-live-assignment-command"

: > "$log"
case "$mode" in
rejected) printf '%s\n%s\n' "$assign" "$failure" >> "$log" ;;
pre-assignment) printf '%s\n' "$failure" >> "$log" ;;
wrong-reason) printf '%s\n%s\n' "$assign" \
  "${LEANOS_SERIAL_3_FINAL} status=FAIL reason=dma-live-command" >> "$log" ;;
passed) printf '%s\n%s\n' "$assign" "${LEANOS_SERIAL_10_FINAL} status=PASS" >> "$log"
  exit 33 ;;
hang) sleep 30 ;;
*) exit 2 ;;
esac
exit 35
