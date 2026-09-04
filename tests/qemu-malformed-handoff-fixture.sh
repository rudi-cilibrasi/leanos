#!/usr/bin/env bash
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

[[ "${1:-}" == --version ]] && {
  echo "QEMU malformed-handoff fixture version 1"
  exit 0
}
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2
reason="${LEANOS_HANDOFF_REJECTION_REASON:-decode-rejected}"
terminal="${LEANOS_SERIAL_7_BOOTALLOC} status=FAIL reason=$reason"

case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
  success) echo "$terminal" > "$log"; exit 35 ;;
  missing) : > "$log"; exit 35 ;;
  wrong-reason) echo "${LEANOS_SERIAL_7_BOOTALLOC} status=FAIL reason=no-frame" > "$log"; exit 35 ;;
  authority-leak)
    printf '%s\n%s\n' "$terminal" \
      "${LEANOS_SERIAL_7_ALLOC} frame=800 firmware-usable=1 boot-accessible=1 reserved=0 result=PASS" \
      > "$log"
    exit 35
    ;;
  reset) : > "$log"; exit 0 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
