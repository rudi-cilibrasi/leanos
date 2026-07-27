#!/usr/bin/env bash
set -euo pipefail

[[ "${1:-}" == --version ]] && {
  echo "QEMU DMA unknown-device fixture version 1"
  exit 0
}
log=""
for argument in "$@"; do
  [[ "$argument" == file:* ]] && log="${argument#file:}"
done
[[ -n "$log" ]] || exit 2
terminal='LEANOS/3 FINAL status=FAIL reason=dma-inventory'

case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
  success) echo "$terminal" > "$log"; exit 35 ;;
  missing) : > "$log"; exit 35 ;;
  duplicate) printf '%s\n%s\n' "$terminal" "$terminal" > "$log"; exit 35 ;;
  wrong-reason) echo 'LEANOS/3 FINAL status=FAIL reason=dma-identity' > "$log"; exit 35 ;;
  reached-cpl3) printf '%s\n%s\n' "$terminal" \
    'LEANOS/5 ENTRY subject=1 address-space=1 cpl=3 yielding=0' > "$log"; exit 35 ;;
  forged-pass) printf '%s\n%s\n' "$terminal" \
    'LEANOS/15 DMA snapshot=1 result=PASS' > "$log"; exit 35 ;;
  unrelated-guest-error) echo 'LEANOS/3 FINAL status=FAIL reason=page-table' > "$log"; exit 39 ;;
  reset) : > "$log"; exit 0 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
