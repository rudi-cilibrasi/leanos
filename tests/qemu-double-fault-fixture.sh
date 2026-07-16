#!/usr/bin/env bash
set -euo pipefail

[[ "${1:-}" == --version ]] && {
  echo "QEMU double-fault fixture version 1"
  exit 0
}
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2
terminal='LEANOS/8 TERMINAL reason=double-fault vector=8 error=0 ist=1 rsp=in-range canaries=intact normal-stack=unmapped return=none'

case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
  success) echo "$terminal" > "$log"; exit 37 ;;
  missing) : > "$log"; exit 37 ;;
  duplicate) printf '%s\n%s\n' "$terminal" "$terminal" > "$log"; exit 37 ;;
  wrong-vector) echo "${terminal/vector=8/vector=14}" > "$log"; exit 37 ;;
  wrong-ist) echo "${terminal/ist=1/ist=0}" > "$log"; exit 37 ;;
  wrong-rsp) echo "${terminal/rsp=in-range/rsp=out-of-range}" > "$log"; exit 37 ;;
  ordinary-stack) echo "${terminal/normal-stack=unmapped/normal-stack=mapped}" > "$log"; exit 37 ;;
  direct-handler) echo "${terminal/reason=double-fault/reason=direct-handler}" > "$log"; exit 37 ;;
  returned) echo "${terminal/return=none/return=iretq}" > "$log"; exit 37 ;;
  forged-pass) printf '%s\n' "$terminal" 'LEANOS/8 TERMINAL status=PASS' > "$log"; exit 37 ;;
  guest-evidence) echo 'LEANOS/8 TERMINAL reason=double-fault evidence=invalid status=FAIL' > "$log"; exit 39 ;;
  reset) : > "$log"; exit 0 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
