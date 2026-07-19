#!/usr/bin/env bash
set -euo pipefail

[[ "${1:-}" == --version ]] && {
  echo "QEMU entry-stack overflow fixture version 1"
  exit 0
}
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2
terminal='LEANOS/11 ENTRY-STACK-OVERFLOW reason=guard-crossing vector=8 error=0 ist=1 rsp=in-range canaries=intact guard=unmapped adjacent=intact handler=none return=none'

case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
  success) echo "$terminal" > "$log"; exit 37 ;;
  missing) : > "$log"; exit 37 ;;
  partial) echo "${terminal% return=none}" > "$log"; exit 37 ;;
  duplicate) printf '%s\n%s\n' "$terminal" "$terminal" > "$log"; exit 37 ;;
  reordered) echo 'LEANOS/11 ENTRY-HIGH-WATER path=syscall observed-bytes=512 usable-bytes=16384 margin-bytes=15872 authority=diagnostic result=PASS' > "$log"; echo "$terminal" >> "$log"; exit 37 ;;
  wrong-vector) echo "${terminal/vector=8/vector=14}" > "$log"; exit 37 ;;
  wrong-ist) echo "${terminal/ist=1/ist=0}" > "$log"; exit 37 ;;
  wrong-rsp) echo "${terminal/rsp=in-range/rsp=out-of-range}" > "$log"; exit 37 ;;
  mapped-guard) echo "${terminal/guard=unmapped/guard=mapped}" > "$log"; exit 37 ;;
  stale-rsp0) echo "${terminal/reason=guard-crossing/reason=stale-rsp0}" > "$log"; exit 37 ;;
  adjacent-write) echo "${terminal/adjacent=intact/adjacent=modified}" > "$log"; exit 37 ;;
  direct-handler) echo "${terminal/handler=none/handler=reached}" > "$log"; exit 37 ;;
  returned) echo "${terminal/return=none/return=iretq}" > "$log"; exit 37 ;;
  forged-pass) printf '%s\n' "$terminal" 'LEANOS/11 ENTRY-STACK-OVERFLOW status=PASS' > "$log"; exit 37 ;;
  guest-evidence) echo 'LEANOS/11 ENTRY-STACK-OVERFLOW evidence=invalid status=FAIL' > "$log"; exit 39 ;;
  reset) : > "$log"; exit 0 ;;
  triple-fault) : > "$log"; exit 0 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
