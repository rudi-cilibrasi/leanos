#!/usr/bin/env bash
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
probe="${LEANOS_FAULT_INTEGRITY_PROBE:-reserved-bit}"
elf="${LEANOS_FAULT_INTEGRITY_ELF:?}"
symbol_value() {
  local symbol="$1"
  printf '%u' "$((16#$(nm -n "$elf" | awk -v wanted="$symbol" '$3 == wanted { print $1 }')))"
}
if [[ "$probe" == reserved-bit ]]; then
  cr2="$(symbol_value user_a_nx_fault_instruction)"
  printf -v expected_leaf '%u' \
    "$(( (1 << 63) | (cr2 / 4096) * 4096 | 7 ))"
  expected_live_leaf="$expected_leaf"
  accelerator="${LEANOS_QEMU_ACCELERATOR:-tcg}"
  expected_error=12
  [[ "$accelerator" != kvm ]] || expected_error=13
  record="${LEANOS_SERIAL_14_PF_TERMINAL} codec=1 case=reserved-bit vector=14 error=${expected_error} access=read cr2=${cr2} rip=user-a-reserved-fault-instruction expected-leaf=${expected_leaf} live-leaf=${expected_live_leaf} authorization=0 route=144115188075855874 halt=absorbing containment=0 cleanup=0 dispatch=0 return=none"
else
  record="${LEANOS_SERIAL_14_PF_TERMINAL} codec=1 case=walk-mismatch vector=14 error=5 access=read cr2=0 rip=user-a-fault-instruction expected-leaf=9223372036854775809 live-leaf=9223372036854775811 authorization=1 route=144115188075855875 halt=absorbing containment=0 cleanup=0 dispatch=0 return=none"
fi
printf '%s\n' "${LEANOS_SERIAL_14_ENTER} subject=1 address-space=1 cpl=3 resources=owned fatal-only=1" "$record" > "$log"
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
success) exit 37 ;;
missing) sed -i '/PF-TERMINAL/d' "$log"; exit 37 ;;
duplicate) printf '%s\n' "$record" >> "$log"; exit 37 ;;
wrong-field) sed -i 's/ vector=14 / vector=13 /' "$log"; exit 37 ;;
containment) printf '%s\n' "${LEANOS_SERIAL_14_FAULT_ENTRY} vector=14 result=PASS" >> "$log"; exit 37 ;;
cleanup) printf '%s\n' "${LEANOS_SERIAL_14_TERMINATE} subject=1 result=PASS" >> "$log"; exit 37 ;;
peer-dispatch) printf '%s\n' "${LEANOS_SERIAL_14_DISPATCH} subject=2 result=PASS" >> "$log"; exit 37 ;;
user-return) printf '%s\n' "${LEANOS_SERIAL_14_PEER} subject=2 return=validated result=PASS" >> "$log"; exit 37 ;;
normal-success) printf '%s\n' "${LEANOS_SERIAL_14_FINAL} status=PASS" >> "$log"; exit 33 ;;
generic-error) exit 35 ;;
reset) exit 0 ;;
hang) sleep 60 ;;
*) exit 2 ;;
esac
