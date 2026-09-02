#!/usr/bin/env bash
set -euo pipefail

if [[ "${1:-}" == --version ]]; then
  echo "QEMU emulator version 8.2.2 (fixture)"
  exit 0
fi

log=
for argument in "$@"; do
  [[ "$argument" == file:* ]] && log="${argument#file:}"
done
[[ -n "$log" ]] || exit 2

mode="${LEANOS_QEMU_PEER_CONTROL_FIXTURE_MODE:-pke}"
deny='LEANOS/13 EXTENDED-STATE event=deny subject=1 vector=7 instruction=x87 bank-write=prevented cleanup=complete peer=2'
pke='LEANOS/13 EXTENDED-STATE event=peer-control-injected control=pke bit=22 live=1 stage=pre-iretq result=PASS'
osxsave='LEANOS/13 EXTENDED-STATE event=peer-control-injected control=osxsave bit=18 live=1 stage=pre-iretq result=PASS'
failure='LEANOS/3 FINAL status=FAIL reason=extended-state-denial-peer-controls'

printf '%s\n' "$deny" > "$log"
case "$mode" in
pke) printf '%s\n' "$pke" >> "$log" ;;
osxsave) printf '%s\n' "$osxsave" >> "$log" ;;
missing) ;;
duplicate) printf '%s\n%s\n' "$pke" "$pke" >> "$log" ;;
wrong) printf '%s\n' \
  'LEANOS/13 EXTENDED-STATE event=peer-control-injected control=pke bit=18 live=1 stage=pre-iretq result=PASS' >> "$log" ;;
peer-entry) printf '%s\n%s\n' "$pke" \
  'LEANOS/13 EXTENDED-STATE event=peer-cpl3-entry subject=2' >> "$log" ;;
*) exit 2 ;;
esac
printf '%s\n' "$failure" >> "$log"
exit 35
