#!/usr/bin/env bash
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

[[ "${1:-}" == --version ]] && {
  echo "QEMU capability-transfer fixture version 1"
  exit 0
}

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mode="${LEANOS_CAPABILITY_TRANSFER_FIXTURE_MODE:-success}"
log=""
for argument in "$@"; do
  [[ "$argument" == file:* ]] && log="${argument#file:}"
done
[[ -n "$log" ]] || exit 2
rewrite_log() {
  local temporary="${log}.rewrite"
  sed "$@" "$log" > "$temporary"
  mv "$temporary" "$log"
}

if [[ "$mode" == hang ]]; then
  printf '%s\n' \
    "${LEANOS_SERIAL_22_BOOT} target=x86_64-q35 subjects=2 schedule=capability-transfer-v1 controls=wp,smep,smap boundary=generated-composite" \
    >"$log"
  sleep 120
  exit 0
fi

set +e
LEANOS_BOOT_SCENARIO=blocking-ipc \
  LEANOS_QEMU_FIXTURE_MODE=success \
  "$root/tests/qemu-fixture.sh" "$@"
status=$?
set -e
[[ $status -eq 33 ]] || exit "$status"

rewrite_log \
  -e "s|${LEANOS_SERIAL_10_BOOT} target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|${LEANOS_SERIAL_22_BOOT} target=x86_64-q35 subjects=2 schedule=capability-transfer-v1 controls=wp,smep,smap boundary=generated-composite|" \
  -e "/^$(leanos_serial_family_re 9) /d" \
  -e "/^$(leanos_serial_family_re 10) /d" \
  -e "/^$(leanos_serial_re 6 COPY) /d" \
  -e "/^$(leanos_serial_re 11 USER-FAULT) /d" \
  -e "/^$(leanos_serial_re 11 ENTRY-HIGH-WATER) /d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=B selected=1/d"

cat >> "$log" <<EOF
${LEANOS_SERIAL_22_ENTER} subject=1 address-space=1 cpl=3 source=owned-context result=PASS
${LEANOS_SERIAL_22_OFFER} subject=1 address-space=1 origin=cpl3 source-handle=131073 transfer-endpoint=131073 child=6 parent=2 rights=send sealed=1 installed=0 payload0=51966 payload1=48879 control=2118145 value=0 result=PASS
${LEANOS_SERIAL_22_DISPATCH} subject=2 address-space=2 source=authoritative-resumable-context control=4870913 value=0 result=PASS
${LEANOS_SERIAL_22_ENTER} subject=2 address-space=2 origin=cpl3 context=fresh result=PASS
${LEANOS_SERIAL_22_SEALED_DENIAL} subject=2 handle=393219 operation=send authorized=0 reason=not-installed state=unchanged control=4674305 value=0 result=PASS
${LEANOS_SERIAL_22_ACCEPT} subject=2 address-space=2 origin=cpl3 transfer-endpoint=196608 destination-slot=3 child=6 generation=6 handle=393219 sealed=0 installed=1 exactly-once=1 control=2184193 value=393219 result=PASS
${LEANOS_SERIAL_22_DELEGATED_SEND} subject=2 handle=393219 endpoint=3 payload0=41332 payload1=45428 right=send authorized=1 mailbox=filled control=4740353 value=0 result=PASS
${LEANOS_SERIAL_22_EXCESS_RIGHT_DENIAL} subject=2 handle=393219 operation=receive authorized=0 reason=rights state=unchanged mailbox=filled control=4805889 value=0 result=PASS
${LEANOS_SERIAL_22_UNRELATED} slots-a=unchanged slots-b-except-3=unchanged contexts=unchanged canaries=preserved mailbox=delegated-message-only result=PASS
${LEANOS_SERIAL_22_FINAL} status=PASS offer=1 sealed-denied=1 receipt=1 exact-handle=1 delegated-send=1 excess-right-denied=1 unrelated=unchanged
EOF

case "$mode" in
  success) ;;
  payload-authority)
    rewrite_log 's/source-handle=131073/source-handle=51966/' ;;
  rights-widened)
    rewrite_log 's/rights=send /rights=send,receive /' ;;
  installed-early)
    rewrite_log "/^$(leanos_serial_re 22 OFFER) /s/installed=0/installed=1/" ;;
  truncated-handle)
    rewrite_log "/^$(leanos_serial_re 22 ACCEPT) /s/handle=393219/handle=3/" ;;
  replaced-return)
    rewrite_log "/^$(leanos_serial_re 22 ACCEPT) /s/value=393219/value=393220/" ;;
  stale-a-context)
    rewrite_log "/^$(leanos_serial_re 22 ENTER) subject=2 /s/address-space=2/address-space=1/" ;;
  old-adapter)
    rewrite_log "/^$(leanos_serial_re 22 BOOT) /s/boundary=generated-composite/boundary=stateless/" ;;
  state-splice)
    rewrite_log "/^$(leanos_serial_re 22 SEALED-DENIAL) /s/control=4674305/control=4674561/" ;;
  missing)
    rewrite_log "/^$(leanos_serial_re 22 ACCEPT) /d" ;;
  reordered)
    rewrite_log \
      -e "s/^$(leanos_serial_re 22 ACCEPT) /$(leanos_serial_family_re 22) __SWAP__ /" \
      -e "s/^$(leanos_serial_re 22 DELEGATED-SEND) /$(leanos_serial_re 22 ACCEPT) /" \
      -e "s/^$(leanos_serial_family_re 22) __SWAP__ /$(leanos_serial_re 22 DELEGATED-SEND) /" ;;
  forged-final)
    rewrite_log "/^$(leanos_serial_re 22 FINAL) /s/exact-handle=1/exact-handle=0/" ;;
  guest-error)
    exit 35 ;;
  *)
    echo "unknown capability-transfer fixture mode: $mode" >&2
    exit 2 ;;
esac
exit 33
