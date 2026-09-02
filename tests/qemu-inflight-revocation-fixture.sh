#!/usr/bin/env bash
set -euo pipefail

[[ "${1:-}" == --version ]] && {
  echo "QEMU inflight-revocation fixture version 1"
  exit 0
}

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mode="${LEANOS_INFLIGHT_REVOCATION_FIXTURE_MODE:-success}"
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
    'LEANOS/23 BOOT target=x86_64-q35 subjects=2 schedule=inflight-revocation-v1 controls=wp,smep,smap boundary=generated-composite' \
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
  -e 's|LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|LEANOS/23 BOOT target=x86_64-q35 subjects=2 schedule=inflight-revocation-v1 controls=wp,smep,smap boundary=generated-composite|' \
  -e '/^LEANOS\/9 /d' \
  -e '/^LEANOS\/10 /d' \
  -e '/^LEANOS\/6 COPY /d' \
  -e '/^LEANOS\/11 USER-FAULT /d' \
  -e '/^LEANOS\/11 ENTRY-HIGH-WATER /d' \
  -e '/^LEANOS\/8 PAGING root=B selected=1/d'

cat >> "$log" <<'EOF'
LEANOS/23 ENTER subject=1 address-space=1 cpl=3 source=owned-context authority=slot2:revoke result=PASS
LEANOS/23 OFFER subject=1 address-space=1 origin=cpl3 source-handle=131073 transfer-endpoint=131073 child=7 parent=2 rights=send sealed=1 installed=0 payload0=51966 payload1=48879 control=2121985 value=0 result=PASS
LEANOS/23 REVOKE-DENIAL subject=1 authority-slot=1 root-slot=1 reason=missingRevoke state=unchanged control=5267713 value=0 result=PASS
LEANOS/23 REVOKE-DENIAL subject=1 authority-slot=2 root-slot=0 reason=objectMismatch state=unchanged control=5333249 value=0 result=PASS
LEANOS/23 REVOKE subject=1 authority-slot=2 root-slot=1 root=2 descendant=7 installed-cleared=1 envelope=cleared pending=cleared history=retained next-identity=8 control=5399041 value=0 result=PASS
LEANOS/23 REVOKE-DENIAL subject=1 authority-slot=2 root-slot=1 reason=staleSlot state=unchanged control=5464577 value=0 result=PASS
LEANOS/23 OFFER-DENIAL subject=1 source-handle=131073 reason=staleEndpoint state=unchanged control=5530113 value=0 result=PASS
LEANOS/23 DISPATCH subject=2 address-space=2 source=authoritative-resumable-context control=5595905 value=0 result=PASS
LEANOS/23 ENTER subject=2 address-space=2 origin=cpl3 context=fresh result=PASS
LEANOS/23 CANCELED-RECEIPT subject=2 address-space=2 origin=cpl3 transfer-endpoint=196608 destination-slot=3 reason=empty delivered=0 installed=0 handle=none control=2188033 value=0 result=PASS
LEANOS/23 REPLACE subject=2 source-slot=0 destination-slot=3 generation=8 canceled-generation=7 aliased=0 history=retained control=2384897 value=0 result=PASS
LEANOS/23 CANCELED-HANDLE-DENIAL subject=2 handle=458755 operation=send authorized=0 reason=staleHandle state=unchanged control=5661697 value=0 result=PASS
LEANOS/23 FRESH-SEND subject=2 handle=524291 endpoint-slot=3 payload0=4369 payload1=8738 right=send authorized=1 mailbox=filled control=5727489 value=0 result=PASS
LEANOS/23 UNRELATED slots-a-except-1=unchanged slots-b-except-3=unchanged contexts=unchanged canaries=preserved mailbox=fresh-message-only result=PASS
LEANOS/23 FINAL status=PASS offer=1 revoke=1 envelope-and-pending=cleared canceled-receipt-denied=1 replacement-generation=8 canceled-handle-denied=1 fresh-send=1 unrelated=unchanged
EOF

case "$mode" in
  success) ;;
  envelope-only)
    rewrite_log '/^LEANOS\/23 REVOKE /s/pending=cleared/pending=retained/' ;;
  pending-only)
    rewrite_log '/^LEANOS\/23 REVOKE /s/envelope=cleared/envelope=retained/' ;;
  installed-after-revoke)
    rewrite_log '/^LEANOS\/23 CANCELED-RECEIPT /s/installed=0/installed=1/' ;;
  delivered-handle)
    rewrite_log '/^LEANOS\/23 CANCELED-RECEIPT /s/value=0/value=458755/' ;;
  old-identity-reused)
    rewrite_log '/^LEANOS\/23 REPLACE /s/generation=8/generation=7/' ;;
  truncated-generation)
    rewrite_log '/^LEANOS\/23 CANCELED-HANDLE-DENIAL /s/handle=458755/handle=3/' ;;
  caller-chosen-root)
    rewrite_log '/^LEANOS\/23 REVOKE /s/root=2 /root=3 /' ;;
  stale-b-context)
    rewrite_log '/^LEANOS\/23 ENTER subject=2 /s/address-space=2/address-space=1/' ;;
  old-adapter)
    rewrite_log '/^LEANOS\/23 BOOT /s/boundary=generated-composite/boundary=stateless/' ;;
  state-splice)
    rewrite_log '/^LEANOS\/23 REVOKE /s/control=5399041/control=5399297/' ;;
  replayed-offer)
    rewrite_log '/^LEANOS\/23 OFFER-DENIAL /s/state=unchanged/state=offered/' ;;
  missing)
    rewrite_log '/^LEANOS\/23 REVOKE /d' ;;
  reordered)
    rewrite_log \
      -e 's/^LEANOS\/23 REVOKE /LEANOS\/23 __SWAP__ /' \
      -e 's/^LEANOS\/23 CANCELED-RECEIPT /LEANOS\/23 REVOKE /' \
      -e 's/^LEANOS\/23 __SWAP__ /LEANOS\/23 CANCELED-RECEIPT /' ;;
  forged-final)
    rewrite_log '/^LEANOS\/23 FINAL /s/canceled-receipt-denied=1/canceled-receipt-denied=0/' ;;
  guest-error)
    exit 35 ;;
  *)
    echo "unknown inflight-revocation fixture mode: $mode" >&2
    exit 2 ;;
esac
exit 33
