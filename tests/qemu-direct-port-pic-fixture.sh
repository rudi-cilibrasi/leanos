#!/usr/bin/env bash
# Fake QEMU for the direct-port PIC-mask probe (#130).  It reuses the shared
# blocking-ipc success transcript (corpus, allocation, paging fixtures, control
# and manifest snapshots) produced by qemu-fixture.sh, rewrites it into the
# direct-port-containment PIC transcript, then applies one controlled mutation so
# the runner's independent oracles can be exercised without a real boot.
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"
[[ "${1:-}" == --version ]] && { echo "QEMU direct-port-pic fixture version 1"; exit 0; }
log=""; for arg in "$@"; do [[ "$arg" == file:* ]] && log="${arg#file:}"; done
[[ -n "$log" ]] || exit 2
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mode="${LEANOS_QEMU_FIXTURE_MODE:-success}"

# The base transcript is generated exactly as the blocking-ipc success path so
# every shared record (256-vector oracle corpus, boot allocation, live
# page-table fixtures, ENTRY-MANIFEST, DIRECT-PORT-CONTROL, controls, probes) is
# byte-identical to a real boot.
set +e
LEANOS_BOOT_SCENARIO=blocking-ipc LEANOS_QEMU_FIXTURE_MODE=success \
  "$here/qemu-fixture.sh" "$@"
set -e
sed -i \
  -e "s|${LEANOS_SERIAL_10_BOOT} target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|${LEANOS_SERIAL_16_BOOT} target=x86_64-q35 subjects=2 schedule=direct-port-containment probe=pic-mask contract=v1 controls=wp,smep,smap|" \
  -e "/^$(leanos_serial_family_re 9) /d" -e "/^$(leanos_serial_family_re 10) /d" \
  -e "/^$(leanos_serial_re 6 COPY) /d" -e "/^$(leanos_serial_re 11 USER-FAULT) /d" \
  -e "/^$(leanos_serial_re 11 ENTRY-HIGH-WATER) /d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=B selected=1 result=PASS\$/d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=A selected=1 resumed=1 result=PASS\$/d" "$log"
cat >> "$log" <<EOF
${LEANOS_SERIAL_8_PAGING} root=A selected=1 resumed=1 result=PASS
${LEANOS_SERIAL_16_ENTER} subject=1 address-space=1 cpl=3 resources=owned
${LEANOS_SERIAL_16_DIRECT_PORT_DENIAL} subject=1 vector=13 error=0 origin=cpl3 port=33 direction=out width=byte purpose=user device-mutation=0 result=PASS
${LEANOS_SERIAL_16_DIRECT_PORT_TERMINATE} subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS
${LEANOS_SERIAL_16_DIRECT_PORT_DISPATCH} subject=2 address-space=2 source=lean-scheduler context=owned result=PASS
${LEANOS_SERIAL_8_PAGING} root=B selected=1 result=PASS
${LEANOS_SERIAL_16_DIRECT_PORT_CANARY} register=pic-mask port=33 programmed=255 observed=255 device-mutation=0 result=PASS
${LEANOS_SERIAL_16_DIRECT_PORT_PEER} subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS
${LEANOS_SERIAL_16_FINAL} status=PASS denied=1 resumed-a=0 peer-ran=1 device-mutation=0
EOF

case "$mode" in
  success) exit 33 ;;
  pic-write-executed)
    # The attacker's write to 0x21 actually executed.  Every serial claim of
    # containment above is forged, but the kernel-owned mask read-back observed
    # a cleared mask and fail-stopped: the independent oracle wins.
    sed -i "/^$(leanos_serial_re 16 DIRECT-PORT-CANARY) /,\$d" "$log"
    echo "${LEANOS_SERIAL_3_FINAL} status=FAIL reason=direct-port-pic-canary" >> "$log"
    exit 35 ;;
  pic-canary-mutated) sed -i 's/observed=255/observed=0/' "$log"; exit 33 ;;
  pic-canary-missing) sed -i "/^$(leanos_serial_re 16 DIRECT-PORT-CANARY) /d" "$log"; exit 33 ;;
  forged-denial) sed -i "/^$(leanos_serial_re 16 DIRECT-PORT-DENIAL) /d" "$log"; exit 33 ;;
  forged-pass) sed -i "/^$(leanos_serial_family_re 16) /d" "$log"; exit 33 ;;
  attacker-selected-b)
    sed -i 's/DIRECT-PORT-DISPATCH subject=2/DIRECT-PORT-DISPATCH subject=3/' "$log"
    exit 33 ;;
  stale-cr3)
    sed -i 's/DIRECT-PORT-DISPATCH subject=2 address-space=2/DIRECT-PORT-DISPATCH subject=2 address-space=1/' "$log"
    exit 33 ;;
  reordered)
    sed -i -e "s/^$(leanos_serial_re 16 DIRECT-PORT-TERMINATE) /$(leanos_serial_family_re 16) __SWAP__ /" \
      -e "s/^$(leanos_serial_re 16 DIRECT-PORT-DISPATCH) /$(leanos_serial_re 16 DIRECT-PORT-TERMINATE) /" \
      -e "s/^$(leanos_serial_family_re 16) __SWAP__ /$(leanos_serial_re 16 DIRECT-PORT-DISPATCH) /" "$log"
    exit 33 ;;
  guest-error) echo "${LEANOS_SERIAL_16_FINAL} status=FAIL reason=forced" >> "$log"; exit 35 ;;
  reset) exit 0 ;;
  triple-fault) exit 43 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
