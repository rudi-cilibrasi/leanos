#!/usr/bin/env bash
set -euo pipefail

[[ "${1:-}" == --version ]] && { echo "QEMU extended-state fixture version 1"; exit 0; }

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2

mode="${LEANOS_QEMU_FIXTURE_MODE:-success}"
case "$mode" in
  hang) sleep 10 ;;
  reset) exit 0 ;;
  triple-fault) exit 1 ;;
esac

set +e
LEANOS_QEMU_FIXTURE_MODE=legacy-success "$repo_root/tests/qemu-fixture.sh" "$@"
status=$?
set -e
[[ $status -eq 33 ]] || exit "$status"

sed -i \
  -e 's|LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap|LEANOS/13 BOOT target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts|' \
  -e '/^LEANOS\/6 CONTROL/i LEANOS/12 ENTRY-MANIFEST ordinary=5 extended=6,7 auxiliary=2 extra=0 rsp0=entry-stack ist1=df-stack result=PASS\
LEANOS/13 EXTENDED-STATE cpuid.1.x87=1 cpuid.1.mmx=1 cpuid.1.sse=1 cpuid.1.sse2=1 cpuid.1.xsave=1 cpuid.1.osxsave=0 cpuid.1.avx=1 cpu=max result=PASS' \
  -e '/^LEANOS\/6 COPY/d' \
  -e '/^LEANOS\/5 /d' \
  -e '/^LEANOS\/8 PAGING root=B selected=1 result=PASS$/d' \
  -e '/^LEANOS\/6 CLEANUP/a LEANOS/13 EXTENDED-STATE event=enter subject=1 address-space=1 instruction=x87 expected-vector=7\
LEANOS/13 EXTENDED-STATE event=deny subject=1 vector=7 instruction=x87 bank-write=prevented cleanup=complete peer=2\
LEANOS/13 EXTENDED-STATE event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved\
LEANOS/13 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1' \
  "$log"

case "$mode" in
  success) ;;
  missing-cpuid) sed -i '/EXTENDED-STATE cpuid/d' "$log" ;;
  missing-control) sed -i '/^LEANOS\/6 CONTROL/d' "$log" ;;
  missing-deny) sed -i '/event=deny/d' "$log" ;;
  missing-peer) sed -i '/event=peer/d' "$log" ;;
  reordered-records)
    sed -i \
      -e 's/^LEANOS\/13 EXTENDED-STATE event=enter /__EXTENDED_ENTER__ /' \
      -e 's/^LEANOS\/13 EXTENDED-STATE event=deny /LEANOS\/13 EXTENDED-STATE event=enter /' \
      -e 's/^__EXTENDED_ENTER__ /LEANOS\/13 EXTENDED-STATE event=deny /' \
      "$log"
    ;;
  forged-record) sed -i 's/bank-write=prevented/bank-write=prevented forged=1/' "$log" ;;
  resumed-a) sed -i 's/resumed-a=0/resumed-a=1/' "$log" ;;
  seeded-peer) sed -i 's/bank-write=prevented/bank-write=seeded/' "$log" ;;
  kernel-contained) sed -i 's/event=enter subject=1/event=enter origin=kernel subject=1/' "$log" ;;
  direct-handler) sed -i 's/event=enter subject=1/event=enter entry=direct subject=1/' "$log" ;;
  *) exit 2 ;;
esac

exit 33
