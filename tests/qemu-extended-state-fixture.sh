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
sed -i 's/projection=exact-rich/projection=scalar-checked/' "$log"
sed -i '/^LEANOS\/8 PAGING fixture=extra-mapping /a LEANOS/8 PAGING fixture=nmi-guard-mapping root=B level=pt page=6 expected=0 actual=9223372036854800387 result=REJECTED' "$log"
sed -i 's/readbacks=5 /readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 /' "$log"
sed -i 's/readback=exact stage=/readback=exact generated-result=0 stage=/' "$log"
sed -i '/^LEANOS\/15 DMA snapshot=/i\
LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:0.0 present=1 vendor=32902 device=10688 class=393216 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:1.0 present=1 vendor=4660 device=4369 class=196608 command-before=3 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:3.0 present=0 vendor=0 device=0 class=0 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:31.0 present=1 vendor=32902 device=10520 class=393472 command-before=3 command-after=0 assigned=0 bridge=1 multifunction=1 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:31.2 present=1 vendor=32902 device=10530 class=67073 command-before=7 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:31.3 present=1 vendor=32902 device=10544 class=787712 command-before=1 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted' "$log"

sed -i \
  -e 's|LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap|LEANOS/13 BOOT target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts|' \
  -e '/^LEANOS\/6 CONTROL/i LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS\
LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS\
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
