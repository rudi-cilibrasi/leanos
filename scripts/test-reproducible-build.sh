#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
version="${LEANOS_VERSION:-0.1.0}"
first="$(mktemp -d)"
trap 'rm -rf "$first"' EXIT

./scripts/build-image.sh
cp "build/boot/leanos-${version}-x86_64.iso" build/boot/leanos.elf \
  build/boot/leanos.map build/boot/SOURCE_REVISION \
  "build/boot/leanos-${version}-x86_64-fault-containment.iso" \
  build/boot/leanos-fault-containment.elf \
  build/boot/leanos-fault-containment.map \
  build/boot/boot-page-plan-fault-containment.final.h \
  build/boot/fault-containment.disassembly.txt \
  build/boot/fault-containment-policy-report.txt \
  "build/boot/leanos-${version}-x86_64-fault-readonly-write.iso" \
  build/boot/leanos-fault-readonly-write.elf \
  build/boot/leanos-fault-readonly-write.map \
  build/boot/boot-page-plan-fault-readonly-write.final.h \
  build/boot/fault-readonly-write.disassembly.txt \
  build/boot/fault-readonly-write-policy-report.txt \
  "build/boot/leanos-${version}-x86_64-fault-nx-execute.iso" \
  build/boot/leanos-fault-nx-execute.elf \
  build/boot/leanos-fault-nx-execute.map \
  build/boot/boot-page-plan-fault-nx-execute.final.h \
  build/boot/fault-nx-execute.disassembly.txt \
  build/boot/fault-nx-execute-policy-report.txt \
  "build/boot/leanos-${version}-x86_64-fault-reserved-bit.iso" \
  build/boot/leanos-fault-reserved-bit.elf \
  build/boot/leanos-fault-reserved-bit.map \
  build/boot/boot-page-plan-fault-reserved-bit.final.h \
  build/boot/fault-reserved-bit.disassembly.txt \
  build/boot/fault-reserved-bit-policy-report.txt \
  "build/boot/leanos-${version}-x86_64-fault-walk-mismatch.iso" \
  build/boot/leanos-fault-walk-mismatch.elf \
  build/boot/leanos-fault-walk-mismatch.map \
  build/boot/boot-page-plan-fault-walk-mismatch.final.h \
  build/boot/fault-walk-mismatch.disassembly.txt \
  build/boot/fault-walk-mismatch-policy-report.txt \
  "build/boot/leanos-${version}-x86_64-fault-stale-translation.iso" \
  build/boot/leanos-fault-stale-translation.elf \
  build/boot/leanos-fault-stale-translation.map \
  build/boot/boot-page-plan-fault-stale-translation.final.h \
  build/boot/fault-stale-translation.disassembly.txt \
  build/boot/fault-stale-translation-policy-report.txt "$first/"
./scripts/build-image.sh

for artifact in "leanos-${version}-x86_64.iso" leanos.elf leanos.map \
  SOURCE_REVISION "leanos-${version}-x86_64-fault-containment.iso" \
  leanos-fault-containment.elf leanos-fault-containment.map \
  boot-page-plan-fault-containment.final.h \
  fault-containment.disassembly.txt fault-containment-policy-report.txt \
  "leanos-${version}-x86_64-fault-readonly-write.iso" \
  leanos-fault-readonly-write.elf leanos-fault-readonly-write.map \
  boot-page-plan-fault-readonly-write.final.h \
  fault-readonly-write.disassembly.txt \
  fault-readonly-write-policy-report.txt \
  "leanos-${version}-x86_64-fault-nx-execute.iso" \
  leanos-fault-nx-execute.elf leanos-fault-nx-execute.map \
  boot-page-plan-fault-nx-execute.final.h \
  fault-nx-execute.disassembly.txt fault-nx-execute-policy-report.txt \
  "leanos-${version}-x86_64-fault-reserved-bit.iso" \
  leanos-fault-reserved-bit.elf leanos-fault-reserved-bit.map \
  boot-page-plan-fault-reserved-bit.final.h \
  fault-reserved-bit.disassembly.txt fault-reserved-bit-policy-report.txt \
  "leanos-${version}-x86_64-fault-walk-mismatch.iso" \
  leanos-fault-walk-mismatch.elf leanos-fault-walk-mismatch.map \
  boot-page-plan-fault-walk-mismatch.final.h \
  fault-walk-mismatch.disassembly.txt fault-walk-mismatch-policy-report.txt \
  "leanos-${version}-x86_64-fault-stale-translation.iso" \
  leanos-fault-stale-translation.elf leanos-fault-stale-translation.map \
  boot-page-plan-fault-stale-translation.final.h \
  fault-stale-translation.disassembly.txt \
  fault-stale-translation-policy-report.txt; do
  if ! cmp -s "$first/$artifact" "build/boot/$artifact"; then
    echo "error: repeated build changed $artifact" >&2
    sha256sum "$first/$artifact" "build/boot/$artifact" >&2
    exit 1
  fi
done

echo "Repeated base/reason-sensitive fault images, including stale-translation artifacts, ELFs, maps, plans, policies, and revision are byte-identical"
