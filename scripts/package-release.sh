#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tag="${1:-${GITHUB_REF_NAME:-}}"
if [[ ! "$tag" =~ ^v([0-9]+\.[0-9]+\.[0-9]+)$ ]]; then
  echo "error: release tag must be vMAJOR.MINOR.PATCH" >&2
  exit 1
fi
version="${BASH_REMATCH[1]}"
revision="$(git rev-parse HEAD)"
if [[ "$(git rev-list -n 1 "$tag")" != "$revision" ]]; then
  echo "error: tag $tag does not resolve to checked-out revision $revision" >&2
  exit 1
fi

evidence="build/evidence/emulator-evidence.json"
./scripts/run-emulator-evidence.py verify "$evidence" --version "$version"

release="$repo_root/build/release"
rm -rf "$release"
mkdir -p "$release"
cp "build/boot/leanos-${version}-x86_64.iso" \
  "$release/leanos-${version}-x86_64.iso"
cp build/boot/leanos.elf "$release/leanos-${version}-x86_64.elf"
cp build/boot/leanos.map "$release/leanos-${version}-x86_64.map"
cp build/boot/serial.log "$release/leanos-${version}-serial.log"
cp "build/boot/leanos-${version}-x86_64-preemption.iso" \
  "$release/leanos-${version}-x86_64-preemption.iso"
cp build/boot/leanos-preemption.elf \
  "$release/leanos-${version}-x86_64-preemption.elf"
cp build/boot/leanos-preemption.map \
  "$release/leanos-${version}-x86_64-preemption.map"
cp build/boot/preemption.serial.log \
  "$release/leanos-${version}-preemption-serial.log"
cp "build/boot/leanos-${version}-x86_64-fault-containment.iso" \
  "$release/leanos-${version}-x86_64-fault-containment.iso"
cp build/boot/leanos-fault-containment.elf \
  "$release/leanos-${version}-x86_64-fault-containment.elf"
cp build/boot/leanos-fault-containment.map \
  "$release/leanos-${version}-x86_64-fault-containment.map"
cp build/boot/fault-containment.serial.log \
  "$release/leanos-${version}-fault-containment-serial.log"
cp build/boot/fault-containment.disassembly.txt \
  "$release/leanos-${version}-fault-containment-disassembly.txt"
cp build/boot/fault-containment-policy-report.txt \
  "$release/leanos-${version}-fault-containment-policy-report.txt"
cp build/boot/fault-containment-snapshot.txt \
  "$release/leanos-${version}-fault-containment-snapshot.txt"
cp build/boot/boot-page-plan-fault-containment.final.h \
  "$release/leanos-${version}-fault-containment-page-plan.h"
cp "build/boot/leanos-${version}-x86_64-fault-readonly-write.iso" \
  "$release/leanos-${version}-x86_64-fault-readonly-write.iso"
cp build/boot/leanos-fault-readonly-write.elf \
  "$release/leanos-${version}-x86_64-fault-readonly-write.elf"
cp build/boot/leanos-fault-readonly-write.map \
  "$release/leanos-${version}-x86_64-fault-readonly-write.map"
cp build/boot/fault-readonly-write.serial.log \
  "$release/leanos-${version}-fault-readonly-write-serial.log"
cp build/boot/fault-readonly-write.disassembly.txt \
  "$release/leanos-${version}-fault-readonly-write-disassembly.txt"
cp build/boot/fault-readonly-write-policy-report.txt \
  "$release/leanos-${version}-fault-readonly-write-policy-report.txt"
cp build/boot/fault-readonly-write-snapshot.txt \
  "$release/leanos-${version}-fault-readonly-write-snapshot.txt"
cp build/boot/boot-page-plan-fault-readonly-write.final.h \
  "$release/leanos-${version}-fault-readonly-write-page-plan.h"
cp "build/boot/leanos-${version}-x86_64-fault-nx-execute.iso" \
  "$release/leanos-${version}-x86_64-fault-nx-execute.iso"
cp build/boot/leanos-fault-nx-execute.elf \
  "$release/leanos-${version}-x86_64-fault-nx-execute.elf"
cp build/boot/leanos-fault-nx-execute.map \
  "$release/leanos-${version}-x86_64-fault-nx-execute.map"
cp build/boot/fault-nx-execute.serial.log \
  "$release/leanos-${version}-fault-nx-execute-serial.log"
cp build/boot/fault-nx-execute.disassembly.txt \
  "$release/leanos-${version}-fault-nx-execute-disassembly.txt"
cp build/boot/fault-nx-execute-policy-report.txt \
  "$release/leanos-${version}-fault-nx-execute-policy-report.txt"
cp build/boot/fault-nx-execute-snapshot.txt \
  "$release/leanos-${version}-fault-nx-execute-snapshot.txt"
cp build/boot/boot-page-plan-fault-nx-execute.final.h \
  "$release/leanos-${version}-fault-nx-execute-page-plan.h"
cp "build/boot/leanos-${version}-x86_64-fault-reserved-bit.iso" \
  "$release/leanos-${version}-x86_64-fault-reserved-bit.iso"
cp build/boot/leanos-fault-reserved-bit.elf \
  "$release/leanos-${version}-x86_64-fault-reserved-bit.elf"
cp build/boot/leanos-fault-reserved-bit.map \
  "$release/leanos-${version}-x86_64-fault-reserved-bit.map"
cp build/boot/fault-reserved-bit.serial.log \
  "$release/leanos-${version}-fault-reserved-bit-serial.log"
cp build/boot/fault-reserved-bit.disassembly.txt \
  "$release/leanos-${version}-fault-reserved-bit-disassembly.txt"
cp build/boot/fault-reserved-bit-policy-report.txt \
  "$release/leanos-${version}-fault-reserved-bit-policy-report.txt"
cp build/boot/fault-reserved-bit-terminal.txt \
  "$release/leanos-${version}-fault-reserved-bit-terminal.txt"
cp build/boot/boot-page-plan-fault-reserved-bit.final.h \
  "$release/leanos-${version}-fault-reserved-bit-page-plan.h"
cp "build/boot/leanos-${version}-x86_64-fault-walk-mismatch.iso" \
  "$release/leanos-${version}-x86_64-fault-walk-mismatch.iso"
cp build/boot/leanos-fault-walk-mismatch.elf \
  "$release/leanos-${version}-x86_64-fault-walk-mismatch.elf"
cp build/boot/leanos-fault-walk-mismatch.map \
  "$release/leanos-${version}-x86_64-fault-walk-mismatch.map"
cp build/boot/fault-walk-mismatch.serial.log \
  "$release/leanos-${version}-fault-walk-mismatch-serial.log"
cp build/boot/fault-walk-mismatch.disassembly.txt \
  "$release/leanos-${version}-fault-walk-mismatch-disassembly.txt"
cp build/boot/fault-walk-mismatch-policy-report.txt \
  "$release/leanos-${version}-fault-walk-mismatch-policy-report.txt"
cp build/boot/fault-walk-mismatch-terminal.txt \
  "$release/leanos-${version}-fault-walk-mismatch-terminal.txt"
cp build/boot/boot-page-plan-fault-walk-mismatch.final.h \
  "$release/leanos-${version}-fault-walk-mismatch-page-plan.h"
cp build/boot/entry-adversarial.serial.log \
  "$release/leanos-${version}-entry-adversarial-serial.log"
cp build/boot/double-fault.serial.log \
  "$release/leanos-${version}-double-fault-serial.log"
cp build/boot/double-fault-guard-mapped.serial.log \
  "$release/leanos-${version}-double-fault-guard-mapped-serial.log"
cp build/boot/corpus.tsv "$release/leanos-${version}-oracle.tsv"
cp "$evidence" "$release/EMULATOR_EVIDENCE.json"
cp scripts/emulator-evidence-matrix.tsv "$release/EMULATOR_EVIDENCE_MATRIX.tsv"
cp build/boot/SOURCE_REVISION "$release/SOURCE_REVISION"
cp docs/release-notes.md "$release/RELEASE_NOTES.md"
LEANOS_VERSION="$version" ./scripts/record-tool-versions.sh \
  "$release/TOOLCHAIN.txt"
(cd "$release" && sha256sum \
  "leanos-${version}-x86_64.iso" "leanos-${version}-x86_64.elf" \
  "leanos-${version}-x86_64.map" "leanos-${version}-serial.log" \
  "leanos-${version}-x86_64-preemption.iso" \
  "leanos-${version}-x86_64-preemption.elf" \
  "leanos-${version}-x86_64-preemption.map" \
  "leanos-${version}-preemption-serial.log" \
  "leanos-${version}-x86_64-fault-containment.iso" \
  "leanos-${version}-x86_64-fault-containment.elf" \
  "leanos-${version}-x86_64-fault-containment.map" \
  "leanos-${version}-fault-containment-serial.log" \
  "leanos-${version}-fault-containment-disassembly.txt" \
  "leanos-${version}-fault-containment-policy-report.txt" \
  "leanos-${version}-fault-containment-snapshot.txt" \
  "leanos-${version}-fault-containment-page-plan.h" \
  "leanos-${version}-x86_64-fault-readonly-write.iso" \
  "leanos-${version}-x86_64-fault-readonly-write.elf" \
  "leanos-${version}-x86_64-fault-readonly-write.map" \
  "leanos-${version}-fault-readonly-write-serial.log" \
  "leanos-${version}-fault-readonly-write-disassembly.txt" \
  "leanos-${version}-fault-readonly-write-policy-report.txt" \
  "leanos-${version}-fault-readonly-write-snapshot.txt" \
  "leanos-${version}-fault-readonly-write-page-plan.h" \
  "leanos-${version}-x86_64-fault-nx-execute.iso" \
  "leanos-${version}-x86_64-fault-nx-execute.elf" \
  "leanos-${version}-x86_64-fault-nx-execute.map" \
  "leanos-${version}-fault-nx-execute-serial.log" \
  "leanos-${version}-fault-nx-execute-disassembly.txt" \
  "leanos-${version}-fault-nx-execute-policy-report.txt" \
  "leanos-${version}-fault-nx-execute-snapshot.txt" \
  "leanos-${version}-fault-nx-execute-page-plan.h" \
  "leanos-${version}-x86_64-fault-reserved-bit.iso" \
  "leanos-${version}-x86_64-fault-reserved-bit.elf" \
  "leanos-${version}-x86_64-fault-reserved-bit.map" \
  "leanos-${version}-fault-reserved-bit-serial.log" \
  "leanos-${version}-fault-reserved-bit-disassembly.txt" \
  "leanos-${version}-fault-reserved-bit-policy-report.txt" \
  "leanos-${version}-fault-reserved-bit-terminal.txt" \
  "leanos-${version}-fault-reserved-bit-page-plan.h" \
  "leanos-${version}-x86_64-fault-walk-mismatch.iso" \
  "leanos-${version}-x86_64-fault-walk-mismatch.elf" \
  "leanos-${version}-x86_64-fault-walk-mismatch.map" \
  "leanos-${version}-fault-walk-mismatch-serial.log" \
  "leanos-${version}-fault-walk-mismatch-disassembly.txt" \
  "leanos-${version}-fault-walk-mismatch-policy-report.txt" \
  "leanos-${version}-fault-walk-mismatch-terminal.txt" \
  "leanos-${version}-fault-walk-mismatch-page-plan.h" \
  "leanos-${version}-entry-adversarial-serial.log" \
  "leanos-${version}-double-fault-serial.log" \
  "leanos-${version}-double-fault-guard-mapped-serial.log" \
  "leanos-${version}-oracle.tsv" \
  EMULATOR_EVIDENCE.json EMULATOR_EVIDENCE_MATRIX.tsv \
  SOURCE_REVISION TOOLCHAIN.txt RELEASE_NOTES.md > SHA256SUMS)

echo "packaged $tag release assets in build/release"
