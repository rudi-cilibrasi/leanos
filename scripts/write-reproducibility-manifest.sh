#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
version="${LEANOS_VERSION:-0.1.0}"
artifacts=(
  "leanos-${version}-x86_64.iso" leanos.elf leanos.map SOURCE_REVISION
  TOOLCHAIN_PROFILE.json
  "leanos-${version}-x86_64-fault-containment.iso"
  leanos-fault-containment.elf leanos-fault-containment.map
  boot-page-plan-fault-containment.final.h
  fault-containment.disassembly.txt fault-containment-policy-report.txt
  "leanos-${version}-x86_64-fault-readonly-write.iso"
  leanos-fault-readonly-write.elf leanos-fault-readonly-write.map
  boot-page-plan-fault-readonly-write.final.h
  fault-readonly-write.disassembly.txt fault-readonly-write-policy-report.txt
  "leanos-${version}-x86_64-fault-nx-execute.iso"
  leanos-fault-nx-execute.elf leanos-fault-nx-execute.map
  boot-page-plan-fault-nx-execute.final.h
  fault-nx-execute.disassembly.txt fault-nx-execute-policy-report.txt
  "leanos-${version}-x86_64-fault-reserved-bit.iso"
  leanos-fault-reserved-bit.elf leanos-fault-reserved-bit.map
  boot-page-plan-fault-reserved-bit.final.h
  fault-reserved-bit.disassembly.txt fault-reserved-bit-policy-report.txt
  "leanos-${version}-x86_64-fault-walk-mismatch.iso"
  leanos-fault-walk-mismatch.elf leanos-fault-walk-mismatch.map
  boot-page-plan-fault-walk-mismatch.final.h
  fault-walk-mismatch.disassembly.txt fault-walk-mismatch-policy-report.txt
  "leanos-${version}-x86_64-fault-stale-translation.iso"
  leanos-fault-stale-translation.elf leanos-fault-stale-translation.map
  boot-page-plan-fault-stale-translation.final.h
  fault-stale-translation.disassembly.txt
  fault-stale-translation-policy-report.txt
)

if [[ "${1:-}" == "--list" ]]; then
  printf '%s\n' "${artifacts[@]}"
  exit 0
fi

output="${1:-$repo_root/build/boot/REPRODUCIBILITY-SHA256SUMS}"
boot_dir="${2:-$repo_root/build/boot}"
mkdir -p "$(dirname "$output")"
for artifact in "${artifacts[@]}"; do
  [[ -f "$boot_dir/$artifact" ]] || {
    echo "error: reproducibility artifact is missing: $artifact" >&2
    exit 1
  }
done
(
  cd "$boot_dir"
  sha256sum "${artifacts[@]}"
) >"$output"
