#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source scripts/q35-platform.sh

command=()
leanos_q35_command command qemu-system-x86_64 128 build/evidence/serial.log \
  build/boot/leanos.iso
leanos_validate_q35_command command

assigned_edu=()
leanos_q35_assigned_edu_command assigned_edu qemu-system-x86_64 128 \
  build/evidence/assigned-edu.serial.log build/boot/leanos.iso
leanos_validate_q35_assigned_edu_command assigned_edu
[[ "$LEANOS_Q35_ASSIGNED_EDU_TOPOLOGY_VERSION" != "$LEANOS_Q35_TOPOLOGY_VERSION" ]] || {
  echo "error: assigned-EDU construction reused the production topology version" >&2
  exit 1
}
if leanos_validate_q35_command assigned_edu 2>/dev/null; then
  echo "error: production q35 platform accepted the assigned EDU function" >&2
  exit 1
fi

negative=("${assigned_edu[@]}")
negative[-1]=edu,bus=pcie.0,addr=0x3
if leanos_validate_q35_assigned_edu_command negative 2>/dev/null; then
  echo "error: assigned-EDU platform accepted a drifted BDF" >&2
  exit 1
fi

negative=("${assigned_edu[@]}" -device edu,bus=pcie.0,addr=0x2)
if leanos_validate_q35_assigned_edu_command negative 2>/dev/null; then
  echo "error: assigned-EDU platform accepted a duplicate function" >&2
  exit 1
fi

negative=("${command[@]}")
for index in "${!negative[@]}"; do
  if [[ "${negative[$index]}" == -nodefaults ]]; then
    unset 'negative[index]'
    negative=("${negative[@]}")
    break
  fi
done
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted omitted -nodefaults" >&2
  exit 1
fi

negative=("${command[@]}")
for index in "${!negative[@]}"; do
  if [[ "${negative[$index]}" == max ]]; then
    negative[$index]=host
    break
  fi
done
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted unreviewed CPU options" >&2
  exit 1
fi

negative=("${command[@]}" -device edu)
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted an unexpected PCI function" >&2
  exit 1
fi

iommu_pinned=intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off

negative=("${command[@]}")
for index in "${!negative[@]}"; do
  if [[ "${negative[$index]}" == "$iommu_pinned" ]]; then
    negative[$index]="${iommu_pinned/pt=off/pt=on}"
    break
  fi
done
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted drifted intel-iommu options" >&2
  exit 1
fi

negative=()
for argument in "${command[@]}"; do
  [[ "$argument" == "$iommu_pinned" ]] && { unset 'negative[-1]'; continue; }
  negative+=("$argument")
done
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted an omitted intel-iommu unit" >&2
  exit 1
fi

negative=()
for argument in "${command[@]}"; do
  [[ "$argument" == "$iommu_pinned" ]] && { unset 'negative[-1]'; continue; }
  negative+=("$argument")
done
negative+=(-device "$iommu_pinned")
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted the intel-iommu unit after a translated device" >&2
  exit 1
fi

negative=("${command[@]}")
for index in "${!negative[@]}"; do
  if [[ "${negative[$index]}" == VGA,bus=pcie.0,addr=0x1 ]]; then
    negative[$index]=VGA
    break
  fi
done
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted an unpinned VGA BDF" >&2
  exit 1
fi

mapfile -t raw_q35 < <(
  grep -El -- '-machine[[:space:]]+q35' scripts/run-*.sh || true
)
[[ ${#raw_q35[@]} -eq 0 ]] || {
  printf 'error: mandatory runners bypass the q35 platform builder: %s\n' \
    "${raw_q35[*]}" >&2
  exit 1
}

for runner in \
  scripts/run-bootstrap32-ud.sh \
  scripts/run-bootstrap64-nmi.sh \
  scripts/run-double-fault.sh \
  scripts/run-entry-stack-overflow.sh \
  scripts/run-extended-state-peer-pke.sh \
  scripts/run-fault-integrity.sh \
  scripts/run-image.sh \
  scripts/run-malformed-handoff.sh \
  scripts/run-nmi.sh \
  scripts/run-return-corruptions.sh
do
  grep -Eq 'source .*q35-platform\.sh' "$runner" &&
    grep -Eq 'leanos_q35_command command ' "$runner" || {
      echo "error: runner does not consume the q35 platform builder: $runner" >&2
      exit 1
    }
done

grep -Eq 'source .*q35-platform\.sh' scripts/run-dma-unknown-device.sh &&
  grep -Eq 'leanos_q35_assigned_edu_command command ' \
    scripts/run-dma-unknown-device.sh || {
  echo "error: assigned-EDU boot negative bypasses its versioned platform builder" >&2
  exit 1
}

echo "Explicit q35 platform positive and controlled-negative checks passed"
