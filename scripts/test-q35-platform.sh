#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source scripts/q35-platform.sh

command=()
leanos_q35_command command qemu-system-x86_64 128 build/evidence/serial.log \
  build/boot/leanos.iso
leanos_validate_q35_command command

kvm=()
LEANOS_QEMU_ACCELERATOR=kvm \
  leanos_q35_command kvm qemu-system-x86_64 128 \
    build/evidence/kvm.serial.log build/boot/leanos.iso
LEANOS_QEMU_ACCELERATOR=kvm leanos_validate_q35_command kvm
[[ " ${kvm[*]} " == *" -machine q35,accel=kvm "* ]] || {
  echo "error: q35 platform omitted the explicit KVM accelerator" >&2
  exit 1
}
[[ " ${kvm[*]} " == *" -cpu max,vendor=AuthenticAMD "* ]] || {
  echo "error: KVM q35 platform did not preserve the reviewed guest CPU contract" >&2
  exit 1
}
if LEANOS_QEMU_ACCELERATOR=tcg \
    leanos_validate_q35_command kvm 2>/dev/null; then
  echo "error: q35 platform accepted KVM under the TCG contract" >&2
  exit 1
fi
if LEANOS_QEMU_ACCELERATOR=kvm,tcg \
    leanos_q35_command negative qemu-system-x86_64 128 \
      build/evidence/fallback.serial.log build/boot/leanos.iso 2>/dev/null; then
  echo "error: q35 platform accepted an accelerator fallback list" >&2
  exit 1
fi

multivcpu=()
leanos_q35_command multivcpu qemu-system-x86_64 128 \
  build/evidence/multivcpu.serial.log build/boot/leanos.iso max \
  2,sockets=1,cores=2,threads=1
leanos_validate_q35_command multivcpu
[[ " ${multivcpu[*]} " == *" -smp 2,sockets=1,cores=2,threads=1 "* ]] || {
  echo "error: q35 platform omitted the explicit multi-vCPU topology" >&2
  exit 1
}

negative=("${multivcpu[@]}")
for index in "${!negative[@]}"; do
  if [[ "${negative[$index]}" == 2,sockets=1,cores=2,threads=1 ]]; then
    negative[$index]=2
    break
  fi
done
if leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted an implicit multi-vCPU topology" >&2
  exit 1
fi

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

grep -Eq 'source .*q35-platform\.sh' scripts/run-assigned-edu.sh &&
  grep -Eq 'leanos_q35_assigned_edu_command command ' \
    scripts/run-assigned-edu.sh &&
  grep -Fq 'VTD-FAULT requester=16 domain=0 generation=1 direction=read' \
    scripts/run-assigned-edu.sh || {
  echo "error: assigned-EDU positive bypasses its versioned platform builder" >&2
  exit 1
}

grep -Eq 'source .*q35-platform\.sh' scripts/run-assigned-edu-negatives.sh &&
  grep -Eq 'leanos_q35_assigned_edu_command command ' \
    scripts/run-assigned-edu-negatives.sh || {
  echo "error: assigned-EDU negatives bypass their versioned platform builder" >&2
  exit 1
}

grep -Fq './scripts/run-assigned-edu-negatives.sh' .github/workflows/ci.yml &&
  grep -Fq './scripts/run-emulator-evidence.py bundle' .github/workflows/ci.yml &&
  grep -Fq 'path: build/ci/emulator-evidence-shard-${{ matrix.shard }}.tar' \
    .github/workflows/ci.yml || {
  echo "error: mandatory CI does not run and retain complete assigned-EDU evidence" >&2
  exit 1
}
if ! python3 - <<'PY'
import runpy

evidence = runpy.run_path("scripts/run-emulator-evidence.py")
required = (
    "build/boot/assigned-edu-control.serial.log",
    "build/boot/leanos-0.1.0-x86_64-assigned-edu.iso",
    "build/boot/leanos-assigned-edu.elf",
    "build/boot/leanos-assigned-edu.map",
    "build/boot/boot-page-plan-assigned-edu.h",
    "build/boot/boot-page-plan-assigned-edu.final.h",
)
if "build/boot" not in evidence["BUNDLE_ROOTS"]:
    raise SystemExit("emulator bundle omits the boot evidence root")
for artifact in required:
    if not evidence["bundle_candidate"](artifact):
        raise SystemExit(f"emulator bundle excludes assigned-EDU artifact: {artifact}")
PY
then
  echo "error: mandatory CI bundle does not retain complete assigned-EDU evidence" >&2
  exit 1
fi

echo "Explicit q35 platform positive and controlled-negative checks passed"
