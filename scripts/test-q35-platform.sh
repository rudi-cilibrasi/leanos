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

# The disk medium attaches the same image as an IDE hard disk, never written.
disk=()
LEANOS_QEMU_MEDIUM=disk leanos_q35_command disk qemu-system-x86_64 128 \
  build/evidence/disk.serial.log build/boot/leanos.iso
LEANOS_QEMU_MEDIUM=disk leanos_validate_q35_command disk
[[ " ${disk[*]} " == *" -device ide-hd,drive=leanos-disk,bus=ide.0 "* &&
   " ${disk[*]} " == *" id=leanos-disk,if=none,format=raw,snapshot=on,file=build/boot/leanos.iso "* &&
   " ${disk[*]} " != *" ide-cd,"* ]] || {
  echo "error: q35 disk medium did not attach exactly the image as a snapshot disk" >&2
  exit 1
}
if leanos_validate_q35_command disk 2>/dev/null; then
  echo "error: q35 platform accepted a disk command under the CD-ROM contract" >&2
  exit 1
fi
if LEANOS_QEMU_MEDIUM=disk leanos_validate_q35_command command 2>/dev/null; then
  echo "error: q35 platform accepted a CD-ROM command under the disk contract" >&2
  exit 1
fi
negative=("${disk[@]}")
for index in "${!negative[@]}"; do
  if [[ "${negative[$index]}" == id=leanos-disk,* ]]; then
    negative[$index]=id=leanos-disk,if=none,format=raw,file=build/boot/leanos.iso
    break
  fi
done
if LEANOS_QEMU_MEDIUM=disk leanos_validate_q35_command negative 2>/dev/null; then
  echo "error: q35 platform accepted a writable disk image" >&2
  exit 1
fi
if LEANOS_QEMU_MEDIUM=usb leanos_q35_command negative qemu-system-x86_64 128 \
    build/evidence/usb.serial.log build/boot/leanos.iso 2>/dev/null; then
  echo "error: q35 platform accepted an unknown boot medium" >&2
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

device_service=()
leanos_q35_device_service_command device_service /tmp/leanos-qmp.sock \
  qemu-system-x86_64 128 build/evidence/device-service.serial.log \
  build/boot/leanos.iso
leanos_validate_q35_device_service_command device_service
[[ "$LEANOS_Q35_DEVICE_SERVICE_TOPOLOGY_VERSION" != "$LEANOS_Q35_TOPOLOGY_VERSION" &&
   "$LEANOS_Q35_DEVICE_SERVICE_TOPOLOGY_VERSION" != "$LEANOS_Q35_ASSIGNED_EDU_TOPOLOGY_VERSION" ]] || {
  echo "error: device-service construction reused another topology version" >&2
  exit 1
}
if leanos_validate_q35_command device_service 2>/dev/null; then
  echo "error: production q35 platform accepted the device-service xHCI" >&2
  exit 1
fi
negative=("${device_service[@]}")
negative[-7]=qemu-xhci,id=xhci,bus=pcie.0,addr=0x3
if leanos_validate_q35_device_service_command negative 2>/dev/null; then
  echo "error: device-service platform accepted a drifted xHCI BDF" >&2
  exit 1
fi
negative=("${device_service[@]:0:${#device_service[@]}-2}")
if leanos_validate_q35_device_service_command negative 2>/dev/null; then
  echo "error: device-service platform accepted a missing QMP socket" >&2
  exit 1
fi
negative=("${device_service[@]:0:${#device_service[@]}-2}" -device edu,bus=pcie.0,addr=0x3 "${device_service[@]: -2}")
if leanos_validate_q35_device_service_command negative 2>/dev/null; then
  echo "error: device-service platform accepted an extra function" >&2
  exit 1
fi

ahci_service=()
leanos_q35_ahci_service_command ahci_service build/boot/ahci-service-disk.img \
  qemu-system-x86_64 128 build/evidence/ahci-service.serial.log \
  build/boot/leanos.iso
leanos_validate_q35_ahci_service_command ahci_service
[[ "$LEANOS_Q35_AHCI_SERVICE_TOPOLOGY_VERSION" != "$LEANOS_Q35_TOPOLOGY_VERSION" &&
   "$LEANOS_Q35_AHCI_SERVICE_TOPOLOGY_VERSION" != "$LEANOS_Q35_ASSIGNED_EDU_TOPOLOGY_VERSION" &&
   "$LEANOS_Q35_AHCI_SERVICE_TOPOLOGY_VERSION" != "$LEANOS_Q35_DEVICE_SERVICE_TOPOLOGY_VERSION" ]] || {
  echo "error: ahci-service construction reused another topology version" >&2
  exit 1
}
if leanos_validate_q35_command ahci_service 2>/dev/null; then
  echo "error: production q35 platform accepted the ahci-service disk" >&2
  exit 1
fi
negative=("${ahci_service[@]}")
negative[-3]="id=leanos-disk,if=none,format=raw,file=build/boot/ahci-service-disk.img"
if leanos_validate_q35_ahci_service_command negative 2>/dev/null; then
  echo "error: ahci-service platform accepted a writable disk" >&2
  exit 1
fi
negative=("${ahci_service[@]}")
negative[-1]=ide-hd,drive=leanos-disk,bus=ide.0
if leanos_validate_q35_ahci_service_command negative 2>/dev/null; then
  echo "error: ahci-service platform accepted the disk on the CD's port" >&2
  exit 1
fi
negative=("${ahci_service[@]:0:${#ahci_service[@]}-4}" -device edu,bus=pcie.0,addr=0x3 "${ahci_service[@]: -4}")
if leanos_validate_q35_ahci_service_command negative 2>/dev/null; then
  echo "error: ahci-service platform accepted an extra function" >&2
  exit 1
fi

# The netboot construction (issue #601): no boot medium, the pinned TFTP
# network and the boot NIC at 00:03.0, with the firmware's own loader.
netboot_tree="$(mktemp -d)"
trap 'rm -rf "$netboot_tree"' EXIT
mkdir -p "$netboot_tree/boot/grub/i386-pc" "$netboot_tree/boot/grub/x86_64-efi"
: >"$netboot_tree/boot/grub/i386-pc/core.0"
: >"$netboot_tree/boot/grub/x86_64-efi/core.efi"
netboot=()
leanos_q35_netboot_command netboot "$netboot_tree" qemu-system-x86_64 128 \
  build/evidence/netboot.serial.log
leanos_validate_q35_netboot_command netboot
[[ " ${netboot[*]} " == *" -netdev user,id=leanos-net,restrict=on,tftp=$netboot_tree,bootfile=boot/grub/i386-pc/core.0 "* &&
   " ${netboot[*]} " == *" -device $LEANOS_Q35_NETBOOT_NIC "* &&
   " ${netboot[*]} " == *" -nic none "* &&
   " ${netboot[*]} " != *" ide-cd,"* && " ${netboot[*]} " != *" ide-hd,"* ]] || {
  echo "error: q35 netboot construction did not attach exactly the TFTP network and boot NIC" >&2
  exit 1
}
[[ "$LEANOS_Q35_NETBOOT_TOPOLOGY_VERSION" != "$LEANOS_Q35_TOPOLOGY_VERSION" &&
   "$LEANOS_Q35_NETBOOT_TOPOLOGY_VERSION" != "$LEANOS_Q35_ASSIGNED_EDU_TOPOLOGY_VERSION" &&
   "$LEANOS_Q35_NETBOOT_TOPOLOGY_VERSION" != "$LEANOS_Q35_DEVICE_SERVICE_TOPOLOGY_VERSION" &&
   "$LEANOS_Q35_NETBOOT_TOPOLOGY_VERSION" != "$LEANOS_Q35_AHCI_SERVICE_TOPOLOGY_VERSION" ]] || {
  echo "error: netboot construction reused another topology version" >&2
  exit 1
}
netboot_ovmf=()
LEANOS_QEMU_FIRMWARE=ovmf leanos_q35_netboot_command netboot_ovmf "$netboot_tree" \
  qemu-system-x86_64 128 "$netboot_tree/ovmf.serial.log"
LEANOS_QEMU_FIRMWARE=ovmf leanos_validate_q35_netboot_command netboot_ovmf
[[ " ${netboot_ovmf[*]} " == *",bootfile=boot/grub/x86_64-efi/core.efi "* ]] || {
  echo "error: q35 OVMF netboot construction did not name the UEFI loader" >&2
  exit 1
}
if LEANOS_QEMU_FIRMWARE=ovmf leanos_validate_q35_netboot_command netboot 2>/dev/null; then
  echo "error: netboot platform accepted the BIOS loader under OVMF" >&2
  exit 1
fi
if leanos_validate_q35_command netboot 2>/dev/null ||
   LEANOS_QEMU_MEDIUM=disk leanos_validate_q35_command netboot 2>/dev/null; then
  echo "error: production q35 platform accepted the netboot construction" >&2
  exit 1
fi
if leanos_validate_q35_netboot_command command 2>/dev/null; then
  echo "error: netboot platform accepted the CD-ROM construction" >&2
  exit 1
fi
if LEANOS_QEMU_MEDIUM=disk leanos_q35_netboot_command negative "$netboot_tree" \
    qemu-system-x86_64 128 build/evidence/netboot.serial.log 2>/dev/null ||
   LEANOS_QEMU_MEDIUM=disk leanos_validate_q35_netboot_command netboot 2>/dev/null; then
  echo "error: netboot platform accepted an explicit boot medium" >&2
  exit 1
fi
if LEANOS_QEMU_MEDIUM=network leanos_q35_command negative qemu-system-x86_64 128 \
    build/evidence/network.serial.log build/boot/leanos.iso 2>/dev/null; then
  echo "error: q35 platform accepted the network medium outside the netboot construction" >&2
  exit 1
fi
negative=("${netboot[@]}")
negative[-1]="${LEANOS_Q35_NETBOOT_NIC/addr=0x3/addr=0x4}"
if leanos_validate_q35_netboot_command negative 2>/dev/null; then
  echo "error: netboot platform accepted a drifted boot NIC BDF" >&2
  exit 1
fi
negative=("${netboot[@]}")
negative[-3]="user,id=leanos-net,tftp=$netboot_tree,bootfile=boot/grub/i386-pc/core.0"
if leanos_validate_q35_netboot_command negative 2>/dev/null; then
  echo "error: netboot platform accepted an unrestricted user network" >&2
  exit 1
fi
negative=("${netboot[@]:0:${#netboot[@]}-4}")
if leanos_validate_q35_netboot_command negative 2>/dev/null; then
  echo "error: netboot platform accepted a missing boot NIC" >&2
  exit 1
fi
negative=("${netboot[@]:0:${#netboot[@]}-4}" -device edu,bus=pcie.0,addr=0x2 "${netboot[@]: -4}")
if leanos_validate_q35_netboot_command negative 2>/dev/null; then
  echo "error: netboot platform accepted an extra function" >&2
  exit 1
fi
negative=("${netboot[@]:0:${#netboot[@]}-4}" -netdev user,id=other "${netboot[@]: -4}")
if leanos_validate_q35_netboot_command negative 2>/dev/null; then
  echo "error: netboot platform accepted a second network" >&2
  exit 1
fi
negative=("${netboot[@]:0:${#netboot[@]}-4}"
  -drive "id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=build/boot/leanos.iso"
  -device ide-cd,drive=leanos-cd,bus=ide.0 "${netboot[@]: -4}")
if leanos_validate_q35_netboot_command negative 2>/dev/null; then
  echo "error: netboot platform accepted a boot CD beside the network" >&2
  exit 1
fi
rm -f "$netboot_tree/boot/grub/i386-pc/core.0"
if leanos_q35_netboot_command negative "$netboot_tree" qemu-system-x86_64 128 \
    build/evidence/netboot.serial.log 2>/dev/null; then
  echo "error: netboot platform accepted a tree without the firmware's loader" >&2
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
  grep -Fq '${LEANOS_SERIAL_21_VTD_FAULT} requester=16 domain=0 generation=1 direction=read' \
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

grep -Eq 'source .*q35-platform\.sh' scripts/run-device-service-rejection.sh &&
  grep -Eq 'leanos_q35_device_service_command command ' \
    scripts/run-device-service-rejection.sh || {
  echo "error: device-service negatives bypass their versioned platform builder" >&2
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
