#!/usr/bin/env bash
# Authoritative QEMU 8.2.2 q35 construction used by every emulator runner.
#
# The machine-integrated host/ISA/AHCI/SMBus functions are fixed by q35.  All
# optional defaults are suppressed; the DMA-remapping unit, VGA function, boot
# CD attachment, and ISA debug-exit device are then added explicitly.  The
# intel-iommu unit must be the first device so QEMU constructs it before any
# translated PCI function; every remapping-relevant option is pinned so drift
# is a construction error rather than a silent capability change.  This is
# reproducible QEMU construction evidence, not a proof of firmware, PCI, DMA,
# or VT-d semantics.

readonly LEANOS_Q35_TOPOLOGY_VERSION=0001000800020002
# The assigned-device scenario is a separate construction contract. Keeping a
# distinct version prevents its deliberately admitted DMA-capable function from
# being confused with the production deny-all inventory.
readonly LEANOS_Q35_ASSIGNED_EDU_TOPOLOGY_VERSION=0001000800020003

leanos_qemu_accelerator() {
  local accelerator="${LEANOS_QEMU_ACCELERATOR:-tcg}"
  case "$accelerator" in
    tcg|kvm) printf '%s\n' "$accelerator" ;;
    *)
      echo "error: QEMU accelerator must be exactly 'tcg' or 'kvm'; fallback lists are forbidden" >&2
      return 1
      ;;
  esac
}

# Firmware family: SeaBIOS (QEMU's built-in default, BIOS/El Torito boot) or
# OVMF (EDK II UEFI, El Torito EFI boot).  Both reach the same GRUB
# configuration and the same Multiboot2 kernel entry.  OVMF is loaded as the
# pinned read-only code flash plus a private copy of the variable store.
# Boot medium: the ISO as an IDE CD-ROM (El Torito, the default), or the same
# image as an IDE hard disk, as it boots once written to a USB stick or an
# internal disk (its MBR for BIOS, its GPT EFI system partition for UEFI).
# The disk is opened with snapshot=on, so the image is never written.
# The netboot construction below has no boot medium attached: it boots from
# the network, and only its own builder and validator select that medium.
leanos_qemu_medium() {
  local medium="${LEANOS_QEMU_MEDIUM:-cdrom}"
  case "$medium" in
    cdrom|disk) ;;
    *)
      echo "error: QEMU boot medium must be exactly 'cdrom' or 'disk'" >&2
      return 1
      ;;
  esac
  [[ "${leanos_q35_network_medium:-0}" != 1 ]] || medium=network
  printf '%s\n' "$medium"
}

readonly LEANOS_OVMF_CODE=/usr/share/OVMF/OVMF_CODE_4M.fd
readonly LEANOS_OVMF_VARS=/usr/share/OVMF/OVMF_VARS_4M.fd

leanos_qemu_firmware() {
  local firmware="${LEANOS_QEMU_FIRMWARE:-seabios}"
  case "$firmware" in
    seabios|ovmf) printf '%s\n' "$firmware" ;;
    *)
      echo "error: QEMU firmware must be exactly 'seabios' or 'ovmf'" >&2
      return 1
      ;;
  esac
}

leanos_q35_cpu() {
  local requested="$1"
  local accelerator

  accelerator="$(leanos_qemu_accelerator)" || return 1
  case "$requested" in
    max|max,phys-bits=48) ;;
    *)
      echo "error: q35 platform CPU options drifted" >&2
      return 1
      ;;
  esac
  if [[ "$accelerator" == kvm ]]; then
    printf '%s,vendor=AuthenticAMD\n' "$requested"
  else
    printf '%s\n' "$requested"
  fi
}

leanos_validate_q35_command() {
  local command_name="$1"
  local -n q35_command="$command_name"
  local machine=0 nodefaults=0 iommu=0 vga=0 cdrom=0 cdrom_drive=0
  local debug_exit=0 devices=0 cpu_options=0 smp_options=0
  local ovmf_code=0 ovmf_vars=0 pflash=0 expected_pflash=0
  local hard_disk=0 hard_disk_drive=0
  local argument previous= first_device= accelerator firmware medium

  accelerator="$(leanos_qemu_accelerator)" || return 1
  firmware="$(leanos_qemu_firmware)" || return 1
  medium="$(leanos_qemu_medium)" || return 1
  [[ "$firmware" == ovmf ]] && expected_pflash=2

  for argument in "${q35_command[@]}"; do
    if [[ "$previous" == -cpu ]]; then
      if [[ "$argument" == "$(leanos_q35_cpu max)" ||
            "$argument" == "$(leanos_q35_cpu max,phys-bits=48)" ]]; then
        ((cpu_options += 1))
      else
        echo "error: q35 platform CPU options drifted" >&2
        return 1
      fi
    fi
    if [[ "$previous" == -smp ]]; then
      case "$argument" in
        1|2,sockets=1,cores=2,threads=1) ((smp_options += 1)) ;;
        *)
          echo "error: q35 platform SMP topology drifted" >&2
          return 1
          ;;
      esac
    fi
    if [[ "$previous" == -device && -z "$first_device" ]]; then
      first_device="$argument"
    fi
    if [[ "$argument" == "q35,accel=$accelerator" ]]; then
      ((machine += 1))
    elif [[ "$argument" == q35,accel=* ]]; then
      echo "error: q35 platform accelerator differs from the selected $accelerator mode" >&2
      return 1
    fi
    case "$argument" in
      -nodefaults) ((nodefaults += 1)) ;;
      intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off)
        ((iommu += 1))
        ;;
      VGA,bus=pcie.0,addr=0x1) ((vga += 1)) ;;
      ide-cd,drive=leanos-cd,bus=ide.0) ((cdrom += 1)) ;;
      id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=*)
        ((cdrom_drive += 1))
        ;;
      ide-hd,drive=leanos-disk,bus=ide.0) ((hard_disk += 1)) ;;
      id=leanos-disk,if=none,format=raw,snapshot=on,file=*) ((hard_disk_drive += 1)) ;;
      isa-debug-exit,iobase=0xf4,iosize=0x04) ((debug_exit += 1)) ;;
      if=pflash,format=raw,readonly=on,file="$LEANOS_OVMF_CODE")
        ((ovmf_code += 1))
        ;;
      if=pflash,format=raw,file=*) ((ovmf_vars += 1)) ;;
      *if=pflash*|-bios|-pflash) ((pflash += 1)) ;;
      -device) ((devices += 1)) ;;
      -cdrom)
        echo "error: q35 platform must use the explicit ide-cd attachment" >&2
        return 1
        ;;
    esac
    previous="$argument"
  done
  [[ $machine -eq 1 && $nodefaults -eq 1 ]] || {
    echo "error: q35 platform requires the exact q35/$accelerator machine and -nodefaults" >&2
    return 1
  }
  # The caller's array is reached by name: keep these locals' names distinct.
  local expected_cd=1 expected_hard_disk=0 expected_devices=4
  [[ "$medium" == disk ]] && { expected_cd=0; expected_hard_disk=1; }
  [[ "$medium" == network ]] && { expected_cd=0; expected_devices=3; }
  [[ $devices -eq $expected_devices && $iommu -eq 1 && $vga -eq 1 && $cdrom -eq $expected_cd &&
     $cdrom_drive -eq $expected_cd && $hard_disk -eq $expected_hard_disk &&
     $hard_disk_drive -eq $expected_hard_disk && $debug_exit -eq 1 && $cpu_options -eq 1 &&
     $smp_options -eq 1 ]] || {
    echo "error: q35 platform device topology drifted" >&2
    return 1
  }
  [[ $pflash -eq 0 && $ovmf_code -eq $((expected_pflash / 2)) &&
     $ovmf_vars -eq $((expected_pflash / 2)) ]] || {
    echo "error: q35 platform firmware drifted from $firmware" >&2
    return 1
  }
  [[ "$first_device" == intel-iommu,* ]] || {
    echo "error: q35 platform requires the pinned intel-iommu unit before every translated device" >&2
    return 1
  }
}

leanos_q35_command() {
  local command_name="$1"
  local qemu="$2"
  local memory_mib="$3"
  local serial_log="$4"
  local image="$5"
  local cpu="${6:-max}"
  local smp="${7:-1}"
  local -n q35_command="$command_name"
  local accelerator

  accelerator="$(leanos_qemu_accelerator)" || return 1
  cpu="$(leanos_q35_cpu "$cpu")" || return 1

  q35_command=(
    "$qemu"
    -machine "q35,accel=$accelerator"
    -nodefaults
    -cpu "$cpu"
    -smp "$smp"
    -m "${memory_mib}M"
    -display none
    -monitor none
    -serial "file:$serial_log"
    -no-reboot
    -no-shutdown
    -nic none
    -device intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off
    -device VGA,bus=pcie.0,addr=0x1
    -device isa-debug-exit,iobase=0xf4,iosize=0x04
  )
  case "$(leanos_qemu_medium)" in
    disk)
      q35_command+=(
        -drive "id=leanos-disk,if=none,format=raw,snapshot=on,file=$image"
        -device ide-hd,drive=leanos-disk,bus=ide.0
      )
      ;;
    cdrom)
      q35_command+=(
        -drive "id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=$image"
        -device ide-cd,drive=leanos-cd,bus=ide.0
      )
      ;;
    network) ;;
    *) return 1 ;;
  esac
  if [[ "$(leanos_qemu_firmware)" == ovmf ]]; then
    # UEFI writes boot variables, so each run gets a fresh private store
    # next to its serial log; the pinned code flash stays read-only.
    local vars="${serial_log}.ovmf-vars.fd"
    cp "$LEANOS_OVMF_VARS" "$vars" || return 1
    q35_command+=(
      -drive "if=pflash,format=raw,readonly=on,file=$LEANOS_OVMF_CODE"
      -drive "if=pflash,format=raw,file=$vars"
    )
  fi
  leanos_validate_q35_command "$command_name"
}

leanos_validate_q35_assigned_edu_command() {
  local command_name="$1"
  local -n assigned_command="$command_name"
  local count="${#assigned_command[@]}"
  local -a production_command=()

  [[ $count -ge 2 &&
     "${assigned_command[$((count - 2))]}" == -device &&
     "${assigned_command[$((count - 1))]}" == edu,bus=pcie.0,addr=0x2 ]] || {
    echo "error: assigned-EDU platform requires the pinned function as the final device" >&2
    return 1
  }

  production_command=("${assigned_command[@]:0:$((count - 2))}")
  leanos_validate_q35_command production_command
}

leanos_q35_assigned_edu_command() {
  local command_name="$1"

  leanos_q35_command "$@"
  local -n assigned_command="$command_name"
  assigned_command+=(-device edu,bus=pcie.0,addr=0x2)
  leanos_validate_q35_assigned_edu_command "$command_name"
}

# The device-service scenario (issue #449) is its own construction contract:
# qemu-xhci at 00:02.0 with a hub on root port 1 and a USB keyboard behind it,
# appended after the unchanged production devices and bound to the QMP socket
# the runner types through.
readonly LEANOS_Q35_DEVICE_SERVICE_TOPOLOGY_VERSION=0001000800020004
readonly -a LEANOS_Q35_DEVICE_SERVICE_DEVICES=(
  -device qemu-xhci,id=xhci,bus=pcie.0,addr=0x2
  -device usb-hub,id=hub,bus=xhci.0,port=1
  -device usb-kbd,id=kbd0,bus=xhci.0,port=1.1
)

leanos_validate_q35_device_service_command() {
  local command_name="$1"
  local -n service_command="$command_name"
  local count="${#service_command[@]}"
  local tail=$((${#LEANOS_Q35_DEVICE_SERVICE_DEVICES[@]} + 2))
  local -a production_command=()
  local i

  [[ $count -ge $tail && "${service_command[$((count - 2))]}" == -qmp &&
     "${service_command[$((count - 1))]}" == unix:*,server=on,wait=off ]] || {
    echo "error: device-service platform requires the runner's QMP socket last" >&2
    return 1
  }
  for ((i = 0; i < ${#LEANOS_Q35_DEVICE_SERVICE_DEVICES[@]}; ++i)); do
    [[ "${service_command[$((count - tail + i))]}" == \
       "${LEANOS_Q35_DEVICE_SERVICE_DEVICES[$i]}" ]] || {
      echo "error: device-service platform requires the pinned xHCI, hub and keyboard" >&2
      return 1
    }
  done
  production_command=("${service_command[@]:0:$((count - tail))}")
  leanos_validate_q35_command production_command
}

leanos_q35_device_service_command() {
  local command_name="$1"
  local qmp_socket="$2"
  shift 2

  leanos_q35_command "$command_name" "$@"
  local -n service_command="$command_name"
  service_command+=("${LEANOS_Q35_DEVICE_SERVICE_DEVICES[@]}"
    -qmp "unix:$qmp_socket,server=on,wait=off")
  leanos_validate_q35_device_service_command "$command_name"
}

# The ahci-service scenario (issue #496) is its own construction contract: the
# unchanged production devices plus one disk behind port 1 (ide.1) of the
# built-in ICH9 AHCI, whose port 0 holds the boot CD. The disk is the
# generated fixed image (scripts/generate-ahci-service-disk.py), opened with
# snapshot=on so the guest can never change it; the program only reads it.
readonly LEANOS_Q35_AHCI_SERVICE_TOPOLOGY_VERSION=0001000800020005

leanos_validate_q35_ahci_service_command() {
  local command_name="$1"
  local -n ahci_command="$command_name"
  local count="${#ahci_command[@]}"
  local -a production_command=()

  [[ $count -ge 4 &&
     "${ahci_command[$((count - 4))]}" == -drive &&
     "${ahci_command[$((count - 3))]}" == id=leanos-disk,if=none,format=raw,snapshot=on,file=* &&
     "${ahci_command[$((count - 2))]}" == -device &&
     "${ahci_command[$((count - 1))]}" == ide-hd,drive=leanos-disk,bus=ide.1 ]] || {
    echo "error: ahci-service platform requires the pinned snapshot disk on AHCI port 1 last" >&2
    return 1
  }
  production_command=("${ahci_command[@]:0:$((count - 4))}")
  leanos_validate_q35_command production_command
}

leanos_q35_ahci_service_command() {
  local command_name="$1"
  local disk="$2"
  shift 2

  leanos_q35_command "$command_name" "$@"
  local -n ahci_command="$command_name"
  ahci_command+=(
    -drive "id=leanos-disk,if=none,format=raw,snapshot=on,file=$disk"
    -device ide-hd,drive=leanos-disk,bus=ide.1
  )
  leanos_validate_q35_ahci_service_command "$command_name"
}

# The netboot scenario (issue #601) is its own construction contract: the
# unchanged production devices with no boot medium, plus QEMU's user network
# serving a TFTP tree made from an ISO (scripts/build-netboot-tree.sh) and,
# as the only boot device, a transitional virtio-net function at 00:03.0, the
# optional network slot of the q35 manifest (DMAQuarantine.q35Manifest).
# SeaBIOS boots it through QEMU's iPXE option ROM and GRUB i386-pc's core.0,
# OVMF through its own PXE client and GRUB x86_64-efi's core.efi; both read
# the ISO's grub.cfg and kernel from the tree. The kernel quarantines the NIC
# to Command=0 with every other function and never uses it. restrict=on keeps
# the guest off the host's networks; the TFTP server still answers.
readonly LEANOS_Q35_NETBOOT_TOPOLOGY_VERSION=0001000800020006
readonly LEANOS_Q35_NETBOOT_NIC=virtio-net-pci,netdev=leanos-net,bus=pcie.0,addr=0x3,disable-legacy=off,bootindex=1

# The network loader each firmware family fetches from the tree.
leanos_q35_netboot_loader() {
  local firmware
  firmware="$(leanos_qemu_firmware)" || return 1
  case "$firmware" in
    seabios) printf '%s\n' boot/grub/i386-pc/core.0 ;;
    ovmf) printf '%s\n' boot/grub/x86_64-efi/core.efi ;;
  esac
}

leanos_validate_q35_netboot_command() {
  local command_name="$1"
  local -n netboot_command="$command_name"
  local count="${#netboot_command[@]}"
  local -a production_command=()
  local leanos_q35_network_medium=1
  local loader argument previous=

  [[ -z "${LEANOS_QEMU_MEDIUM:-}" ]] || {
    echo "error: netboot platform boots from the network, not LEANOS_QEMU_MEDIUM" >&2
    return 1
  }
  loader="$(leanos_q35_netboot_loader)" || return 1
  [[ $count -ge 4 &&
     "${netboot_command[$((count - 4))]}" == -netdev &&
     "${netboot_command[$((count - 3))]}" =~ ^user,id=leanos-net,restrict=on,tftp=[^,]+,bootfile=([^,]+)$ &&
     "${BASH_REMATCH[1]}" == "$loader" &&
     "${netboot_command[$((count - 2))]}" == -device &&
     "${netboot_command[$((count - 1))]}" == "$LEANOS_Q35_NETBOOT_NIC" ]] || {
    echo "error: netboot platform requires the pinned TFTP network, the firmware's loader and the virtio-net at 00:03.0 last" >&2
    return 1
  }
  production_command=("${netboot_command[@]:0:$((count - 4))}")
  # The production part keeps its `-nic none` and adds no network of its own.
  for argument in "${production_command[@]}"; do
    if [[ "$argument" == -netdev || "$argument" == -net ||
          ( "$previous" == -nic && "$argument" != none ) ]]; then
      echo "error: netboot platform requires its one pinned network last" >&2
      return 1
    fi
    previous="$argument"
  done
  leanos_validate_q35_command production_command
}

# usage: leanos_q35_netboot_command <array> <tftp-tree> <qemu> <memory-mib> <serial-log>
leanos_q35_netboot_command() {
  local command_name="$1"
  local tree="$2"
  local leanos_q35_network_medium=1
  local loader
  shift 2

  [[ -z "${LEANOS_QEMU_MEDIUM:-}" ]] || {
    echo "error: netboot platform boots from the network, not LEANOS_QEMU_MEDIUM" >&2
    return 1
  }
  [[ "$tree" != *,* ]] || {
    echo "error: netboot TFTP tree path must not contain a comma" >&2
    return 1
  }
  loader="$(leanos_q35_netboot_loader)" || return 1
  [[ -f "$tree/$loader" ]] || {
    echo "error: netboot TFTP tree '$tree' has no $loader" >&2
    return 1
  }
  leanos_q35_command "$command_name" "$1" "$2" "$3" - || return 1
  local -n netboot_command="$command_name"
  netboot_command+=(
    -netdev "user,id=leanos-net,restrict=on,tftp=$tree,bootfile=$loader"
    -device "$LEANOS_Q35_NETBOOT_NIC"
  )
  leanos_validate_q35_netboot_command "$command_name"
}
