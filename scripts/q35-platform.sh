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
  local argument previous= first_device= accelerator

  accelerator="$(leanos_qemu_accelerator)" || return 1

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
      isa-debug-exit,iobase=0xf4,iosize=0x04) ((debug_exit += 1)) ;;
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
  [[ $devices -eq 4 && $iommu -eq 1 && $vga -eq 1 && $cdrom -eq 1 &&
     $cdrom_drive -eq 1 && $debug_exit -eq 1 && $cpu_options -eq 1 &&
     $smp_options -eq 1 ]] || {
    echo "error: q35 platform device topology drifted" >&2
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
    -drive "id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=$image"
    -device ide-cd,drive=leanos-cd,bus=ide.0
  )
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
