#!/usr/bin/env bash
# Authoritative QEMU 8.2.2 q35 construction used by every emulator runner.
#
# The machine-integrated host/ISA/AHCI/SMBus functions are fixed by q35.  All
# optional defaults are suppressed; the VGA function, boot CD attachment, and
# ISA debug-exit device are then added explicitly.  This is reproducible QEMU
# construction evidence, not a proof of firmware, PCI, or DMA semantics.

readonly LEANOS_Q35_TOPOLOGY_VERSION=000800020002

leanos_validate_q35_command() {
  local command_name="$1"
  local -n q35_command="$command_name"
  local machine=0 nodefaults=0 vga=0 cdrom=0 cdrom_drive=0
  local debug_exit=0 devices=0 cpu_options=0
  local argument previous=

  for argument in "${q35_command[@]}"; do
    if [[ "$previous" == -cpu ]]; then
      case "$argument" in
        max|max,phys-bits=48) ((cpu_options += 1)) ;;
        *)
          echo "error: q35 platform CPU options drifted" >&2
          return 1
          ;;
      esac
    fi
    case "$argument" in
      q35,accel=tcg) ((machine += 1)) ;;
      -nodefaults) ((nodefaults += 1)) ;;
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
    echo "error: q35 platform requires the exact q35/TCG machine and -nodefaults" >&2
    return 1
  }
  [[ $devices -eq 3 && $vga -eq 1 && $cdrom -eq 1 && $cdrom_drive -eq 1 &&
     $debug_exit -eq 1 && $cpu_options -eq 1 ]] || {
    echo "error: q35 platform device topology drifted" >&2
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
  local -n q35_command="$command_name"

  q35_command=(
    "$qemu"
    -machine q35,accel=tcg
    -nodefaults
    -cpu "$cpu"
    -smp 1
    -m "${memory_mib}M"
    -display none
    -monitor none
    -serial "file:$serial_log"
    -no-reboot
    -no-shutdown
    -nic none
    -device VGA,bus=pcie.0,addr=0x1
    -device isa-debug-exit,iobase=0xf4,iosize=0x04
    -drive "id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=$image"
    -device ide-cd,drive=leanos-cd,bus=ide.0
  )
  leanos_validate_q35_command "$command_name"
}
