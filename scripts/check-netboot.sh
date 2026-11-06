#!/usr/bin/env bash
# Boot LeanOS over the network (PXE/TFTP) on the pinned q35 platform, under
# SeaBIOS and under OVMF.
#
# The q35 netboot construction (leanos_q35_netboot_command in
# scripts/q35-platform.sh) serves a TFTP tree made from an ISO
# (scripts/build-netboot-tree.sh) through QEMU's user network. Its only boot
# device is a transitional virtio-net function at 00:03.0, the optional
# network slot of the q35 manifest (LeanOS.DMAQuarantine.q35Manifest).
# SeaBIOS boots it through QEMU's iPXE option ROM and GRUB i386-pc's core.0;
# OVMF through its own PXE client and GRUB x86_64-efi's core.efi.
#
# The netboot image (issue #601) admits exactly that NIC: present, unassigned
# and quarantined to Command 0 like every other function, its snapshot
# DMAQuarantine.q35OptionalNetworkPresentSnapshot checked by the generated
# leanos_validate_q35_netboot_dma_snapshot and rechecked at every CPL3 gate.
# It must reach the full PASS under both firmwares:
#   SeaBIOS  scripts/run-image.sh's netboot scenario: the complete serial
#            protocol, the DMA and VT-d snapshots;
#   OVMF     the guest's PASS exit and FINAL status=PASS after its BOOT
#            record, and the six exact DMA-FUNCTION records and summary
#            (write-dma-snapshot.py, profile netboot-ovmf). OVMF prints its
#            console before the kernel, reports a different memory map and
#            leaves every function bus-mastering, so the SeaBIOS transcript
#            is not its transcript.
#
# The canonical image admits that slot empty, as under `-nic none`. Netbooted
# the same way it must still stop at platform admission with `FINAL
# status=FAIL reason=dma-q35-nic-none` after its BOOT record, under both
# firmwares: the production kernel does not admit the boot NIC.
#
# usage: check-netboot.sh [<netboot-iso>] [<canonical-iso>] [<output-dir>]
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

version="${LEANOS_VERSION:-0.1.0}"
netboot_image="${1:-build/boot/leanos-${version}-x86_64-netboot.iso}"
canonical_image="${2:-build/boot/leanos-${version}-x86_64.iso}"
output="${3:-build/boot/netboot}"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-180}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
corpus="${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}"
serial_protocol_tsv="$(dirname "$corpus")/serial-protocol.tsv"
source_revision_file="${LEANOS_SOURCE_REVISION_FILE:-build/boot/SOURCE_REVISION}"
# isa-debug-exit reports (code << 1) | 1; the kernel writes 0x10 on PASS and
# 0x11 on FAIL.
readonly pass_exit=33
readonly fail_exit=35
readonly refusal='FINAL status=FAIL reason=dma-q35-nic-none'

for image in "$netboot_image" "$canonical_image"; do
  [[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
done
[[ -f "$LEANOS_OVMF_CODE" && -f "$LEANOS_OVMF_VARS" ]] || {
  echo "error: missing OVMF firmware; install Ubuntu package ovmf=2024.02-2ubuntu0.9" >&2
  exit 1
}
[[ -f "$corpus" && -f "$serial_protocol_tsv" && -f "$source_revision_file" ]] || {
  echo "error: missing build records next to '$corpus'; run ./scripts/build-image.sh first" >&2
  exit 1
}
[[ "$output" != *,* ]] || { echo "error: output directory must not contain a comma" >&2; exit 1; }
mkdir -p "$output"
output="$(cd "$output" && pwd)"
./scripts/build-netboot-tree.sh "$netboot_image" "$output/netboot-tree"
./scripts/build-netboot-tree.sh "$canonical_image" "$output/canonical-tree"

# Boot one tree under one firmware; prints the guest's exit status.
netboot() {
  local firmware="$1" tree="$2" log="$3" status=0
  local -a command=()
  rm -f "$log"
  LEANOS_QEMU_FIRMWARE="$firmware" \
    leanos_q35_netboot_command command "$tree" "$qemu" "$memory_mib" "$log" ||
    { printf '1\n'; return 0; }
  timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}" >&2 || status=$?
  printf '%s\n' "$status"
}

# Under OVMF the BOOT record can follow firmware console output on its line.
boot_record() { grep -a -o -m1 'LEANOS/[0-9]* BOOT target=x86_64-q35 .*' "$1" || true; }
final_record() { grep -a -m1 '^LEANOS/[0-9]* FINAL ' "$1" || true; }

failed=0
# The netboot image: the full PASS.
log="$output/netboot-seabios.serial.log"
if LEANOS_BOOT_SCENARIO=netboot LEANOS_QEMU_FIRMWARE=seabios \
    LEANOS_QEMU_TIMEOUT_SECONDS="$limit" LEANOS_SERIAL_LOG="$log" \
    LEANOS_DMA_SNAPSHOT="$output/netboot-seabios-dma-snapshot.tsv" \
    LEANOS_VTD_SNAPSHOT="$output/netboot-seabios-vtd-snapshot.tsv" \
    ./scripts/run-image.sh "$netboot_image" >"$output/netboot-seabios.run.log" 2>&1; then
  echo "netboot seabios netboot-image PASS protocol=complete final='$(final_record "$log" | sed 's/^LEANOS\/[0-9]* //')'"
else
  echo "netboot seabios netboot-image FAIL: scripts/run-image.sh rejected the run" >&2
  grep -a 'failure_class=' "$output/netboot-seabios.run.log" >&2 || tail -5 "$output/netboot-seabios.run.log" >&2
  failed=1
fi

log="$output/netboot-ovmf.serial.log"
status="$(netboot ovmf "$output/netboot-tree" "$log")"
boot="$(boot_record "$log")"
final="$(final_record "$log")"
if [[ $status -eq $pass_exit && -n "$boot" && "$final" == *' FINAL status=PASS'* ]] &&
    LEANOS_SERIAL_PROTOCOL_TSV="$serial_protocol_tsv" \
    ./scripts/write-dma-snapshot.py --profile netboot-ovmf --serial-log "$log" \
      --source-revision "$source_revision_file" \
      --qemu-version "$("$qemu" --version 2>&1 | head -n 1)" \
      --output "$output/netboot-ovmf-dma-snapshot.tsv"; then
  echo "netboot ovmf netboot-image PASS exit=$status dma=exact final='${final#LEANOS/* }'"
else
  echo "netboot ovmf netboot-image FAIL exit=$status boot='${boot:-none}' final='${final:-none}'" >&2
  failed=1
fi

# The canonical image: fail-closed at platform admission.
for firmware in seabios ovmf; do
  log="$output/canonical-$firmware.serial.log"
  status="$(netboot "$firmware" "$output/canonical-tree" "$log")"
  boot="$(boot_record "$log")"
  final="$(final_record "$log")"
  if [[ $status -eq $fail_exit && -n "$boot" && "$final" == *" $refusal" ]]; then
    echo "netboot $firmware canonical-image fail-closed exit=$status final='${final#LEANOS/* }'"
  else
    echo "netboot $firmware canonical-image UNEXPECTED exit=$status boot='${boot:-none}' final='${final:-none}'" >&2
    failed=1
  fi
done
exit "$failed"
