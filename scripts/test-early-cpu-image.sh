#!/usr/bin/env bash
# Focused negative CPU execution fixtures, separate from canonical q35 evidence.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
image="${1:?usage: test-early-cpu-image.sh ISO [output-directory]}"
output="${2:-build/early-cpu-negative}"
mkdir -p "$output"
export LEANOS_QEMU_ACCELERATOR=tcg
source scripts/q35-platform.sh
source build/boot/serial-protocol.sh
for feature in msr nx syscall; do
  cpu_command=()
  leanos_q35_command cpu_command qemu-system-x86_64 128 "$output/no-$feature.log" "$image"
  # Deliberately mutate only the CPU feature after constructing and validating
  # the common machine/device layout. These are rejection fixtures, never an
  # alternative accepted canonical CPU profile.
  for ((i=0; i<${#cpu_command[@]}; i++)); do
    if [[ "${cpu_command[$i]}" == -cpu ]]; then
      cpu_command[$((i+1))]="max,$feature=off"
    fi
  done
  set +e
  timeout --signal=TERM --kill-after=2s 10s "${cpu_command[@]}" > "$output/no-$feature.stderr" 2>&1
  cpu_status=$?
  set -e
  [[ "$cpu_status" == 124 ]] || { echo "unexpected QEMU status: $cpu_status" >&2; exit 1; }
  grep -Fxq "$LEANOS_SERIAL_3_FINAL status=FAIL reason=early-cpu-capability" "$output/no-$feature.log"
  [[ "$(wc -l < "$output/no-$feature.log")" == 1 ]]
  echo "CPU $feature=off: exact early rejection and terminal timeout verified"
done
