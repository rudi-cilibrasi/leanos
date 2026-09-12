#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
build=build/pci-capabilities
mkdir -p "$build"
"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/pci-capabilities.c -o "$build/ordinary"
"$build/ordinary"
source scripts/hosted-sanitizer-config.sh
leanos_assert_pinned_toolchain
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/pci-capabilities.c -o "$build/sanitized"
leanos_run_sanitized "$build/sanitized"
printf '%s\n' 'PASS bounded capability lists: maximum size, cycles, read failures, pointer bounds, drift and backward links'

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror -Iboot tests/qotom-pci-capabilities-lab.c -o "$build/lab-ordinary"
"$build/lab-ordinary"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  -Iboot tests/qotom-pci-capabilities-lab.c -o "$build/lab-sanitized"
leanos_run_sanitized "$build/lab-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/pci-af-observation.c -o "$build/af-ordinary"
"$build/af-ordinary"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/pci-af-observation.c -o "$build/af-sanitized"
leanos_run_sanitized "$build/af-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror -Iboot -DLEANOS_QOTOM_AF_OBSERVATION tests/qotom-pci-capabilities-lab.c -o "$build/af-lab-ordinary"
"$build/af-lab-ordinary"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  -Iboot -DLEANOS_QOTOM_AF_OBSERVATION tests/qotom-pci-capabilities-lab.c -o "$build/af-lab-sanitized"
leanos_run_sanitized "$build/af-lab-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ehci-capabilities.c -o "$build/ehci-ordinary"
"$build/ehci-ordinary"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ehci-capabilities.c -o "$build/ehci-sanitized"
leanos_run_sanitized "$build/ehci-sanitized"

python3 scripts/generate-qotom-ecam-firmware.py "$build/qotom-ecam-firmware-inputs.h"
for test in qotom-hda-state-window qotom-hda-state-arm qotom-hda-window qotom-hda-arm qotom-ahci-bme-window qotom-ahci-bme-arm qotom-ahci-interrupt-window qotom-ahci-interrupt-arm qotom-ahci-port-window qotom-ahci-port-arm qotom-ahci-window qotom-ahci-arm qotom-ehci-window qotom-ehci-arm qotom-ehci-semaphore qotom-ehci-semaphore-arm qotom-pm-delay qotom-ehci-smi-window qotom-ehci-smi-arm qotom-ehci-operational-window qotom-ehci-operational-arm qotom-ehci-bme-window qotom-ehci-bme-arm qotom-xhci-window qotom-xhci-arm qotom-xhci-ext-window qotom-xhci-ext-arm qotom-xhci-semaphore-window qotom-xhci-semaphore-arm qotom-xhci-smi-window qotom-xhci-smi-arm qotom-xhci-operational-window qotom-xhci-operational-arm qotom-xhci-bme-window qotom-xhci-bme-arm; do
  "${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror -Iboot -Ihardware/lab -I"$build" "tests/$test.c" -o "$build/$test"
  "$build/$test"
  "$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
    -Iboot -Ihardware/lab -I"$build" "tests/$test.c" -o "$build/$test-sanitized"
  leanos_run_sanitized "$build/$test-sanitized"
done

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ehci-legacy.c -o "$build/ehci-legacy"
"$build/ehci-legacy"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ehci-legacy.c -o "$build/ehci-legacy-sanitized"
leanos_run_sanitized "$build/ehci-legacy-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ehci-handoff.c -o "$build/ehci-handoff"
"$build/ehci-handoff"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ehci-handoff.c -o "$build/ehci-handoff-sanitized"
leanos_run_sanitized "$build/ehci-handoff-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ehci-smi.c -o "$build/ehci-smi"
"$build/ehci-smi"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ehci-smi.c -o "$build/ehci-smi-sanitized"
leanos_run_sanitized "$build/ehci-smi-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ehci-operational.c -o "$build/ehci-operational"
"$build/ehci-operational"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ehci-operational.c -o "$build/ehci-operational-sanitized"
leanos_run_sanitized "$build/ehci-operational-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ehci-bme.c -o "$build/ehci-bme"
"$build/ehci-bme"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ehci-bme.c -o "$build/ehci-bme-sanitized"
leanos_run_sanitized "$build/ehci-bme-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-xhci-capabilities.c -o "$build/xhci-capabilities"
"$build/xhci-capabilities"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-xhci-capabilities.c -o "$build/xhci-capabilities-sanitized"
leanos_run_sanitized "$build/xhci-capabilities-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-xhci-legacy.c -o "$build/xhci-legacy"
"$build/xhci-legacy"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-xhci-legacy.c -o "$build/xhci-legacy-sanitized"
leanos_run_sanitized "$build/xhci-legacy-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-xhci-handoff.c -o "$build/xhci-handoff"
"$build/xhci-handoff"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-xhci-handoff.c -o "$build/xhci-handoff-sanitized"
leanos_run_sanitized "$build/xhci-handoff-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-xhci-smi.c -o "$build/xhci-smi"
"$build/xhci-smi"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-xhci-smi.c -o "$build/xhci-smi-sanitized"
leanos_run_sanitized "$build/xhci-smi-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-xhci-operational.c -o "$build/xhci-operational"
"$build/xhci-operational"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-xhci-operational.c -o "$build/xhci-operational-sanitized"
leanos_run_sanitized "$build/xhci-operational-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-xhci-bme.c -o "$build/xhci-bme"
"$build/xhci-bme"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-xhci-bme.c -o "$build/xhci-bme-sanitized"
leanos_run_sanitized "$build/xhci-bme-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/pci-express-observation.c -o "$build/express"
"$build/express"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/pci-express-observation.c -o "$build/express-sanitized"
leanos_run_sanitized "$build/express-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror -Iboot tests/qotom-pcie-device-lab.c -o "$build/pcie-device-lab"
"$build/pcie-device-lab"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  -Iboot tests/qotom-pcie-device-lab.c -o "$build/pcie-device-lab-sanitized"
leanos_run_sanitized "$build/pcie-device-lab-sanitized"

python3 scripts/test-qotom-pcie-device-capture.py

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ahci-capabilities.c -o "$build/ahci-capabilities"
"$build/ahci-capabilities"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ahci-capabilities.c -o "$build/ahci-capabilities-sanitized"
leanos_run_sanitized "$build/ahci-capabilities-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ahci-port.c -o "$build/ahci-port"
"$build/ahci-port"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ahci-port.c -o "$build/ahci-port-sanitized"
leanos_run_sanitized "$build/ahci-port-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ahci-interrupts.c -o "$build/ahci-interrupts"
"$build/ahci-interrupts"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ahci-interrupts.c -o "$build/ahci-interrupts-sanitized"
leanos_run_sanitized "$build/ahci-interrupts-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-ahci-bme.c -o "$build/ahci-bme"
"$build/ahci-bme"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-ahci-bme.c -o "$build/ahci-bme-sanitized"
leanos_run_sanitized "$build/ahci-bme-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-hda-observation.c -o "$build/hda-observation"
"$build/hda-observation"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-hda-observation.c -o "$build/hda-observation-sanitized"
leanos_run_sanitized "$build/hda-observation-sanitized"

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/qotom-hda-state.c -o "$build/hda-state"
"$build/hda-state"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/qotom-hda-state.c -o "$build/hda-state-sanitized"
leanos_run_sanitized "$build/hda-state-sanitized"
