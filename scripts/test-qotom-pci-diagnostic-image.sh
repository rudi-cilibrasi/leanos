#!/usr/bin/env bash
# Build the opt-in diagnostic from an existing boot object graph, then execute it.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build="$root/build/boot"
output="${1:-build/ci/cpu-diagnostics/qotom-pci}"
[[ -f "$build/generated-image-objects.mk" ]] || {
  echo 'error: run scripts/build-image.sh before the PCI diagnostic image test' >&2
  exit 1
}
mkdir -p "$output"
# A selective evidence build may not have built this opt-in image yet.
plan="$build/boot-page-plan-qotom-pci-diagnostic.h"
[[ -f "$plan" ]] || scripts/generate-boot-page-plan.sh --stub "$plan"
make -f "$build/generated-image-objects.mk" -j "${LEANOS_BUILD_JOBS:-2}" \
  "$build/leanos-qotom-pci-diagnostic-prelink.elf"
scripts/generate-boot-page-plan.sh "$build/leanos-qotom-pci-diagnostic-prelink.elf" "$plan"
make -f "$build/generated-image-objects.mk" -j "${LEANOS_BUILD_JOBS:-2}" \
  "$build/leanos-qotom-pci-diagnostic.elf"
scripts/generate-boot-page-plan.sh "$build/leanos-qotom-pci-diagnostic.elf" "${plan%.h}.final.h"
cmp "$plan" "${plan%.h}.final.h"
python3 - "$build/pci-config-read.o" <<'PY'
from pathlib import Path
import runpy
import sys
runpy.run_path('scripts/check-pci-config-read.py')['check'](Path(sys.argv[1]))
PY
scripts/check-j1900-cpu-host.sh ordinary > "$output/cpu-replay-build.log" 2>&1
scripts/check-qotom-pci-inventory-host.sh ordinary > "$output/pci-replay-build.log" 2>&1
python3 scripts/test-qotom-pci-diagnostic.py
python3 scripts/test-qotom-handoff-capture.py
python3 scripts/test-qotom-acpi-capture.py
python3 scripts/test-qotom-pci-read-trace.py
python3 scripts/test-qotom-pci-diagnostic-image.py --output "$output"
