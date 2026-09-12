#!/usr/bin/env bash
# Produce only the proved scalar export for the freestanding lab image.
set -euo pipefail
cd "$(dirname "$0")/.."
build="${1:?usage: build-qotom-native-pci-object.sh output-directory}"
mkdir -p "$build"
lake build LeanOS.QotomNativePCISnapshot
./scripts/generate-oracle.sh build/boundary-abi
for module in PCIHeaderObservation QotomNativePCIFields QotomPCIFinalAdmission; do
  "${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fno-pic -mno-red-zone \
    -mgeneral-regs-only -ffunction-sections -fdata-sections \
    -I"$(lean --print-prefix)/include" \
    -c ".lake/build/ir/LeanOS/$module.c" -o "$build/$module.o"
done
ld -r --gc-sections -u leanos_qotom_native_pci_header_check \
  -u leanos_qotom_pci_final_admission \
  "$build/PCIHeaderObservation.o" "$build/QotomNativePCIFields.o" \
  "$build/QotomPCIFinalAdmission.o" -o "$build/native-pci.o"
objcopy --strip-unneeded "$build/native-pci.o"
test -z "$(nm -u "$build/native-pci.o")"
nm --defined-only "$build/native-pci.o" > "$build/symbols.txt"
python3 - "$build/symbols.txt" <<'PY'
from pathlib import Path
import sys
symbols = [line.split() for line in Path(sys.argv[1]).read_text().splitlines()]
allowed = {'lp_leanos_LeanOS_QotomNativePCIFields_' + s
           for s in ('expected', 'matchesFields', 'checkHeader')}
allowed |= {'lp_leanos_LeanOS_PCIHeaderObservation_Scalar_' + s for s in ('status', 'query')}
allowed.add('leanos_qotom_native_pci_header_check')
allowed |= {'lp_leanos_LeanOS_QotomPCIFinalAdmission_' + s
            for s in ('commandsAccepted', 'accepted')}
allowed.add('leanos_qotom_pci_final_admission')
functions = {s[2] for s in symbols if len(s) == 3 and s[1] == 'T'}
if any(len(s) != 3 or s[1] not in ('T', 'r', 'R') for s in symbols):
    raise SystemExit('unexpected state in native PCI image object')
if not functions <= allowed or not {
        'leanos_qotom_native_pci_header_check',
        'leanos_qotom_pci_final_admission'} <= functions:
    raise SystemExit('unexpected functions in native PCI image object')
PY
