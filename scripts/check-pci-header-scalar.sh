#!/usr/bin/env bash
# Link and execute only the scalar status and query functions, without the Lean runtime.
set -euo pipefail
cd "$(dirname "$0")/.."
build=build/pci-header-scalar
mkdir -p "$build"
lake build LeanOS.PCIHeaderObservation
cp .lake/build/ir/LeanOS/PCIHeaderObservation.c "$build/header.c"
"${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fPIC -mno-red-zone \
  -ffunction-sections -fdata-sections -I"$(lean --print-prefix)/include" \
  -c "$build/header.c" -o "$build/header.o"
symbol=lp_leanos_LeanOS_PCIHeaderObservation_Scalar_status
query=lp_leanos_LeanOS_PCIHeaderObservation_Scalar_query
ld -r --gc-sections -u "$symbol" -u "$query" "$build/header.o" -o "$build/retained.o"
# Drop unused symbol-table entries left by the relocatable garbage-collecting link.
objcopy --strip-unneeded "$build/retained.o"
test -z "$(nm -u "$build/retained.o")"
test "$(nm --defined-only "$build/retained.o" | awk '{print $3}' | sort)" = "$(printf '%s\n' "$symbol" "$query" | sort)"
"${CC:-gcc}" -shared -nostdlib -Wl,--no-undefined "$build/retained.o" -o "$build/status.so"
python3 scripts/test-pci-header-scalar.py "$build/status.so"
