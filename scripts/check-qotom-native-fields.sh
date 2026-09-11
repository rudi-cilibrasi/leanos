#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
build=build/qotom-native-fields
mkdir -p "$build"
lake build LeanOS.QotomNativePCIFields
"${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fPIC -mno-red-zone \
  -ffunction-sections -fdata-sections -I"$(lean --print-prefix)/include" \
  -c .lake/build/ir/LeanOS/QotomNativePCIFields.c -o "$build/fields.o"
"${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fPIC -mno-red-zone \
  -ffunction-sections -fdata-sections -I"$(lean --print-prefix)/include" \
  -c .lake/build/ir/LeanOS/PCIHeaderObservation.c -o "$build/header.o"
prefix=lp_leanos_LeanOS_QotomNativePCIFields
ld -r --gc-sections -u "${prefix}_expected" -u "${prefix}_matchesFields" -u "${prefix}_checkHeader" \
  "$build/fields.o" "$build/header.o" -o "$build/retained.o"
objcopy --strip-unneeded "$build/retained.o"
test -z "$(nm -u "$build/retained.o")"
# Compiler-generated read-only tables are allowed; writable state is not.
nm --defined-only "$build/retained.o" > "$build/symbols.txt"
python3 - "$build/symbols.txt" <<'CHECK'
from pathlib import Path
import sys
symbols = [line.split() for line in Path(sys.argv[1]).read_text().splitlines()]
expected = {'lp_leanos_LeanOS_QotomNativePCIFields_' + name
            for name in ('expected', 'matchesFields', 'checkHeader')}
expected |= {'lp_leanos_LeanOS_PCIHeaderObservation_Scalar_' + name
             for name in ('status', 'query')}
if any(len(s) != 3 or s[1] not in ('T', 'r', 'R') for s in symbols):
    raise SystemExit('unexpected state or symbol in retained scalar object')
if {s[2] for s in symbols if s[1] == 'T'} != expected:
    raise SystemExit('unexpected retained scalar functions')
CHECK
"${CC:-gcc}" -shared -nostdlib -Wl,--no-undefined "$build/retained.o" -o "$build/fields.so"
python3 scripts/test-qotom-native-fields.py "$build/fields.so"
