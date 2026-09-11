#!/usr/bin/env bash
# Keep only the two proved scalar exports in the lab image.
set -euo pipefail
cd "$(dirname "$0")/.."
build="${1:?usage: build-qotom-bsp-object.sh output-directory}"
mkdir -p "$build"
lake build LeanOS.QotomMadtStream
./scripts/generate-oracle.sh build/boundary-abi
lake env lean -c "$build/QotomMadtStream.c" LeanOS/QotomMadtStream.lean
"${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fno-pic -mno-red-zone \
  -mgeneral-regs-only -ffunction-sections -fdata-sections \
  -I"$(lean --print-prefix)/include" -c "$build/QotomMadtStream.c" -o "$build/stream.o"
ld -r --gc-sections -u leanos_qotom_madt_stream_byte_step_query \
  -u leanos_qotom_madt_stream_finish_query "$build/stream.o" -o "$build/bsp.o"
objcopy --strip-unneeded "$build/bsp.o"
test -z "$(nm -u "$build/bsp.o")"
nm --defined-only "$build/bsp.o" > "$build/symbols.txt"
python3 - "$build/symbols.txt" <<'PY'
from pathlib import Path
import sys
rows = [s.split() for s in Path(sys.argv[1]).read_text().splitlines()]
required = {'leanos_qotom_madt_stream_byte_step_query', 'leanos_qotom_madt_stream_finish_query'}
allowed = required | {'l_LeanOS_QotomMadtStream_byteStepQuery', 'l_LeanOS_QotomMadtStream_finishQuery'}
actual = {s[2] for s in rows if len(s) == 3 and s[1] == 'T'}
if not required <= actual <= allowed or any(len(s) != 3 or s[1] not in {'T','r','R'} for s in rows):
    raise SystemExit('unexpected state or function in native BSP object')
PY
