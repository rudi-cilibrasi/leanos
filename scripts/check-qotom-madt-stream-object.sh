#!/usr/bin/env bash
# Inspect the retained scalar export; this ELF is a link probe, not executable boot code.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build=build/qotom-madt-stream
mkdir -p "$build"
prefix="$(lean --print-prefix)"
lake env lean -c "$build/QotomMadtStream.c" LeanOS/QotomMadtStream.lean
"${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fno-pic -mno-red-zone \
  -ffunction-sections -fdata-sections -I"$prefix/include" \
  -c "$build/QotomMadtStream.c" -o "$build/stream.o"
ld --gc-sections -e leanos_qotom_madt_stream_byte_step_query \
  -u leanos_qotom_madt_stream_finish_query \
  "$build/stream.o" -o "$build/retained.elf"
test -z "$(nm -u "$build/retained.elf")"
nm --defined-only "$build/retained.elf" > "$build/retained-symbols.txt"
python3 - "$build/retained-symbols.txt" <<'PY'
import sys
from pathlib import Path
symbols = {line.split()[-1] for line in Path(sys.argv[1]).read_text().splitlines()}
expected = {'l_LeanOS_QotomMadtStream_byteStepQuery',
            'leanos_qotom_madt_stream_byte_step_query',
            'l_LeanOS_QotomMadtStream_finishQuery', 'leanos_qotom_madt_stream_finish_query', '__bss_start', '_edata', '_end'}
if symbols != expected:
    raise SystemExit(f'unexpected retained symbols: {symbols ^ expected}')
PY
printf '%s\n' 'PASS scalar export links without allocation or Lean runtime dependencies'
