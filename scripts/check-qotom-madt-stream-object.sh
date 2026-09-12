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
  -u leanos_qotom_madt_nmi_policy_query \
  -u leanos_qotom_inherited_lvt_policy_query \
  "$build/stream.o" -o "$build/retained.elf"
test -z "$(nm -u "$build/retained.elf")"
nm --defined-only "$build/retained.elf" > "$build/retained-symbols.txt"
python3 - "$build/retained-symbols.txt" <<'PY'
import sys
from pathlib import Path
rows = [line.split() for line in Path(sys.argv[1]).read_text().splitlines()]
symbols = {row[-1] for row in rows}
required = {'leanos_qotom_madt_stream_byte_step_query',
            'leanos_qotom_madt_stream_finish_query',
            'leanos_qotom_madt_nmi_policy_query',
            'leanos_qotom_inherited_lvt_policy_query',
            '__bss_start', '_edata', '_end'}
# Clang may inline the generated internal functions into the exported wrappers.
optional = {'l_LeanOS_QotomMadtStream_byteStepQuery',
            'l_LeanOS_QotomMadtStream_finishQuery',
            'l_LeanOS_QotomMadtStream_nmiPolicyQuery',
            'l_LeanOS_QotomMadtStream_inheritedLvtPolicyQuery'}
if not required <= symbols or symbols - required - optional:
    raise SystemExit(f'unexpected retained symbols: {symbols ^ required}')
for _, kind, name in rows:
    if name not in {'__bss_start', '_edata', '_end'} and kind not in {'T', 't', 'R', 'r'}:
        raise SystemExit(f'unexpected writable or special symbol: {kind} {name}')

PY
printf '%s\n' 'PASS scalar export links without allocation or Lean runtime dependencies'
