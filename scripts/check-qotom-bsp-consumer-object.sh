#!/usr/bin/env bash
# Called after scalar generation and generated ABI rendering by the host runner.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build=build/qotom-madt-stream
"${CC:-gcc}" -O2 -ffreestanding -fno-stack-protector -fno-pic -mno-red-zone \
  -mgeneral-regs-only -ffunction-sections -fdata-sections -Wall -Wextra -Werror \
  -Ibuild/boundary-abi -c tests/qotom-bsp-consumer-object.c -o "$build/consumer.o"
ld --gc-sections -e qotom_bsp_consumer_probe \
  -u leanos_qotom_machine_topology_admission_result_query "$build/stream.o" \
  "$build/consumer.o" -o "$build/consumer.elf"
test -z "$(nm -u "$build/consumer.elf")"
nm --defined-only "$build/consumer.elf" > "$build/consumer-symbols.txt"
python3 - "$build/consumer-symbols.txt" <<'PY'
import sys
from pathlib import Path
rows = [line.split() for line in Path(sys.argv[1]).read_text().splitlines()]
expected = {'qotom_bsp_consumer_probe',
            'leanos_qotom_madt_stream_byte_step_query',
            'leanos_qotom_madt_stream_finish_query',
            'leanos_qotom_machine_topology_admission_result_query',
            '__bss_start', '_edata', '_end'}
actual = {r[-1] for r in rows}
# GCC may outline the static inline consumer; Clang may inline it.
optional = {'qotom_bind_validated_madt_entries',
            'l_LeanOS_QotomMadtStream_byteStepQuery',
            'l_LeanOS_QotomMadtStream_finishQuery',
            'l_LeanOS_QotomMadtStream_machineTopologyAdmissionResultQuery'}
if not expected <= actual or actual - expected - optional:
    raise SystemExit(f'unexpected consumer symbols: {actual ^ expected}')
for _, kind, name in rows:
    if name not in {'__bss_start', '_edata', '_end'} and kind not in {'T', 't', 'R', 'r'}:
        raise SystemExit(f'unexpected writable or special symbol: {kind} {name}')
PY
printf '%s\n' 'PASS bounded BSP consumer links without runtime dependencies or writable state'
