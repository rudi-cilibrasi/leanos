#!/usr/bin/env python3
"""Generate a lab-only exact firmware gate from the native DSDT capture."""
import hashlib
import json
from pathlib import Path
import runpy
import sys

root = Path(__file__).resolve().parents[1]
capture = root / 'hardware/lab/observations/qotom-dsdt-20260911'
manifest = json.loads((capture / 'manifest.json').read_text())


def pinned(name):
    raw = (capture / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
        raise ValueError('native firmware capture hash mismatch: ' + name)
    return raw


decoder = runpy.run_path(str(root / 'scripts/check-qotom-acpi-capture.py'))
_, metadata, files = decoder['extract'](pinned('cycle-1/serial.raw'),
    pinned('cycle-1/multiboot2.bin'), dsdt=True)
if metadata != json.loads(pinned('cycle-1/acpi.json')):
    raise ValueError('native firmware metadata mismatch')
tables = metadata['tables']
if len(tables) != 12 or metadata['dsdt_address'] != 0xb979f180:
    raise ValueError('unexpected reviewed firmware profile')
lines = ['/* Generated lab-only exact firmware inputs; do not edit. */',
         '#ifndef LEANOS_LAB_ECAM_FIRMWARE_INPUTS_H',
         '#define LEANOS_LAB_ECAM_FIRMWARE_INPUTS_H',
         f'#define LAB_ECAM_FIRMWARE_TABLE_COUNT {len(tables)}u']
for i, table in enumerate(tables):
    name = f"{table['address']:016x}.bin"
    raw = pinned('cycle-1/acpi/' + name)
    if raw != files[name]:
        raise ValueError('captured table differs from serial bytes')
    lines.append(f'static const uint8_t lab_ecam_firmware_bytes_{i}[] = {{')
    for offset in range(0, len(raw), 16):
        lines.append('    ' + ','.join(f'0x{x:02x}' for x in raw[offset:offset+16]) + ',')
    lines.append('};')
lines.append('static const struct lab_ecam_firmware_table lab_ecam_expected_tables[] = {')
for i, table in enumerate(tables):
    lines.append(f"    {{UINT64_C(0x{table['address']:x}), lab_ecam_firmware_bytes_{i}, {table['length']}u}},")
lines.extend(['};', '#endif', ''])
Path(sys.argv[1]).write_text('\n'.join(lines))
