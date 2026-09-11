#!/usr/bin/env python3
"""Decode only the manifest-pinned native MCFG for the hosted ECAM fixture."""
import hashlib
import json
from pathlib import Path
import struct
import sys

root = Path(__file__).resolve().parents[1]
capture = root / 'hardware/lab/observations/qotom-bootstrap-20260911'
manifest = json.loads((capture / 'manifest.json').read_text())
def pinned(name):
    raw = (capture / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
        raise ValueError(f'capture hash mismatch: {name}')
    return raw
metadata = json.loads(pinned('cycle-1/acpi.json'))
allocations = [table for table in metadata['tables'] if table['signature_hex'] == '4d434647']
if len(allocations) != 1:
    raise ValueError('expected one captured MCFG')
table = allocations[0]
raw = pinned(f"cycle-1/acpi/{table['address']:016x}.bin")
if (raw[:4] != b'MCFG' or len(raw) != 60 or
    struct.unpack_from('<I', raw, 4)[0] != len(raw) or sum(raw) % 256 or
    hashlib.sha256(raw).hexdigest() != table['sha256'] or table['length'] != len(raw) or
    raw[36:44] != bytes(8)):
    raise ValueError('invalid captured MCFG envelope or shape')
base, segment, first, last, reserved = struct.unpack_from('<QHBBI', raw, 44)
if reserved or first > last:
    raise ValueError('invalid captured MCFG allocation')
Path(sys.argv[1]).write_text(
    '/* Manifest-pinned native MCFG; hosted fixture only. */\n'
    '#define QOTOM_CAPTURED_ECAM_ALLOCATION '
    f'{{UINT64_C(0x{base:x}), {segment}, {first}, {last}}}\n')
