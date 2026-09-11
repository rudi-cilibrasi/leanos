#!/usr/bin/env python3
"""Bind the ECAM arm record to complete captured firmware, without admission."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = b'LEANOS-LAB/1 ECAM-ARM '
ARM = PREFIX + b'firmware=exact root=checked access=read32\n'


def firmware_matches(metadata, files):
    capture = ROOT / 'hardware/lab/observations/qotom-dsdt-20260911'
    manifest = json.loads((capture / 'manifest.json').read_bytes())
    def pinned(name):
        raw = (capture / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
            raise ValueError('reviewed firmware hash mismatch')
        return raw
    expected = json.loads(pinned('cycle-1/acpi.json'))
    # The handoff hash binds this capture's loader input, not the static ACPI
    # firmware gate. Rebuilding the ELF changes handoff bytes/placement. The
    # preceding ACPI decoder has already bound this hash to the actual handoff.
    if (metadata is None or set(metadata) != set(expected) or
            any(metadata[key] != value for key, value in expected.items()
                if key != 'handoff_sha256')):
        return False
    names = {f"{t['address']:016x}.bin" for t in expected['tables']}
    if set(files) != names:
        return False
    return all(files[name] == pinned('cycle-1/acpi/' + name) for name in names)


def extract(raw, protocol, metadata, files):
    """Consume after ACPI extraction and before bootstrap/memory extraction."""
    lines = raw.splitlines(keepends=True)
    if not lines or not raw.endswith(b'\n'):
        raise ValueError('ECAM capture terminator')
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    scans = [i for i, line in enumerate(lines)
             if line.startswith(protocol['PCI-SCAN'].encode() + b' ')]
    rejected = lines[-1] == protocol['FINAL'].encode() + b' status=FAIL reason=qotom-ecam-arm\n'
    fault = lines[-1] == protocol['FINAL'].encode() + b' status=FAIL reason=qotom-ecam-transaction\n'
    if not indices:
        if scans or fault:
            raise ValueError('ECAM scan/fault without arm record')
        if not rejected:
            return raw, None  # The ordinary diagnostic replay checks earlier CPU failures.
        if metadata is None or len(lines) != 6:
            raise ValueError('ECAM rejection without complete observations')
        return raw, {'schema': 'leanos-ecam-capture-v1', 'armed': False,
                     'firmware_matches': firmware_matches(metadata, files),
                     'platform_admitted': False}
    if indices != [5] or lines[5] != ARM:
        raise ValueError('missing, repeated or misplaced ECAM arm record')
    if rejected or (scans != [6] and not (fault and not scans and len(lines) == 7)):
        raise ValueError('ECAM arm/scan/terminal ordering')
    if not firmware_matches(metadata, files):
        raise ValueError('ECAM arm disagrees with captured firmware')
    del lines[5]
    return b''.join(lines), {'schema': 'leanos-ecam-capture-v1', 'armed': True,
        'firmware_matches': True, 'transaction_fault': fault, 'platform_admitted': False}
