#!/usr/bin/env python3
"""Match every retained native row, with every field and position mutated."""
import ctypes
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
capture = root / 'hardware/lab/observations/qotom-ecam-20260911'
manifest = json.loads((capture / 'manifest.json').read_text())
name = 'cycle-1/reclassified-result.json'
raw = (capture / name).read_bytes()
if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
    raise SystemExit('native capture hash mismatch')
headers = json.loads(raw)['diagnostic']['pci_headers']
if len(headers) != 16:
    raise SystemExit('native inventory length changed')
lib = ctypes.CDLL(str(Path(sys.argv[1]).resolve()))
expected = lib.lp_leanos_LeanOS_QotomNativePCIFields_expected
expected.argtypes = [ctypes.c_uint64] * 2
expected.restype = ctypes.c_uint64
matches = lib.lp_leanos_LeanOS_QotomNativePCIFields_matchesFields
matches.argtypes = [ctypes.c_uint64] * 13
matches.restype = ctypes.c_uint8
check_header = lib.lp_leanos_LeanOS_QotomNativePCIFields_checkHeader
check_header.argtypes = [ctypes.c_uint64] * 20
check_header.restype = ctypes.c_uint8
cases = 0
for index, header in enumerate(headers):
    assert check_header(index, *header) == 1
    cases += 1
    for word in range(16):
        bad_header = header.copy()
        bad_header[3 + word] = 1 << 32
        assert check_header(index, *bad_header) == 0, (index, word)
        cases += 1
    for other in (*range(16), 16, (1 << 64) - 1):
        if other != index:
            assert check_header(other, *header) == 0, (index, other)
            cases += 1
    bdf, words = header[:3], header[3:]
    layout = (words[3] >> 16) & 0x7f
    row = bdf + [words[0] & 0xffff, words[0] >> 16, words[2] >> 8,
                 int(bool(words[3] & 0x800000)), layout]
    row += [words[6] & 0xff, (words[6] >> 8) & 0xff,
            (words[6] >> 16) & 0xff, words[15] >> 16] if layout == 1 else [0] * 4
    assert [expected(index, f) for f in range(12)] == row
    assert matches(index, *row) == 1
    cases += 1
    for field in range(12):
        for value in (row[field] ^ 1, 1 << 32, (1 << 64) - 1):
            bad = row.copy()
            bad[field] = value
            assert matches(index, *bad) == 0, (index, field, value)
            cases += 1
    for other in (*range(16), 16, (1 << 64) - 1):
        if other != index:
            assert matches(other, *row) == 0, (index, other)
            cases += 1
    for field in (12, 20, (1 << 64) - 1):
        assert expected(index, field) == 0x70001
        cases += 1
for index in (16, (1 << 64) - 1):
    for field in (0, 11, 12, (1 << 64) - 1):
        assert expected(index, field) == 0x70000
        cases += 1
print(f'PASS native scalar inventory: {cases} cases, no Lean runtime')
