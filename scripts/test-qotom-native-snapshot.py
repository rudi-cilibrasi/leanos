#!/usr/bin/env python3
"""Exercise the immutable complete-snapshot loop and actual collector together."""
import ctypes as C
import hashlib
import json
from pathlib import Path
import sys


class Header(C.Structure):
    _fields_ = [('bus', C.c_uint8), ('device', C.c_uint8), ('function', C.c_uint8),
                ('words', C.c_uint32 * 16)]


class Snapshot(C.Structure):
    _fields_ = [('count', C.c_uint32), ('headers', Header * 16)]


root = Path(__file__).resolve().parents[1]
capture = root / 'hardware/lab/observations/qotom-ecam-20260911'
manifest = json.loads((capture / 'manifest.json').read_text())
name = 'cycle-1/reclassified-result.json'
raw = (capture / name).read_bytes()
assert hashlib.sha256(raw).hexdigest() == manifest['files'][name]
headers = json.loads(raw)['diagnostic']['pci_headers']
assert len(headers) == 16
source = Snapshot()
source.count = 16
for i, h in enumerate(headers):
    source.headers[i] = Header(*h[:3], (C.c_uint32 * 16)(*h[3:]))
lib = C.CDLL(str(Path(sys.argv[1]).resolve()))
replay = lib.qotom_native_snapshot_replay
replay.argtypes = [C.c_uint32, C.POINTER(Snapshot)]
replay.restype = C.c_uint64
collect = lib.qotom_native_collect_replay
collect.argtypes = [C.POINTER(Snapshot), C.c_int]
collect.restype = C.c_uint64
cases = 0


def expect(snapshot, status, wanted):
    global cases
    before = bytes(snapshot) if snapshot is not None else None
    actual = replay(status, C.byref(snapshot) if snapshot is not None else None)
    assert actual == wanted, (status, actual, wanted)
    assert snapshot is None or bytes(snapshot) == before
    cases += 1


expect(source, 0, 0)
expect(None, 0, 1 << 32)
for status in (1, 2, 3, 0xffffffff):
    expect(source, status, 2 << 32)
for count in (*range(16), 17, 0xffffffff):
    changed = Snapshot.from_buffer_copy(source)
    changed.count = count
    expect(changed, 0, 3 << 32)
for index in range(16):
    for address in ('bus', 'device', 'function'):
        changed = Snapshot.from_buffer_copy(source)
        setattr(changed.headers[index], address, 255)
        expect(changed, 0, (4 << 32) | index)
    for word, xor in ((0, 1), (2, 1 << 8), (3, 1 << 23), (3, 2 << 16)):
        changed = Snapshot.from_buffer_copy(source)
        changed.headers[index].words[word] ^= xor
        expect(changed, 0, (4 << 32) | index)
    if 6 <= index < 10:
        for word, xor in ((6, 1), (6, 1 << 8), (6, 1 << 16), (15, 1 << 16)):
            changed = Snapshot.from_buffer_copy(source)
            changed.headers[index].words[word] ^= xor
            expect(changed, 0, (4 << 32) | index)
    if index:
        changed = Snapshot.from_buffer_copy(source)
        changed.headers[index] = source.headers[0]
        expect(changed, 0, (4 << 32) | index)
# Full enumeration must precede comparison; a late failure cannot publish success.
before = bytes(source)
assert collect(C.byref(source), 0) == 0
assert collect(C.byref(source), 1) == 2 << 32
assert bytes(source) == before
cases += 2
missing = Snapshot.from_buffer_copy(source)
missing.count = 15
assert collect(C.byref(missing), 0) == 3 << 32
cases += 1
print(f'PASS native complete snapshot: {cases} cases; source bytes unchanged')
