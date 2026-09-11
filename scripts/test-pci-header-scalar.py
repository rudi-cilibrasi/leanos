#!/usr/bin/env python3
"""Execute the retained scalar object, checking status and rejection precedence."""
import ctypes
import random
import sys
from pathlib import Path

lib = ctypes.CDLL(str(Path(sys.argv[1]).resolve()))
status = lib.lp_leanos_LeanOS_PCIHeaderObservation_Scalar_status
status.argtypes = [ctypes.c_uint64] * 20
status.restype = ctypes.c_uint64
query = lib.lp_leanos_LeanOS_PCIHeaderObservation_Scalar_query
query.argtypes = [ctypes.c_uint64] * 21
query.restype = ctypes.c_uint64


def expected(count, bus, device, fn, words):
    if bus >= 256 or device >= 32 or fn >= 8:
        return 0x100
    if count != 16:
        return 0x101
    if any(w >= 1 << 32 for w in words):
        return 0x102
    if words[0] & 0xffff == 0xffff:
        return 0x103
    return 1 if (words[3] >> 16) & 0x7f in (0, 1) else 0x104


def observation(field, prefix, words):
    if field >= 20:
        return 0x105
    result = expected(*prefix, words)
    if result != 1:
        return result
    layout = (words[3] >> 16) & 0x7f
    common = [1, words[0] & 0xffff, words[0] >> 16, words[2] >> 8,
              words[1] & 0xffff, words[1] >> 16, words[2] & 0xff,
              int(bool(words[3] & 0x800000)), layout]
    bridge = [words[6] & 0xff, (words[6] >> 8) & 0xff,
              (words[6] >> 16) & 0xff, words[15] >> 16,
              words[7] & 0xffff, words[7] >> 16, words[8], words[9],
              words[10], words[11], words[12]] if layout == 1 else [0] * 11
    return (common + bridge)[field]


rng = random.Random(330)
cases = 0
for layout in (0, 1, 2, 0x7f, 0x80, 0x81, 0xff):
    for _ in range(16):
        words = [rng.getrandbits(32) for _ in range(16)]
        words[3] = (words[3] & ~0xff0000) | (layout << 16)
        variants = [words, [(words[0] & ~0xffff) | 0xffff, *words[1:]]]
        for i in range(16):
            bad = words.copy()
            bad[i] = 1 << 32
            variants.append(bad)
        for raw in variants:
            for prefix in ((16, 255, 31, 7), (16, 256, 0, 0),
                           (16, 0, 32, 0), (16, 0, 0, 8),
                           (0, 0, 0, 0), (17, 0, 0, 0),
                           ((1 << 64) - 1, 256, 32, 8)):
                actual = status(*prefix, *raw)
                want = expected(*prefix, raw)
                if actual != want:
                    raise SystemExit(f'mismatch: {prefix} {raw}: {actual} != {want}')
                for field in (*range(21), (1 << 64) - 1):
                    actual_field = query(field, *prefix, *raw)
                    want_field = observation(field, prefix, raw)
                    if actual_field != want_field:
                        raise SystemExit(f'field {field}: {actual_field} != {want_field}')
                cases += 1
print(f'PASS scalar PCI header: {cases} status and {cases * 22} field cases, no Lean runtime')
