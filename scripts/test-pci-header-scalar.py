#!/usr/bin/env python3
"""Execute the retained scalar object, checking status and rejection precedence."""
import ctypes
import random
import sys
from pathlib import Path

lib = ctypes.CDLL(str(Path(sys.argv[1]).resolve()))
status = lib.l_LeanOS_PCIHeaderObservation_Scalar_status
status.argtypes = [ctypes.c_uint64] * 20
status.restype = ctypes.c_uint64


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
                cases += 1
print(f'PASS scalar PCI header status: {cases} cases, no Lean runtime')
