#!/usr/bin/env python3
"""Replay the hash-bound native ECAM headers through the distinct inventory model."""
import hashlib
import json
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parents[1]


def main():
    capture = ROOT / 'hardware/lab/observations/qotom-ecam-20260911'
    manifest = json.loads((capture / 'manifest.json').read_text())
    name = 'cycle-1/reclassified-result.json'
    raw = (capture / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
        raise ValueError('native ECAM result hash mismatch')
    headers = json.loads(raw)['diagnostic']['pci_headers']
    lines = ['import LeanOS.QotomNativePCIInventory', 'set_option maxRecDepth 100000',
             'set_option maxHeartbeats 0', 'open LeanOS.PCIHeaderObservation LeanOS.QotomNativePCIInventory']
    for i, h in enumerate(headers):
        lines.append(f'def raw{i} : RawHeader := ⟨⟨{h[0]}, {h[1]}, {h[2]}⟩, [' +
                     ','.join(hex(x) for x in h[3:]) + ']⟩')
    lines.append('def captured : List RawHeader := [' + ','.join(f'raw{i}' for i in range(len(headers))) + ']')
    lines.append('example : (match check captured with | .ok w => w.headers.map (·.raw) == captured | .error _ => false) = true := by decide')
    def rejects(expr, error):
        lines.append(f'example : (match check ({expr}) with | .error e => e == {error} | .ok _ => false) = true := by decide')
    rejects('captured.take 10 ++ captured.drop 11', '.count')
    rejects('captured ++ [raw0]', '.count')
    rejects('captured.set 0 raw1 |>.set 1 raw0', '.address 0')
    for i in range(16):
        rejects(f'captured.set {i} ⟨raw{i}.bdf, raw{i}.words.set 0 0x12348086⟩', f'.identity {i}')
        rejects(f'captured.set {i} ⟨⟨255, 31, 7⟩, raw{i}.words⟩', f'.address {i}')
    rejects('captured.set 10 ⟨raw10.bdf, raw10.words.set 3 0x00800000⟩', '.multifunction 10')
    for i in range(6, 10):
        rejects(f'captured.set {i} ⟨raw{i}.bdf, raw{i}.words.set 15 0⟩', f'.routing {i}')
    lines.append('example : (match LeanOS.QotomPCIInventory.check captured with | .error e => e == .count | .ok _ => false) = true := by decide')
    flat = [word for header in headers for word in header]
    cases = [('native', 16, flat, 1), ('old-count', 15, flat, 0x10000),
             ('short-array', 16, flat[:-1], 0x10001), ('long-array', 16, flat + [0], 0x10001)]
    for i in range(16):
        changed = flat.copy(); changed[i * 19 + 3] = 0x12348086
        cases.append((f'identity-{i}', 16, changed, 0x40000 + i))
        changed = flat.copy(); changed[i * 19:i * 19 + 3] = [255, 31, 7]
        cases.append((f'address-{i}', 16, changed, 0x30000 + i))
    c = ['#include <stdint.h>', 'static const struct { const char *name; uint64_t count; unsigned size; uint64_t expected; uint64_t words[305]; } native_cases[] = {']
    for name, count, words, expected in cases:
        values = ','.join(str(w) for w in words)
        lines.append(f'example : checkWords {count} #[{values}] = {expected} := by decide')
        c.append(f'{{"{name}",{count},{len(words)},{expected},{{{values}}}}},')
    c.append('};')
    case_header = ROOT / 'build/native-inventory/cases.h'
    case_header.parent.mkdir(parents=True, exist_ok=True)
    case_header.write_text('\n'.join(c) + '\n')
    output = ROOT / 'build/native-inventory/replay.lean'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('\n'.join(lines) + '\n')
    subprocess.run(['lean', str(output)], cwd=ROOT, check=True)
    print('Native inventory: raw preservation, 41 rejections and 36 array ABI cases PASS')


if __name__ == '__main__': main()
