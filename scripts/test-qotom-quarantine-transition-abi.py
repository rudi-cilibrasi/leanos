#!/usr/bin/env python3
"""Emit identical complete snapshots and explicit expected errors for Lean/C."""
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/qotom-quarantine-transition'


def main():
    spec = importlib.util.spec_from_file_location('capture', ROOT / 'scripts/test-pci-header-capture.py')
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    capture.replay_source()  # validates all hashes and selector projections
    functions = json.loads((capture.CAPTURE / 'inventory.json').read_text())['functions']
    initial = []
    for f in functions:
        _, bus, device, fn = map(int, f['selector'].removeprefix('pci').split(':'))
        initial += [bus, device, fn] + f['words']
    order = [12, 13, 14, 0, 1, 2, 3, 4, 5, 10, 11, 6, 7, 8, 9]
    trace = []
    for i in order:
        f = functions[i]
        _, bus, device, fn = map(int, f['selector'].removeprefix('pci').split(':'))
        raw = f['words'].copy()
        raw[1] &= 0xffff0000
        trace += [bus, device, fn, 4, 2, 0, bus, device, fn] + raw
    words = initial + trace
    cases = [('synthetic-transition', 15, words, 1)]

    def change(name, index, value, result):
        altered = words.copy()
        altered[index] = value
        cases.append((name, 15, altered, result))

    for count in (0, 14, 16, 2**64 - 1):
        cases.append((f'count-{count}', count, words, 0x10000))
    for size in (0, 659, 661):
        cases.append((f'size-{size}', 15, (words + [0])[:size], 0x10001))
    for i, before_index in enumerate(order):
        base = 285 + i*25
        change(f'initial-identity-{i}', before_index*19+3, 0x12348086, 0x140000+before_index)
        change(f'write-{i}', base+4, 4, 0x220000+i)
        change(f'target-{i}', base, 5, 0x230000+i)
        change(f'trace-identity-{i}', base+9, 0x12348086, 0x250000+i)
        change(f'command-{i}', base+10, words[base+10] | 4, 0x260000+i)
        change(f'after-register-{i}', base+17, words[base+17] ^ 1, 0x300000+i)
        change(f'before-register-{i}', before_index*19+11, words[before_index*19+11] ^ 1, 0x300000+i)
        change(f'initial-non-dword-{i}', before_index*19+18, 2**32, 0x120200+before_index)
        change(f'trace-non-dword-{i}', base+24, 2**32, 0x240200+i)
    change('status-may-change', 285+10, words[285+10] ^ 0x10000, 1)
    both = words.copy()
    both[12*19+11] ^= 1
    both[285+17] ^= 1
    cases.append(('same-register-in-both-observations', 15, both, 1))
    lean = ['import LeanOS.QotomPCIQuarantineTransition', 'open LeanOS.QotomPCIQuarantineTransition']
    c = ['static const struct { const char *name; uint64_t count; size_t size;',
         'uint64_t words[661]; uint64_t expected; } inventory_cases[] = {']
    for name, count, data, expected in cases:
        values = ', '.join(map(str, data))
        lean.append(f'example : checkWords {count} #[{values}] = {expected} := by native_decide')
        c.append(f'{{"{name}", UINT64_C({count}), {len(data)}, '
                 '{' + ', '.join(f'UINT64_C({w})' for w in data) + f'}}, {expected}}},')
    c.append('};')
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'ABI.lean').write_text('\n'.join(lean)+'\n')
    (OUT / 'cases.h').write_text('\n'.join(c)+'\n')
    subprocess.run(['lake', 'env', 'lean', str(OUT / 'ABI.lean')], cwd=ROOT, check=True)
    print(f'Qotom combined transition ABI goldens passed ({len(cases)} cases)')


if __name__ == '__main__':
    main()
