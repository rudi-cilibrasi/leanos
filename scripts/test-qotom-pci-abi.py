#!/usr/bin/env python3
"""Emit identical complete snapshots and explicit expected errors for Lean/C."""
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/qotom-pci-inventory'


def main():
    spec = importlib.util.spec_from_file_location('capture', ROOT / 'scripts/test-pci-header-capture.py')
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    capture.replay_source()  # validates all hashes and selector projections
    functions = json.loads((capture.CAPTURE / 'inventory.json').read_text())['functions']
    words = []
    for f in functions:
        _, bus, device, fn = map(int, f['selector'].removeprefix('pci').split(':'))
        words += [bus, device, fn] + f['words']
    cases = [('captured', 15, words, 1)]

    def change(name, index, value, result):
        altered = words.copy()
        altered[index] = value
        cases.append((name, 15, altered, result))

    for count in (0, 14, 16, 2**64 - 1):
        cases.append((f'count-{count}', count, words, 0x10000))
    for size in (0, 284, 286):
        cases.append((f'size-{size}', 15, (words + [0])[:size], 0x10001))
    for i in range(15):
        change(f'identity-{i}', i*19+3, 0x12348086, 0x40000+i)
        change(f'relocated-{i}', i*19, 5, 0x30000+i)
        change(f'absent-{i}', i*19+3, 0xffffffff, 0x20300+i)
        change(f'non-dword-{i}', i*19+18, 2**32, 0x20200+i)
    for i in range(6, 10):
        for mask in (1, 0x100, 0x10000):
            change(f'bridge-{i}-{mask}', i*19+9, words[i*19+9] ^ mask, 0x60000+i)
        change(f'bridge-control-{i}', i*19+18, 0, 0x60000+i)
    change('q35-mixture', 3, 0x29c08086, 0x40000)
    change('ide-mixture', 2*19+3, 0x0f218086, 0x40002)
    change('multifunction', 6*19+6, 0x10000, 0x50006)
    change('layout', 6*19+6, 0x800000, 0x60006)
    change('bad-bdf', 0, 256, 0x20000)
    change('unsupported-header', 6, 0x20000, 0x20400)
    change('command-is-observation', 6*19+4, 0xffff, 1)
    change('window-is-observation', 6*19+11, 0xffffffff, 1)
    cases.append(('duplicate', 15, words[:14*19] + words[13*19:14*19], 0x3000e))
    cases.append(('reorder', 15, words[19:38] + words[:19] + words[38:], 0x30000))
    lean = ['import LeanOS.QotomPCIInventory', 'open LeanOS.QotomPCIInventory']
    c = ['static const struct { const char *name; uint64_t count; size_t size;',
         'uint64_t words[286]; uint64_t expected; } inventory_cases[] = {']
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
    print(f'Qotom PCI complete-snapshot ABI goldens passed ({len(cases)} cases)')


if __name__ == '__main__':
    main()
