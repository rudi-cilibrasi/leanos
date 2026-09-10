#!/usr/bin/env python3
"""Emit identical complete snapshots and explicit expected errors for Lean/C."""
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/qotom-quarantine-observation'


def main():
    spec = importlib.util.spec_from_file_location('capture', ROOT / 'scripts/test-pci-header-capture.py')
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    capture.replay_source()  # validates all hashes and selector projections
    functions = json.loads((capture.CAPTURE / 'inventory.json').read_text())['functions']
    words = []
    for i in (12, 13, 14, 0, 1, 2, 3, 4, 5, 10, 11, 6, 7, 8, 9):
        f = functions[i]
        _, bus, device, fn = map(int, f['selector'].removeprefix('pci').split(':'))
        raw = f['words'].copy()
        raw[1] &= 0xffff0000  # Synthetic command clear, not observed hardware state.
        words += [bus, device, fn, 4, 2, 0, bus, device, fn] + raw
    cases = [('synthetic-cleared', 15, words, 1)]

    def change(name, index, value, result):
        altered = words.copy()
        altered[index] = value
        cases.append((name, 15, altered, result))

    for count in (0, 14, 16, 2**64 - 1):
        cases.append((f'count-{count}', count, words, 0x10000))
    for size in (0, 374, 376):
        cases.append((f'size-{size}', 15, (words + [0])[:size], 0x10001))
    for i in range(15):
        for offset, value in ((3, 5), (4, 4), (5, 4)):
            change(f'write-{i}-{offset}', i*25+offset, value, 0x20000+i)
        change(f'target-{i}', i*25, 5, 0x30000+i)
        change(f'identity-{i}', i*25+9, 0x12348086, 0x50000+i)
        change(f'command-{i}', i*25+10, words[i*25+10] | 4, 0x60000+i)
        change(f'absent-{i}', i*25+9, 0xffffffff, 0x40300+i)
        change(f'non-dword-{i}', i*25+24, 2**32, 0x40200+i)
    for i in range(11, 15):
        change(f'bridge-{i}', i*25+15, 0, 0x50000+i)
    cases.append(('duplicate', 15, words[:14*25] + words[13*25:14*25], 0x5000e))
    cases.append(('reorder', 15, words[25:50] + words[:25] + words[50:], 0x50000))
    lean = ['import LeanOS.QotomPCIQuarantineObservation', 'open LeanOS.QotomPCIQuarantineObservation']
    c = ['static const struct { const char *name; uint64_t count; size_t size;',
         'uint64_t words[376]; uint64_t expected; } inventory_cases[] = {']
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
    print(f'Qotom command/readback ABI goldens passed ({len(cases)} cases)')


if __name__ == '__main__':
    main()
