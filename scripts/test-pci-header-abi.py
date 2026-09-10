#!/usr/bin/env python3
"""Generate shared typed/hosted scalar PCI observation cases."""
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/pci-header-capture'
spec = importlib.util.spec_from_file_location('pci_capture_replay', ROOT / 'scripts/test-pci-header-capture.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


def main():
    replay.replay_source()  # Validate the retained capture before deriving cases.
    inventory = json.loads((replay.CAPTURE / 'inventory.json').read_text())
    cases = []
    for f in inventory['functions']:
        _, bus, device, fn = map(int, f['selector'].removeprefix('pci').split(':'))
        w = f['words']
        expected = [1, f['vendor'], f['device'], f['class_code'], f['command'],
                    f['status'], f['revision'], int(f['multifunction']), int('bridge' in f)]
        if 'bridge' in f:
            b = f['bridge']
            expected += [b['primary'], b['secondary'], b['subordinate'], b['control'],
                         w[7] & 0xffff, w[7] >> 16, w[8], w[9], w[10], w[11], w[12]]
        else:
            expected += [0] * 11
        cases.append(([16, bus, device, fn, *w], expected))
    # Distinct field sentinels have independent literal expected values.
    cases.append(([16, 0, 28, 0, 0x0f488086, 0x00100407, 0x0604000e, 0x00810000,
                   0, 0, 0x99030201, 0xabcd1234, 0x23456789, 0x3456789a,
                   0x456789ab, 0x56789abc, 0x6789abcd, 0, 0, 0xbeef0102],
                  [1, 0x8086, 0x0f48, 0x060400, 0x407, 0x10, 14, 1, 1,
                   1, 2, 3, 0xbeef, 0x1234, 0xabcd, 0x23456789, 0x3456789a,
                   0x456789ab, 0x56789abc, 0x6789abcd]))
    for index, value, error in [(1, 256, 0x100), (2, 32, 0x100), (3, 8, 0x100),
                                (0, 0, 0x101), (0, 15, 0x101), (0, 17, 0x101),
                                (4, 0x100000000, 0x102), (19, 0x100000000, 0x102),
                                (4, 0xffffffff, 0x103), (7, 0x20000, 0x104)]:
        words = list(cases[0][0])
        words[index] = value
        cases.append((words, [error] * 20))
    OUT.mkdir(parents=True, exist_ok=True)
    lean = ['import LeanOS.PCIHeaderObservation', 'open LeanOS.PCIHeaderObservation']
    c = ['/* Generated scalar observations: 20 inputs and 20 expected outputs. */',
         'static const uint64_t pci_header_cases[][40] = {']
    for words, expected in cases:
        assert len(words) == len(expected) == 20
        arguments = ' '.join(str(x) for x in words)
        lean.append('example : ((List.range 20).map (fun field => checkRaw field.toUInt64 '
                    + arguments + ')) == [' + ', '.join(map(str, expected))
                    + '] := by native_decide')
        for field in (20, 0xffffffffffffffff):
            lean.append(f'example : checkRaw {field} {arguments} = 0x105 := by native_decide')
        c.append('  {' + ', '.join(f'UINT64_C({x})' for x in words + expected) + '},')
    c.append('};')
    (OUT / 'ABI.lean').write_text('\n'.join(lean) + '\n')
    (OUT / 'cases.h').write_text('\n'.join(c) + '\n')
    subprocess.run(['lake', 'env', 'lean', str(OUT / 'ABI.lean')], cwd=ROOT, check=True)
    print(f'PCI scalar ABI Lean checks passed ({len(cases)} cases, 22 fields each)')


if __name__ == '__main__':
    main()
