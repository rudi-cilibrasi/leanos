#!/usr/bin/env python3
"""Check bounded CLI transport into generated Qotom inventory admission."""
import argparse
import json
from pathlib import Path
import runpy
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--replay', type=Path, required=True)
    executable = parser.parse_args().replay.resolve()
    runpy.run_path(str(ROOT / 'scripts/test-pci-header-capture.py'))['replay_source']()
    capture = json.loads((ROOT / 'hardware/lab/observations/qotom-pci-20260910/inventory.json').read_text())
    words = []
    for function in capture['functions']:
        domain, bus, device, slot = map(int, function['selector'].removeprefix('pci').split(':'))
        assert domain == 0
        words += [bus, device, slot, *function['words']]
    arguments = ['inventory', str(len(capture['functions'])), *map(str, words)]
    cases = 0

    def check(args, code, output=None):
        nonlocal cases
        result = subprocess.run([str(executable), *args], capture_output=True, timeout=15)
        assert result.returncode == code, (args[:3], result.returncode, result.stderr)
        if output is not None:
            assert result.stdout == output, result.stdout
        cases += 1

    check(arguments, 0, b'1\n')
    check(['inventory', '0'], 0, b'65536\n')
    # Preserve the input BDFs; mutate the host bridge identity to q35.
    changed = arguments.copy()
    changed[5] = str(0x29c08086)
    check(changed, 0, b'262144\n')
    for args in [['inventory'], ['wrong', '0'], ['inventory', '17'],
                 arguments[:-1], arguments + ['0']]:
        check(args, 2, b'')
    for bad in ['', '00', '+1', '-1', ' 1', '1 ', '0x1', '1x', str(1 << 64)]:
        for index in [1, 2, len(arguments) - 1]:
            malformed = arguments.copy()
            malformed[index] = bad
            check(malformed, 2, b'')
    print(f'Qotom PCI replay CLI passed ({cases} cases)')


if __name__ == '__main__':
    main()
