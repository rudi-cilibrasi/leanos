#!/usr/bin/env python3
"""Replay retained native headers and reject malformed decimal CLI transport."""
import argparse
import json
import hashlib
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--replay', type=Path, required=True)
    executable = p.parse_args().replay.resolve()
    capture = ROOT / 'hardware/lab/observations/qotom-ecam-20260911/cycle-1/reclassified-result.json'
    raw = capture.read_bytes()
    manifest = json.loads((capture.parent.parent / 'manifest.json').read_text())
    if hashlib.sha256(raw).hexdigest() != manifest['files']['cycle-1/reclassified-result.json']:
        raise ValueError('native capture hash mismatch')
    headers = json.loads(raw)['diagnostic']['pci_headers']
    words = [str(w) for h in headers for w in h]
    def run(args, code, output=b''):
        result = subprocess.run([str(executable), *args], capture_output=True, timeout=30)
        if result.returncode != code or result.stdout != output:
            raise AssertionError((args[:3], result.returncode, result.stdout, result.stderr))
    run(['inventory', '16', *words], 0, b'1\n')
    run(['inventory', '0'], 0, b'65536\n')
    run(['inventory', '15', *words[:190], *words[209:]], 0, b'65536\n')
    for bad in ['', '-1', '+16', '016', '17', '18446744073709551616', '1x']:
        run(['inventory', bad, *words], 2)
    for bad in ['', '-1', '+1', '01', '18446744073709551616', '0x1']:
        run(['inventory', '16', bad, *words[1:]], 2)
    run(['inventory', '16', *words[:-1]], 2)
    run(['inventory', '16', *words, '0'], 2)
    run(['wrong-mode', '16', *words], 2)
    for i in range(16):
        changed = words.copy(); changed[i * 19 + 3] = str(0x12348086)
        run(['inventory', '16', *changed], 0, f'{0x40000+i}\n'.encode())
        changed = words.copy(); changed[i * 19 + 18] = str(1 << 32)
        run(['inventory', '16', *changed], 0, f'{0x20200+i}\n'.encode())
    print('Native inventory CLI: retained capture, historical count, 16 identities, 16 non-dword values and malformed transport PASS')


if __name__ == '__main__': main()
