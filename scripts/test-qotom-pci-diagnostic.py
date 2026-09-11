#!/usr/bin/env python3
"""Exercise native model replay and malformed PCI boot capture boundaries."""
import argparse
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('diagnostic', ROOT / 'scripts/check-qotom-pci-diagnostic.py')
D = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(D)
parser = argparse.ArgumentParser()
parser.add_argument('--cpu-replay', type=Path, default=ROOT / 'build/j1900-cpu-host/host')
parser.add_argument('--pci-replay', type=Path, default=ROOT / 'build/qotom-pci-inventory-host/host')
args, remaining = parser.parse_known_args()
P = D.load_protocol(ROOT / 'build/boundary-abi/serial-protocol.tsv')
rows = (ROOT / 'hardware/cpu-corpus/qotom-j1900-20260909/cpu-0.tsv').read_text().splitlines()[1:]
CPU = [1, 31] + [int(word, 16) for row in rows for word in row.split('\t')[2:]]
INVENTORY = json.loads((ROOT / 'hardware/lab/observations/qotom-pci-20260910/inventory.json').read_text())
HEADERS = [list(map(int, f['selector'].removeprefix('pci').split(':')))[1:] + f['words']
           for f in INVENTORY['functions']]


def capture(headers=None, status=0, location=(0, 0, 0, 0), cpu=None, selected=65536, readback=1):
    headers = HEADERS if headers is None else headers
    cpu = CPU if cpu is None else cpu
    lines = [P['BOOT'] + ' target=qotom-j1900-candidate phase=pci-inventory-diagnostic platform-admitted=0 cpl3=0',
             P['CPU'] + ' profile=j1900-cpu-v1 codec=1 width=22 words=' + ','.join(map(str, cpu)) + ' selection=' + str(selected)]
    reason = 'j1900-cpu-profile'
    if selected == 65536:
        msrs = [0xd00] + [0] * 7
        if not readback:
            msrs[1] = 1 << 63
        lines.append(P['CONTROL'] + ' profile=j1900-cpu-v1 codec=1 width=8 words=' + ','.join(map(str, msrs)) + ' readback=' + str(readback))
        reason = 'j1900-msr-readback'
        if readback:
            lines.append(P['PCI-SCAN'] + f' codec=1 status={status} count={len(headers)}' + ''.join(
                f' {name}={word}' for name, word in zip(('bus', 'device', 'function', 'offset'), location)))
            for index, words in enumerate(headers):
                lines.append(P['PCI-HEADER'] + f' codec=1 index={index} width=19 words=' + ','.join(map(str, words)))
            reason = 'qotom-pci-enumeration' if status else 'qotom-platform-pending'
    return ('\n'.join(lines + [P['FINAL'] + ' status=FAIL reason=' + reason]) + '\n').encode()


class CaptureTests(unittest.TestCase):
    def classify(self, raw):
        return D.classify(raw, P, args.cpu_replay.resolve(), args.pci_replay.resolve())

    def test_inventory_results_are_not_admission(self):
        changed = [h.copy() for h in HEADERS]
        changed[0][3] = 0x29c08086
        for headers, expected in ((HEADERS, 1), ([], 65536), (changed, 262144)):
            with self.subTest(expected=expected):
                result = self.classify(capture(headers))
                self.assertEqual(result['inventory_result'], expected)
                self.assertEqual(result['pci_headers'], headers)
                self.assertFalse(result['platform_admitted'])
                self.assertFalse(result['cpl3_authorized'])

    def test_failed_scan_does_not_publish_partial_snapshot(self):
        for status, location in ((1, (255, 31, 7, 60)), (2, (3, 0, 0, 0)), (3, (0, 0, 0, 0))):
            result = self.classify(capture([], status, location))
            self.assertEqual(result['terminal_reason'], 'qotom-pci-enumeration')
            self.assertIsNone(result['inventory_result'])
            with self.assertRaises(D.DiagnosticError):
                self.classify(capture(HEADERS, status, location))

    def test_cpu_and_msr_stop_before_pci(self):
        cpu = CPU.copy()
        cpu[6] ^= 1
        for raw, reason in ((capture(cpu=cpu, selected=6), 'j1900-cpu-profile'),
                            (capture(readback=0), 'j1900-msr-readback')):
            self.assertEqual(self.classify(raw)['terminal_reason'], reason)
            lines = raw.splitlines()
            lines.insert(-1, capture().splitlines()[3])
            with self.assertRaises(D.DiagnosticError):
                self.classify(b'\n'.join(lines) + b'\n')
        for raw in (capture(cpu=cpu), capture().replace(b'readback=1', b'readback=0')):
            with self.assertRaises(D.DiagnosticError):
                self.classify(raw)

    def test_transport_and_record_mutations(self):
        raw = capture()
        lines = raw.splitlines(keepends=True)
        mutations = [b'', raw[:-1], raw + b'\n', raw + b'\0', b'x' * 16385,
                     raw.replace(b'\n', b'\r\n'), b''.join(lines[:-1]),
                     b''.join(lines[:3] + lines[4:]),
                     b''.join(lines[:4] + [lines[5], lines[4]] + lines[6:])]
        for before, after in [(b'count=15', b'count=16'), (b'count=15', b'count=17'),
                              (b'count=15', b'count=015'), (b'index=1 ', b'index=0 '),
                              (b'width=19', b'width=18'), (b'status=0', b'status=4'),
                              (b'offset=0', b'offset=4'), (b'platform-admitted=0', b'platform-admitted=1'),
                              (b'cpl3=0', b'cpl3=1'), (b'status=FAIL', b'status=PASS'),
                              (P['PCI-HEADER'].encode(), P['CPU'].encode())]:
            mutations.append(raw.replace(before, after))
        for malformed in mutations:
            with self.subTest(raw=malformed[:80]), self.assertRaises(D.DiagnosticError):
                self.classify(malformed)

    def test_header_bounds_order_and_absent_functions(self):
        for index, word in ((0, 256), (1, 32), (2, 8), (3, 1 << 32), (3, 0xffffffff)):
            headers = [h.copy() for h in HEADERS]
            headers[0][index] = word
            with self.assertRaises(D.DiagnosticError):
                self.classify(capture(headers))
        for headers in (HEADERS[::-1], [HEADERS[0], HEADERS[0]]):
            with self.assertRaises(D.DiagnosticError):
                self.classify(capture(headers))

    def test_protocol_requires_unique_complete_identities(self):
        source = (ROOT / 'build/boundary-abi/serial-protocol.tsv').read_text()
        row = next(line for line in source.splitlines() if line.startswith('record\t25\tPCI-SCAN\t'))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'protocol.tsv'
            for text in (source + row + '\n', source.replace(row + '\n', '')):
                path.write_text(text)
                with self.assertRaises(D.DiagnosticError):
                    D.load_protocol(path)


if __name__ == '__main__':
    unittest.main(argv=[__file__, *remaining])
