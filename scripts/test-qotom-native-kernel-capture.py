#!/usr/bin/env python3
"""Synthetic kernel-result framing over retained physical PCI headers."""
from pathlib import Path
import json
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
C = ROOT / 'hardware/lab/observations/qotom-ecam-20260911'
PROTOCOL = D['load_protocol'](C / 'diagnostic-protocol.tsv')
BASE = (C / 'cycle-1/diagnostic.raw').read_text().splitlines()
CPU = ROOT / 'build/j1900-cpu-host/host'
PCI = ROOT / 'build/qotom-native-inventory-host/host'
PREFIX = 'LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 '


def frame(lines=BASE, status=0, index=0, count=16):
    result = lines.copy()
    result.insert(-1, PREFIX + f'status={status} index={index} count={count}')
    if status:
        result[-1] = PROTOCOL['FINAL'] + ' status=FAIL reason=qotom-native-inventory'
    return ('\n'.join(result) + '\n').encode()


def replay(raw, **kwargs):
    return D['classify'](raw, PROTOCOL, CPU, PCI, native_inventory=True,
                         native_kernel=True, **kwargs)


class KernelCapture(unittest.TestCase):
    def test_match_and_explicit_selection(self):
        result = replay(frame())
        self.assertEqual(result['native_kernel_inventory'], {'status': 0, 'index': 0, 'count': 16})
        self.assertFalse(result['platform_admitted'] or result['cpl3_authorized'])
        with self.assertRaises(ValueError):
            D['classify'](frame(), PROTOCOL, CPU, PCI, native_inventory=True)
        with self.assertRaises(ValueError):
            D['classify'](frame(), PROTOCOL, CPU, PCI, native_kernel=True)

    def test_missing_duplicate_and_mismatch(self):
        with self.assertRaises(ValueError):
            replay(('\n'.join(BASE) + '\n').encode())
        for raw in (frame(status=4, index=15), frame(index=1), frame(count=15),
                    frame().replace(b'status=0 index=0', b'status=1 index=0'),
                    frame().replace(b'index=0', b'index=00'),
                    frame().replace((PREFIX + 'status=0 index=0 count=16\n').encode(),
                                    ((PREFIX + 'status=0 index=0 count=16\n') * 2).encode())):
            with self.assertRaises(ValueError):
                replay(raw)

    def test_last_identity_rejection(self):
        lines = BASE.copy()
        row = next(i for i, line in enumerate(lines) if 'PCI-HEADER codec=1 index=15 ' in line)
        prefix, payload = lines[row].split('words=')
        words = list(map(int, payload.split(',')))
        words[3] ^= 1
        lines[row] = prefix + 'words=' + ','.join(map(str, words))
        result = replay(frame(lines, status=4, index=15))
        self.assertEqual(result['inventory_result'], 0x4000f)
        self.assertEqual(result['terminal_reason'], 'qotom-native-inventory')
        with self.assertRaises(ValueError):
            replay(frame(lines))

    def test_missing_function_count_rejection(self):
        lines = [s for s in BASE if 'PCI-HEADER codec=1 index=15 ' not in s]
        lines = [s.replace('count=16', 'count=15') if 'PCI-SCAN ' in s else s for s in lines]
        result = replay(frame(lines, status=3, count=15))
        self.assertEqual(result['inventory_result'], 0x10000)
        with self.assertRaises(ValueError):
            replay(frame(lines, status=4, count=15))

    def test_protected_kernel_record(self):
        runner = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        events = [json.loads(line) for line in (C / 'cycle-1/events.jsonl').read_text().splitlines()]
        old = json.loads((C / 'cycle-1/reclassified-result.json').read_text())
        data = b''.join(bytes.fromhex(e['hex']) for e in events)
        terminal = (PROTOCOL['FINAL'] + ' status=FAIL reason=qotom-platform-pending').encode()
        position = data.index(terminal)
        offset = 0
        for event in events:
            chunk = bytes.fromhex(event['hex'])
            if offset <= position < offset + len(chunk):
                local = position - offset
                inserted = (PREFIX + 'status=0 index=0 count=16\n').encode()
                event['hex'] = (chunk[:local] + inserted + chunk[local:]).hex()
                break
            offset += len(chunk)
        else:
            self.fail('terminal not in events')
        opts = dict(handoff=True, acpi=True, bootstrap=True, ecam_memory=True,
                    dsdt=True, ecam_read=True, native_inventory=True, native_kernel=True)
        result = runner['classify_cpu_protected'](events, old['elf_sha256'],
            C / 'diagnostic-protocol.tsv', CPU, PCI, **opts)
        self.assertTrue(result['watchdog_protected'])
        self.assertTrue(result['diagnostic']['native_kernel_inventory_enabled'])
        self.assertEqual(result['diagnostic']['native_kernel_inventory']['status'], 0)
        opts['native_inventory'] = False
        with self.assertRaises(ValueError):
            runner['classify_cpu_protected'](events, old['elf_sha256'],
                C / 'diagnostic-protocol.tsv', CPU, PCI, **opts)

    def test_incomplete_scan_cannot_report_inventory(self):
        lines = BASE[:3] + [PROTOCOL['PCI-SCAN'] +
            ' codec=1 status=1 count=0 bus=255 device=31 function=7 offset=0',
            PROTOCOL['FINAL'] + ' status=FAIL reason=qotom-pci-enumeration']
        result = replay(('\n'.join(lines) + '\n').encode())
        self.assertIsNone(result['native_kernel_inventory'])
        with self.assertRaises(ValueError):
            replay(frame(lines))


if __name__ == '__main__':
    unittest.main()
