#!/usr/bin/env python3
"""Explicit native replay of retained ECAM evidence; never platform admission."""
import json
from pathlib import Path
import runpy
import unittest
ROOT = Path(__file__).resolve().parents[1]
C = ROOT / 'hardware/lab/observations/qotom-ecam-20260911'
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
R = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
P = D['load_protocol'](C / 'diagnostic-protocol.tsv')
CPU = ROOT / 'build/j1900-cpu-host/host'
NATIVE = ROOT / 'build/qotom-native-inventory-host/host'
OLD = ROOT / 'build/qotom-pci-inventory-host/host'
RAW = (C / 'cycle-1/diagnostic.raw').read_bytes()


class Capture(unittest.TestCase):
    def test_explicit_profile(self):
        result = D['classify'](RAW, P, CPU, NATIVE, native_inventory=True)
        self.assertEqual(result['inventory_result'], 1)
        self.assertEqual(result['inventory_profile'], 'qotom-native-ecam-v1')
        self.assertFalse(result['platform_admitted'] or result['cpl3_authorized'])
        self.assertEqual(D['classify'](RAW, P, CPU, OLD)['inventory_result'], 65536)
        with self.assertRaises(ValueError): D['classify'](RAW, P, CPU, OLD, native_inventory=True)
        with self.assertRaises(ValueError): D['classify'](RAW, P, CPU, NATIVE)

    def test_last_index(self):
        lines = RAW.splitlines()
        index = next(i for i, s in enumerate(lines) if b'PCI-HEADER codec=1 index=15 ' in s)
        prefix, words = lines[index].split(b' words=')
        fields = words.split(b','); fields[3] = str(0x12348086).encode()
        lines[index] = prefix + b' words=' + b','.join(fields)
        result = D['classify'](b'\n'.join(lines)+b'\n', P, CPU, NATIVE, native_inventory=True)
        self.assertEqual(result['inventory_result'], 0x4000f)

    def test_protected(self):
        events = [json.loads(s) for s in (C / 'cycle-1/events.jsonl').read_text().splitlines()]
        old = json.loads((C / 'cycle-1/reclassified-result.json').read_text())
        opts = dict(handoff=True, acpi=True, bootstrap=True, ecam_memory=True,
                    dsdt=True, ecam_read=True, native_inventory=True)
        result = R['classify_cpu_protected'](events, old['elf_sha256'],
            C / 'diagnostic-protocol.tsv', CPU, NATIVE, **opts)
        self.assertTrue(result['ecam']['armed'] and result['watchdog_protected'])
        self.assertEqual(result['diagnostic']['inventory_result'], 1)
        self.assertFalse(result['diagnostic']['platform_admitted'])
        opts['ecam_read'] = False
        with self.assertRaises(ValueError):
            R['classify_cpu_protected'](events, old['elf_sha256'], C / 'diagnostic-protocol.tsv', CPU, NATIVE, **opts)


if __name__ == '__main__': unittest.main()
