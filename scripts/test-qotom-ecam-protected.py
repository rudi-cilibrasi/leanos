#!/usr/bin/env python3
"""Synthetic ECAM envelopes built from retained native observations; no hardware claim."""
import json
import hashlib
from pathlib import Path
import re
import runpy
import unittest
ROOT = Path(__file__).resolve().parents[1]
R = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-ecam-capture.py'))
C = ROOT / 'hardware/lab/observations/qotom-dsdt-20260911'
P = R['cpu_replay_module'](True).load_protocol(C / 'diagnostic-protocol.tsv')
EVENTS = [json.loads(s) for s in (C / 'cycle-1/events.jsonl').read_text().splitlines()]
EXPECTED, _ = R['cpu_diagnostic_bytes'](EVENTS, P, True)
# Replace the mechanism-1 trace only in this explicitly synthetic fixture.
PAYLOAD, COUNT = re.subn(rb'LEANOS-LAB/1 PCI-READ [^\n]*\n', D['ARM'], EXPECTED)
assert COUNT == 1
DIGEST = 'a' * 64


def events(payload):
    prefix = (b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
              b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
              b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD sha256=' + DIGEST.encode() + b'\n')
    return [{'elapsed':1, 'hex':prefix.hex()}, {'elapsed':5, 'hex':payload.hex()},
            {'elapsed':40, 'hex':(b'LEANOS-LAB/1 DEFAULT request=none\n' + R['CHAIN']).hex()}]


def classify(payload, **changes):
    opts = dict(handoff=True, acpi=True, bootstrap=True, ecam_memory=True, dsdt=True, ecam_read=True)
    opts.update(changes)
    return R['classify_cpu_protected'](events(payload), DIGEST, C / 'diagnostic-protocol.tsv',
        ROOT / 'build/j1900-cpu-host/host', ROOT / 'build/qotom-pci-inventory-host/host', **opts)


class Protected(unittest.TestCase):
    def test_native_capture(self):
        directory = ROOT / 'hardware/lab/observations/qotom-ecam-20260911'
        manifest = json.loads((directory / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((directory / name).read_bytes()).hexdigest(), digest)
        cycle = directory / 'cycle-1'
        captured = [json.loads(s) for s in (cycle / 'events.jsonl').read_text().splitlines()]
        self.assertEqual(b''.join(bytes.fromhex(e['hex']) for e in captured), (cycle / 'serial.raw').read_bytes())
        recorded = json.loads((cycle / 'reclassified-result.json').read_text())
        result = R['classify_cpu_protected'](captured, recorded['elf_sha256'],
            directory / 'diagnostic-protocol.tsv', ROOT / 'build/j1900-cpu-host/host',
            ROOT / 'build/qotom-pci-inventory-host/host', handoff=True, acpi=True,
            bootstrap=True, ecam_memory=True, dsdt=True, ecam_read=True)
        for key in ['ecam', 'quiet_seconds', 'watchdog_protected', 'acpi']:
            self.assertEqual(result[key], recorded[key])
        self.assertEqual(result['diagnostic']['pci_scan']['count'], 16)
        self.assertEqual(result['diagnostic']['pci_scan']['status'], 0)
        self.assertEqual(result['diagnostic']['inventory_result'], 65536)
        self.assertFalse(result['diagnostic']['platform_admitted'])

    def test_scan(self):
        result = classify(PAYLOAD)
        self.assertTrue(result['ecam']['armed'] and result['watchdog_protected'])
        self.assertFalse(result['diagnostic']['platform_admitted'])
        self.assertIn('ecam_decoder_sha256', result['diagnostic'])

    def test_failures(self):
        before_scan = PAYLOAD[:PAYLOAD.index(P['PCI-SCAN'].encode())]
        for reason in ['qotom-ecam-arm', 'qotom-ecam-transaction']:
            prefix = before_scan.replace(D['ARM'], b'') if reason.endswith('-arm') else before_scan
            raw = prefix + P['FINAL'].encode() + b' status=FAIL reason=' + reason.encode() + b'\n'
            result = classify(raw)
            self.assertEqual(result['diagnostic']['terminal_reason'], reason)
            self.assertEqual(result['diagnostic']['replay_scope'], 'cpu-msr-before-ecam-failure')
            self.assertFalse(result['diagnostic']['platform_admitted'])
            with self.assertRaises(ValueError): classify(raw, ecam_read=False)
            with self.assertRaises(ValueError): classify(raw.replace(b' readback=1\n', b' readback=0\n'))

    def test_rejections(self):
        for raw in [PAYLOAD.replace(D['ARM'], b''), PAYLOAD.replace(D['ARM'], D['ARM']*2),
                    PAYLOAD.replace(b'access=read32', b'access=write32')]:
            with self.assertRaises(ValueError): classify(raw)
        for options in [dict(dsdt=False), dict(ecam_memory=False), dict(pci_read_trace=True)]:
            with self.assertRaises(ValueError): classify(PAYLOAD, **options)


if __name__ == '__main__': unittest.main()
