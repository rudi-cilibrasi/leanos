#!/usr/bin/env python3
"""Check BSP observations, feature gates, and unchanged CPU/PCI replay bytes."""
import json
import hashlib
from pathlib import Path
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-bootstrap-capture.py'))
PCI = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
CAPTURE = ROOT / 'hardware/lab/observations/qotom-native-acpi-20260911'
PROTOCOL = PCI['load_protocol'](CAPTURE / 'diagnostic-protocol.tsv')
RAW = (CAPTURE / 'cycle-1/diagnostic.raw').read_bytes()
EDX = 3219913727


def sample(value=0xfee00900, edx=EDX, available=1):
    return D['PREFIX'] + f'cpuid-edx={edx} available={available} apic-base={value}\n'.encode()


def insert(record, raw=RAW):
    lines = raw.splitlines(keepends=True)
    lines.insert(3, record)
    return b''.join(lines)


class BootstrapTests(unittest.TestCase):
    def test_raw_bsp_and_ap_observations(self):
        for value, bsp, x2 in ((0xfee00900, True, False), (0xfee00800, False, False),
                              (0xfee00d00, True, True), (0xffffffffffffffff, True, True)):
            clean, data = D['extract'](insert(sample(value)), PROTOCOL)
            self.assertEqual(clean, RAW)
            self.assertEqual(data['ia32_apic_base'], value)
            self.assertEqual((data['bsp'], data['x2apic_enabled']), (bsp, x2))
            self.assertFalse(data['platform_admitted'])
            self.assertFalse(data['ap_dormancy_established'])

    def test_absent_feature_does_not_claim_a_read(self):
        edx = EDX & ~0x200
        raw = RAW.replace(str(EDX).encode(), str(edx).encode())
        clean, data = D['extract'](insert(sample(0, edx, 0), raw), PROTOCOL)
        self.assertEqual(clean, raw)
        self.assertFalse(data['available'])
        self.assertIsNone(data['bsp'])
        with self.assertRaises(ValueError):
            D['extract'](insert(sample(1, edx, 0), raw), PROTOCOL)

    def test_gate_binding_and_transport_rejections(self):
        for record in (sample(1 << 64), sample(edx=1 << 32), sample(edx=0),
                       sample(available=0), sample(edx='01'), sample() * 2,
                       sample().rstrip(b'\n'), sample().replace(b'apic-base=', b'base=')):
            with self.subTest(record=record), self.assertRaises(ValueError):
                D['extract'](insert(record), PROTOCOL)
        for raw in (RAW, sample() + RAW, insert(sample()).replace(b'readback=1', b'readback=0'),
                    insert(sample()).replace(str(EDX).encode(), str(EDX-1).encode(), 1)):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                D['extract'](raw, PROTOCOL)

    def test_protected_capture_preserves_existing_replay(self):
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        raw = (CAPTURE / 'cycle-1/serial.raw').read_bytes()
        recorded = json.loads((CAPTURE / 'cycle-1/result.json').read_text())
        position = raw.index(b'\n', raw.index(PROTOCOL['CONTROL'].encode())) + 1
        raw = raw[:position] + sample() + raw[position:]
        terminal = raw.index(PROTOCOL['FINAL'].encode())
        end = raw.index(b'\n', terminal) + 1
        events = [{'hex': raw[:end].hex(), 'elapsed': 1},
                  {'hex': raw[end:].hex(), 'elapsed': 36}]
        args = (events, recorded['elf_sha256'], CAPTURE / 'diagnostic-protocol.tsv',
                ROOT / 'build/j1900-cpu-host/host', ROOT / 'build/qotom-pci-inventory-host/host')
        result = lab['classify_cpu_protected'](*args, handoff=True, acpi=True,
                                              pci_read_trace=True, bootstrap=True)
        self.assertTrue(result['bootstrap']['bsp'])
        self.assertEqual(result['diagnostic']['pci_headers'], recorded['diagnostic']['pci_headers'])
        self.assertEqual(len(result['acpi']['tables']), 11)
        self.assertFalse(result['diagnostic']['platform_admitted'])
        self.assertIn('bootstrap_decoder_sha256', result['diagnostic'])
        with self.assertRaises(ValueError):
            lab['classify_cpu_protected'](*args, handoff=True, acpi=True, pci_read_trace=True)

    def test_retained_physical_bootstrap_and_recovery(self):
        directory = ROOT / 'hardware/lab/observations/qotom-bootstrap-20260911'
        manifest = json.loads((directory / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((directory / name).read_bytes()).hexdigest(), digest, name)
        cycle = directory / 'cycle-1'
        recorded = json.loads((cycle / 'result.json').read_text())
        events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        result = lab['classify_cpu_protected'](events, recorded['elf_sha256'],
            directory / 'diagnostic-protocol.tsv', ROOT / 'build/j1900-cpu-host/host',
            ROOT / 'build/qotom-pci-inventory-host/host', handoff=True, acpi=True,
            pci_read_trace=True, bootstrap=True)
        self.assertEqual(result['bootstrap'], json.loads((cycle / 'bootstrap.json').read_text()))
        self.assertEqual(result['bootstrap']['ia32_apic_base'], 0xfee00900)
        self.assertEqual(result['handoff']['apic'], 0)
        self.assertEqual(result['diagnostic']['terminal_reason'], 'qotom-pci-enumeration')
        self.assertEqual(result['diagnostic']['pci_headers'], [])
        self.assertEqual(result['pci_read_trace']['mismatches'], 1)
        self.assertEqual(len(result['acpi']['tables']), 11)
        self.assertTrue(result['watchdog_protected'])
        self.assertGreater(result['quiet_seconds'], 30)

    def test_early_rejection_has_no_sample(self):
        rejected = PROTOCOL['FINAL'].encode() + b' status=FAIL reason=j1900-cpu-profile\n'
        self.assertEqual(D['extract'](rejected, PROTOCOL), (rejected, None))
        with self.assertRaises(ValueError):
            D['extract'](sample() + rejected, PROTOCOL)


if __name__ == '__main__':
    unittest.main()
