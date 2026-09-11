#!/usr/bin/env python3
"""Check strict PAT/control observation decoding and preserve existing replay."""
from pathlib import Path
import json
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-ecam-memory-capture.py'))
B = runpy.run_path(str(ROOT / 'scripts/check-qotom-bootstrap-capture.py'))
PCI = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
CAPTURE = ROOT / 'hardware/lab/observations/qotom-native-acpi-20260911'
PROTOCOL = PCI['load_protocol'](CAPTURE / 'diagnostic-protocol.tsv')
RAW = (CAPTURE / 'cycle-1/diagnostic.raw').read_bytes()
EDX = 3219913727


def stream(edx=EDX):
    lines = RAW.replace(str(EDX).encode(), str(edx).encode()).splitlines(keepends=True)
    available = int(edx & 0x220 == 0x220)
    lines.insert(3, B['PREFIX'] + f'cpuid-edx={edx} available={available} apic-base={0xfee00900 if available else 0}\n'.encode())
    return b''.join(lines)


def sample(edx=EDX, available=1, pat=0x0007040600070406, cr0=0x80010033, cr3=0x100000, cr4=0x620):
    return D['PREFIX'] + f'cpuid-edx={edx} available={available} pat={pat} cr0={cr0} cr3={cr3} cr4={cr4}\n'.encode()


def insert(record, raw=None):
    lines = (stream() if raw is None else raw).splitlines(keepends=True)
    lines.insert(4, record)
    return b''.join(lines)


class MemoryCaptureTests(unittest.TestCase):
    def test_values_are_observed_not_admitted(self):
        for pat in (0, 0x0007040600070406, 0xffffffffffffffff):
            clean, result = D['extract'](insert(sample(pat=pat)), PROTOCOL)
            self.assertEqual(clean, stream())
            self.assertEqual(result['ia32_pat'], pat)
            self.assertEqual(result['pat_entries'], [(pat >> (8*i)) & 255 for i in range(8)])
            self.assertFalse(result['memory_type_admitted'])
            self.assertFalse(result['platform_admitted'])
            final, _ = B['extract'](clean, PROTOCOL)
            self.assertEqual(final, RAW)

    def test_feature_gate(self):
        for bit in (5, 16):
            edx = EDX & ~(1 << bit)
            clean, result = D['extract'](insert(sample(edx, 0, 0), stream(edx)), PROTOCOL)
            self.assertEqual(clean, stream(edx))
            self.assertFalse(result['available'])
            self.assertIsNone(result['pat_entries'])
            for record in (sample(edx, 1, 0), sample(edx, 0, 1)):
                with self.assertRaises(ValueError): D['extract'](insert(record, stream(edx)), PROTOCOL)

    def test_width_and_format(self):
        for field, value in [('edx', 1 << 32), ('pat', 1 << 64), ('cr0', 1 << 64),
                             ('cr3', 1 << 64), ('cr4', 1 << 64), ('edx', '01'),
                             ('pat', '-1'), ('available', 2)]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                D['extract'](insert(sample(**{field: value})), PROTOCOL)
        for record in (sample().rstrip(b'\n'), sample().replace(b' pat=', b' msr='),
                       sample() * 2, sample() + b' ' * 257):
            with self.assertRaises(ValueError): D['extract'](insert(record), PROTOCOL)

    def test_bound_to_cpu_and_bootstrap(self):
        for raw in (insert(sample()).replace(str(EDX).encode(), str(EDX-1).encode(), 1),
                    insert(sample()).replace(b'readback=1', b'readback=0'),
                    insert(sample(edx=EDX-1)),
                    insert(sample()).replace(B['PREFIX'] + b'cpuid-edx=', B['PREFIX'] + b'bad=')):
            with self.assertRaises(ValueError): D['extract'](raw, PROTOCOL)

    def test_missing_duplicate_and_misplaced(self):
        for raw in (stream(), sample() + stream(), insert(sample()) + sample(),
                    stream() + sample()):
            with self.assertRaises(ValueError): D['extract'](raw, PROTOCOL)

    def test_early_rejection(self):
        rejected = PROTOCOL['FINAL'].encode() + b' status=FAIL reason=j1900-cpu-profile\n'
        self.assertEqual(D['extract'](rejected, PROTOCOL), (rejected, None))
        with self.assertRaises(ValueError): D['extract'](sample() + rejected, PROTOCOL)

    def test_classifier_requires_opt_in_bootstrap(self):
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        with self.assertRaisesRegex(ValueError, 'requires bootstrap'):
            lab['classify_cpu_protected']([], '', '', '', ecam_memory=True)

    def test_protected_capture_preserves_existing_evidence(self):
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        raw = (CAPTURE / 'cycle-1/serial.raw').read_bytes()
        recorded = json.loads((CAPTURE / 'cycle-1/result.json').read_text())
        position = raw.index(b'\n', raw.index(PROTOCOL['CONTROL'].encode())) + 1
        bootstrap = B['PREFIX'] + f'cpuid-edx={EDX} available=1 apic-base={0xfee00900}\n'.encode()
        raw = raw[:position] + bootstrap + sample() + raw[position:]
        terminal = raw.index(PROTOCOL['FINAL'].encode())
        end = raw.index(b'\n', terminal) + 1
        events = [{'hex': raw[:end].hex(), 'elapsed': 1},
                  {'hex': raw[end:].hex(), 'elapsed': 36}]
        args = (events, recorded['elf_sha256'], CAPTURE / 'diagnostic-protocol.tsv',
                ROOT / 'build/j1900-cpu-host/host', ROOT / 'build/qotom-pci-inventory-host/host')
        options = dict(handoff=True, acpi=True, pci_read_trace=True, bootstrap=True)
        result = lab['classify_cpu_protected'](*args, **options, ecam_memory=True)
        self.assertEqual(result['ecam_memory']['ia32_pat'], 0x0007040600070406)
        self.assertFalse(result['ecam_memory']['memory_type_admitted'])
        self.assertTrue(result['bootstrap']['bsp'])
        self.assertEqual(result['diagnostic']['pci_headers'], recorded['diagnostic']['pci_headers'])
        self.assertEqual(len(result['acpi']['tables']), 11)
        self.assertTrue(result['watchdog_protected'])
        self.assertGreaterEqual(result['quiet_seconds'], 30)
        self.assertFalse(result['diagnostic']['platform_admitted'])
        self.assertIn('ecam_memory_decoder_sha256', result['diagnostic'])
        with self.assertRaises(ValueError):
            lab['classify_cpu_protected'](*args, **options)


if __name__ == '__main__':
    unittest.main()
