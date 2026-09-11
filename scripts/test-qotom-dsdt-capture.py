#!/usr/bin/env python3
"""Check FADT pointer selection and complete bounded DSDT transport."""
import ctypes
import hashlib
import json
from pathlib import Path
import runpy
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-acpi-capture.py'))
T = runpy.run_path(str(ROOT / 'scripts/test-qotom-acpi-capture.py'))


def fadt(length=148, revision=3, legacy=196608, extended=262144):
    raw = bytearray(T['table'](b'FACP', bytes(length - 36)))
    raw[8] = revision
    struct.pack_into('<I', raw, 40, legacy)
    if length >= 148:
        struct.pack_into('<Q', raw, 140, extended)
    return T['checksum'](raw, 9)


def capture(parent=None, address=262144, child=None, extra_parent=False):
    parent = fadt() if parent is None else parent
    child = T['table'](b'DSDT', bytes(8)) if child is None else child
    pointers = [131072] + ([393216] if extra_parent else [])
    records = [(65536, T['table'](b'XSDT', b''.join(struct.pack('<Q', p) for p in pointers)))]
    records += [(p, parent) for p in pointers] + [(address, child)]
    lines = [f'LEANOS-LAB/1 ACPI-BEGIN root-kind=2 root-address=65536 tables={len(pointers)} dsdt=1\n'.encode()]
    for i, (physical, raw) in enumerate(records):
        lines.append(f'LEANOS-LAB/1 ACPI-TABLE index={i} address={physical} length={len(raw)}\n'.encode())
        for offset in range(0, len(raw), 64):
            lines.append(f'LEANOS-LAB/1 ACPI-DATA offset={offset} hex={raw[offset:offset+64].hex()}\n'.encode())
    return b'CPU\n' + b''.join(lines) + b'LEANOS-LAB/1 ACPI-END\n' + T['FINAL']


class DSDTTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        path = Path(cls.tmp.name)
        (path / 'test.c').write_text('#include "acpi-dsdt-address.h"\nint select_dsdt(const uint8_t *b, uint32_t n, uint64_t *a) { return lab_fadt_dsdt_address(b,n,a); }\n')
        subprocess.run(['gcc', '-std=c11', '-Wall', '-Wextra', '-Werror', '-O2',
            '-shared', '-fPIC', '-fsanitize=undefined', '-fno-sanitize-recover=all',
            '-I', str(ROOT / 'boot'), str(path / 'test.c'), '-o', str(path / 'test.so')], check=True)
        cls.library = ctypes.CDLL(str(path / 'test.so'))
        cls.select = cls.library.select_dsdt
        cls.select.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint64)]
        cls.select.restype = ctypes.c_int

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_native_and_decoder_selection(self):
        cases = [(fadt(116, 1), 196608), (fadt(148, 3), 262144),
                 (fadt(148, 3, extended=0), 196608), (fadt(268, 5), 262144),
                 (fadt(148, 3, legacy=0), 262144),
                 (fadt(148, 3, extended=2**32 - 36), 2**32 - 36)]
        bad = [fadt(116, 0), fadt(116, 2), fadt(116, 3), fadt(147, 3),
               fadt(148, 3, legacy=0, extended=0), fadt(148, 3, extended=2**32),
               fadt(148, 3, extended=2**32-35), fadt()[:115],
               fadt().replace(b'FACP', b'APIC'), fadt() + b'\0']
        for raw, expected in cases + [(raw, None) for raw in bad]:
            with self.subTest(length=len(raw), expected=expected):
                value = ctypes.c_uint64(42)
                accepted = self.select(ctypes.create_string_buffer(raw), len(raw), ctypes.byref(value))
                if expected is None:
                    self.assertEqual((accepted, value.value), (0, 42))
                    with self.assertRaises(ValueError): D['fadt_dsdt_address'](raw)
                else:
                    self.assertEqual((accepted, value.value), (1, expected))
                    self.assertEqual(D['fadt_dsdt_address'](raw), expected)
        value = ctypes.c_uint64(42)
        self.assertEqual(self.select(None, 148, ctypes.byref(value)), 0)
        self.assertEqual(self.select(ctypes.create_string_buffer(fadt()), 148, None), 0)

    def test_complete_extended_and_legacy_capture(self):
        for parent, address in [(fadt(), 262144), (fadt(116, 1), 196608),
                                 (fadt(148, 3, extended=0), 196608)]:
            clean, metadata, files = D['extract'](capture(parent, address), T['handoff'](), dsdt=True)
            self.assertEqual(clean, b'CPU\n' + T['FINAL'])
            self.assertEqual(metadata['dsdt_address'], address)
            self.assertEqual(metadata['dsdt_fadt_address'], 131072)
            self.assertFalse(metadata['aml_executed'])
            self.assertFalse(metadata['platform_admitted'])
            self.assertEqual(len(files), 3)

    def test_missing_mixed_duplicate_or_overlapping_tables(self):
        for raw in [capture(address=196608), capture(extra_parent=True),
                    capture(parent=T['table'](b'APIC', bytes(112))),
                    capture(child=T['table'](b'SSDT')),
                    capture(parent=fadt(148,3,extended=131073), address=131073),
                    capture(parent=fadt(148,3,extended=65537), address=65537),
                    capture().replace(b' dsdt=1', b''),
                    capture().replace(b'index=2', b'index=3')]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                D['extract'](raw, T['handoff'](), dsdt=True)
        with self.assertRaises(ValueError): D['extract'](capture(), T['handoff']())
        with self.assertRaises(ValueError): D['extract'](T['capture'](), T['handoff'](), dsdt=True)

    def test_budget_and_checksum(self):
        child = bytearray(T['table'](b'DSDT', bytes(8))); child[-1] ^= 1
        payload_limit = 65536 - len(T['handoff']()) - 44 - 148 - 36
        _, metadata, _ = D['extract'](capture(child=T['table'](b'DSDT', bytes(payload_limit))),
                                      T['handoff'](), dsdt=True)
        self.assertEqual(metadata['tables'][-1]['length'], payload_limit + 36)
        for data in (capture(child=child), capture(child=T['table'](b'DSDT', bytes(payload_limit + 1)))):
            with self.assertRaises(ValueError): D['extract'](data, T['handoff'](), dsdt=True)

    def test_native_fadt_binding_and_protected_recovery(self):
        directory = ROOT / 'hardware/lab/observations/qotom-dsdt-20260911'
        manifest = json.loads((directory / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((directory / name).read_bytes()).hexdigest(), digest, name)
        cycle = directory / 'cycle-1'
        raw = (cycle / 'serial.raw').read_bytes()
        _, metadata, files = D['extract'](raw, (cycle / 'multiboot2.bin').read_bytes(), dsdt=True)
        self.assertEqual(metadata, json.loads((cycle / 'acpi.json').read_text()))
        self.assertEqual(metadata['dsdt_address'], 0xb979f180)
        self.assertEqual(len(metadata['tables']), 12)
        parent = files[f"{metadata['dsdt_fadt_address']:016x}.bin"]
        address = ctypes.c_uint64(42)
        self.assertEqual(self.select(ctypes.create_string_buffer(parent), len(parent), ctypes.byref(address)), 1)
        self.assertEqual(address.value, metadata['dsdt_address'])
        dsdt = files[f'{address.value:016x}.bin']
        self.assertEqual(len(dsdt), 30800)
        self.assertEqual(hashlib.sha256(dsdt).hexdigest(),
                         'e02b949e57c1e9eae6714dd67bce15dc25df349167235612f19e8cd2df14543f')
        events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
        self.assertEqual(b''.join(bytes.fromhex(e['hex']) for e in events), raw)
        recorded = json.loads((cycle / 'result.json').read_text())
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        result = lab['classify_cpu_protected'](events, recorded['elf_sha256'],
            directory / 'diagnostic-protocol.tsv', ROOT / 'build/j1900-cpu-host/host',
            ROOT / 'build/qotom-pci-inventory-host/host', handoff=True, acpi=True,
            pci_read_trace=True, bootstrap=True, ecam_memory=True, dsdt=True)
        self.assertEqual(result['acpi'], metadata)
        self.assertEqual(result['pci_read_trace']['mismatches'], 4)
        self.assertFalse(result['diagnostic']['platform_admitted'])
        self.assertTrue(result['watchdog_protected'])
        self.assertGreater(result['quiet_seconds'], 30)


if __name__ == '__main__': unittest.main()
