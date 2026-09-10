#!/usr/bin/env python3
"""Check the binding from retained FreeBSD observations to hosted inputs."""
from pathlib import Path
import shutil
import tempfile
import unittest
import firmware_root_corpus as roots

SOURCE = Path(__file__).resolve().parents[1] / 'firmware-corpus/qotom-j1900-freebsd-uefi'


class SourceBindingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.case = Path(self.temp.name) / 'case'
        shutil.copytree(SOURCE, self.case)

    def test_captured_projection(self):
        roots.validate_freebsd_projection(self.case)
        self.assertIn('efi-map.bin', roots.capture_files(self.case))

    def test_changed_projection(self):
        path = self.case / 'memmap.tsv'
        path.write_text(path.read_text().replace('System RAM', 'Reserved', 1))
        with self.assertRaisesRegex(ValueError, 'projection differs'):
            roots.validate_freebsd_projection(self.case)

    def test_changed_cpu_identity(self):
        (self.case / 'executing-apic-id.txt').write_text('2\n')
        with self.assertRaisesRegex(ValueError, 'executing identity differs'):
            roots.validate_freebsd_projection(self.case)

    def test_changed_producer(self):
        path = self.case / 'cpu0-sample.txt'
        text = path.read_text(); path.write_text('0'*64 + text[64:])
        with self.assertRaisesRegex(ValueError, 'producer digest differs'):
            roots.validate_freebsd_projection(self.case)

    def test_changed_root_address(self):
        (self.case / 'acpi-root-address.txt').write_text('0x1000\n')
        with self.assertRaisesRegex(ValueError, 'RSDP address differs'):
            roots.validate_freebsd_projection(self.case)

    def test_changed_madt_copy(self):
        path = self.case / 'acpi/APIC.bin'
        data = bytearray(path.read_bytes()); data[-1] ^= 1; path.write_bytes(data)
        with self.assertRaisesRegex(ValueError, 'MADT differs'):
            roots.validate_freebsd_projection(self.case)

    def test_bad_address_inventory(self):
        for value in ('[]', '{}', '{"RSDP": true}'):
            with self.subTest(value=value):
                (self.case / 'acpi/addresses.json').write_text(value)
                with self.assertRaisesRegex(ValueError, 'malformed FreeBSD physical address'):
                    roots.validate_freebsd_projection(self.case)

    def test_unaccounted_source_file(self):
        (self.case / 'unexpected.bin').write_bytes(b'x')
        with self.assertRaisesRegex(ValueError, 'unaccounted files'):
            roots.capture_files(self.case)


if __name__ == '__main__': unittest.main()
