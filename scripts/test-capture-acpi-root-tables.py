#!/usr/bin/env python3
"""Exercise physical-query isolation and capture bounds without /dev/mem."""
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest

HELPER = Path(__file__).with_name('capture-acpi-root-tables.sh').resolve()

class CaptureTests(unittest.TestCase):
    def capture(self, entries, *, xsdt=None, size=40, ambiguous=False, fail=False):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory)
            acpi = p / 'acpi'
            acpi.mkdir()
            for kind, vector, width in [('RSDT', entries, 4), ('XSDT', xsdt, 8)]:
                if vector is not None:
                    (acpi / f'{kind}.bin').write_bytes(kind.encode() + bytes(32) + b''.join(
                        int(v).to_bytes(width, 'little') for v in vector))
            fake = p / 'bin'
            fake.mkdir()
            (fake / 'sudo').write_text('#!/bin/sh\nshift\nexec "$@"\n')
            (fake / 'acpidump').write_text('''#!/usr/bin/env python3
import os, pathlib, sys
with open(os.environ['CALLS'], 'a') as f: f.write(' '.join(sys.argv[1:])+'\\n')
if os.environ['FAIL'] == '1': sys.exit(1)
b = b'TEST' + bytes(int(os.environ['SIZE']) - 4)
pathlib.Path('test.dat').write_bytes(b)
if os.environ['AMBIGUOUS'] == '1': pathlib.Path('test1.dat').write_bytes(b)
''')
            for f in fake.iterdir(): f.chmod(0o755)
            env = dict(os.environ, PATH=str(fake)+':'+os.environ['PATH'], CALLS=str(p/'calls'),
                       SIZE=str(size), AMBIGUOUS=str(int(ambiguous)), FAIL=str(int(fail)))
            result = subprocess.run(['bash', str(HELPER), str(acpi)], env=env,
                                    capture_output=True, text=True)
            calls = (p/'calls').read_text().splitlines() if (p/'calls').exists() else []
            files = {f.name: f.read_bytes() for f in (acpi/'root-tables').glob('*.bin')}
            return result, calls, files

    def test_each_address_has_its_own_copy_despite_same_signature(self):
        result, calls, files = self.capture([4096, 8192], xsdt=[8192, 4096])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 2)
        self.assertEqual(set(files), {'0000000000001000.bin', '0000000000002000.bin'})
        self.assertTrue(all(v == b'TEST'+bytes(36) for v in files.values()))

    def test_zero_address_rejected_before_physical_read(self):
        result, calls, _ = self.capture([0])
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, [])

    def test_high_address_rejected_before_physical_read(self):
        result, calls, _ = self.capture(None, xsdt=[2**63])
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, [])

    def test_root_entry_limit_precedes_physical_reads(self):
        result, calls, _ = self.capture([4096]*257)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, [])

    def test_ambiguous_physical_response_rejected(self):
        result, _, files = self.capture([4096], ambiguous=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(files, {})

    def test_failed_physical_read_rejected(self):
        result, _, files = self.capture([4096], fail=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(files, {})

    def test_oversized_table_rejected(self):
        result, _, files = self.capture([4096], size=65537)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(files, {})

    def test_aggregate_bound(self):
        result, calls, files = self.capture(list(range(4096, 4096*18, 4096)), size=65536)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 17)
        self.assertEqual(len(files), 16)

if __name__ == '__main__': unittest.main()
