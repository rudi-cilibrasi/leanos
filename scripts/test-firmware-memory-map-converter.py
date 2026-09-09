#!/usr/bin/env python3
"""Controlled captures: preserve firmware ordering and reject altered inputs."""
import hashlib
import importlib.util
import json
from pathlib import Path
import struct
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('converter', Path(__file__).with_name('convert-firmware-memory-map.py'))
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ConverterTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'capture'
        self.root.mkdir()
        (self.root / 'capture.json').write_text(json.dumps({'schema': 'leanos-firmware-capture-draft-v1', 'entry_count': 2}))
        for index, start, end, kind in [(0, '0x2000\n', '0x2fff\n', 'Reserved\n'), (1, '0x0\n', '0x1fff\n', 'System RAM\n')]:
            directory = self.root / 'memmap' / str(index)
            directory.mkdir(parents=True)
            for name, value in [('start', start), ('end', end), ('type', kind)]:
                (directory / name).write_text(value)
        self.digest = self.rehash()

    def rehash(self):
        text = ''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(self.root).as_posix() + '\n'
                       for p in sorted(self.root.rglob('*')) if p.is_file() and p.name != 'SHA256SUMS')
        (self.root / 'SHA256SUMS').write_text(text)
        return hashlib.sha256(text.encode()).hexdigest()

    def test_preserves_order_and_inclusive_end(self):
        data = MODULE.convert(self.root, self.digest)
        self.assertEqual(struct.unpack_from('<II', data), (80, 0))
        self.assertEqual(struct.unpack_from('<IIII', data, 8), (6, 64, 24, 0))
        self.assertEqual(struct.unpack_from('<QQII', data, 24), (0x2000, 0x1000, 2, 0))
        self.assertEqual(struct.unpack_from('<QQII', data, 48), (0, 0x2000, 1, 0))
        self.assertEqual(data[-8:], struct.pack('<II', 0, 8))

    def test_retained_capture_regenerates_observed_input(self):
        root = Path(__file__).resolve().parent.parent / 'firmware'
        manifest = json.loads((root / 'memory-corpus.json').read_text())
        for row in manifest['cases']:
            with self.subTest(case=row['id']):
                data = MODULE.convert(root / row['capture'], row['inventory_sha256'])
                self.assertEqual(hashlib.sha256(data).hexdigest(), row['converted_sha256'])

    def test_raw_and_inventory_digest_drift(self):
        with self.assertRaisesRegex(MODULE.CaptureError, 'inventory digest mismatch'):
            MODULE.convert(self.root, '0' * 64)
        (self.root / 'memmap/0/start').write_text('0x2001\n')
        with self.assertRaisesRegex(MODULE.CaptureError, 'capture digest mismatch'):
            MODULE.convert(self.root, self.digest)

    def test_extra_and_missing_files(self):
        extra = self.root / 'unrecorded'
        extra.write_text('unexpected')
        with self.assertRaisesRegex(MODULE.CaptureError, 'file inventory differs'):
            MODULE.convert(self.root, self.digest)
        extra.unlink()
        (self.root / 'memmap/0/end').unlink()
        with self.assertRaisesRegex(MODULE.CaptureError, 'incomplete'):
            MODULE.convert(self.root, self.rehash())

    def test_unsupported_kind_is_not_changed_to_reserved(self):
        (self.root / 'memmap/0/type').write_text('Persistent Memory\n')
        with self.assertRaisesRegex(MODULE.CaptureError, 'unsupported memory type'):
            MODULE.convert(self.root, self.rehash())

    def test_range_overflow_and_reversal(self):
        for start, end in [('0x0', '0xffffffffffffffff'), ('0x100', '0xff'), ('0x0', '0x10000000000000000')]:
            with self.subTest(start=start, end=end):
                (self.root / 'memmap/0/start').write_text(start)
                (self.root / 'memmap/0/end').write_text(end)
                with self.assertRaisesRegex(MODULE.CaptureError, 'invalid inclusive range'):
                    MODULE.convert(self.root, self.rehash())

    def test_duplicate_inventory_entry(self):
        p = self.root / 'SHA256SUMS'
        text = p.read_text()
        p.write_text(text + text.splitlines()[0] + '\n')
        with self.assertRaisesRegex(MODULE.CaptureError, 'unsafe or duplicate'):
            MODULE.convert(self.root, hashlib.sha256(p.read_bytes()).hexdigest())

    def test_symlink_is_rejected(self):
        path = self.root / 'memmap/0/start'
        path.unlink()
        path.symlink_to(self.root / 'memmap/1/start')
        with self.assertRaisesRegex(MODULE.CaptureError, 'symlink'):
            MODULE.convert(self.root, self.digest)


if __name__ == '__main__':
    unittest.main()
