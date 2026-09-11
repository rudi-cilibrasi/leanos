#!/usr/bin/env python3
"""Keep native bytes and physical arguments distinct from reconstructed rows."""
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import native_handoff_corpus as native

SPEC = importlib.util.spec_from_file_location('corpus', Path(__file__).with_name('firmware-corpus.py'))
corpus = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(corpus)


class NativeCorpusTests(unittest.TestCase):
    def test_exact_capture_and_complete_projection(self):
        rows = native.inputs()
        self.assertEqual(len(rows), 9)
        name, raw, magic, address, words = rows[0]
        manifest = json.loads(native.MANIFEST.read_text())
        original = native.ROOT / manifest['capture'] / 'cycle-1/multiboot2.bin'
        self.assertEqual(raw, original.read_bytes())
        self.assertEqual((name, magic, address), ('captured', 0x36d76289, 2728208))
        self.assertEqual(words[:5], [1, 1, 2680, 19, 4])
        self.assertEqual(len(words), 5 + 19 * 3 + 4 * 3 + 1)
        self.assertEqual(words[-1], 0)
        self.assertEqual({r[0] for r in rows[1:]}, set(native.MUTATIONS))
        for name, _, _, _, words in rows[1:]:
            self.assertEqual(words, [1, 2, native.MUTATIONS[name], 0, 0])

    def test_drivers_bind_physical_arguments(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            rows = native.rows(out)
            corpus.write_replay(rows, [], out)
            corpus.write_lean(rows, [], out)
            driver = (out / 'replay.tsv').read_text()
            lean = (out / 'Corpus.lean').read_text()
            self.assertIn('\t920085129\t2728208\t', driver)
            self.assertIn('\t0\t2728208\t', driver)
            self.assertIn('\t920085129\t2728209\t', driver)
            self.assertIn('query 920085129 2728208', lean)
            self.assertIn('query 0 2728208', lean)
            self.assertIn('query 920085129 2728209', lean)

    def test_reject_manifest_drift(self):
        original = json.loads(native.MANIFEST.read_text())
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'manifest.json'
            for field, value in [('raw_sha256', '0' * 64), ('magic', 0),
                                 ('address', 4096), ('schema', 'unknown')]:
                manifest = dict(original, **{field: value})
                path.write_text(json.dumps(manifest))
                with self.subTest(field=field), patch.object(native, 'MANIFEST', path), self.assertRaises(ValueError):
                    native.inputs()

    def test_reject_changed_capture_bytes(self):
        manifest = json.loads(native.MANIFEST.read_text())
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp) / 'capture'
            shutil.copytree(native.ROOT / manifest['capture'], directory)
            raw = directory / 'cycle-1/multiboot2.bin'
            data = bytearray(raw.read_bytes()); data[-1] ^= 1; raw.write_bytes(data)
            manifest['capture'] = str(directory)
            path = Path(tmp) / 'manifest.json'; path.write_text(json.dumps(manifest))
            with patch.object(native, 'MANIFEST', path), self.assertRaisesRegex(ValueError, 'hash mismatch'):
                native.inputs()


if __name__ == '__main__':
    unittest.main()
