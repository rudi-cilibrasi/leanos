#!/usr/bin/env python3
"""Bind native firmware replay arguments, bytes and mutations to capture evidence."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
from dataclasses import replace
import native_firmware_root_corpus as native
import firmware_root_corpus as roots


class NativeRootTests(unittest.TestCase):
    def test_exact_capture_arguments_and_bytes(self):
        base, executing = native.load()
        cycle = native.DIRECTORY / 'cycle-1'
        handoff = json.loads((cycle / 'handoff.json').read_text())
        self.assertEqual((base.magic, base.info_address, executing),
                         (handoff['magic'], handoff['address'], handoff['apic']))
        self.assertEqual(base.info, (cycle / 'multiboot2.bin').read_bytes())
        self.assertEqual(base.root, (cycle / 'acpi' / f'{base.root_address:016x}.bin').read_bytes())
        self.assertEqual(len(base.tables), 10)
        for address, data in base.tables:
            self.assertEqual(data, (cycle / 'acpi' / f'{address:016x}.bin').read_bytes())
        with tempfile.TemporaryDirectory() as tmp:
            header = base.write(Path(tmp)).read_text().splitlines()[0].split('\t')
            self.assertEqual(header[3:], [str(base.magic), str(base.info_address)])
        query = roots.lean_query(base, executing)
        self.assertIn(f'capturedRootQuery {base.magic} {base.info_address} ', query)

    def test_legacy_bundle_keeps_defaults(self):
        base, _ = native.load()
        old = replace(base, magic=0x36d76289, info_address=0x1000)
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(len(old.write(Path(tmp)).read_text().splitlines()[0].split('\t')), 3)
        self.assertNotEqual(base.digest(), old.digest())

    def test_tampered_file_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / 'capture'; shutil.copytree(native.DIRECTORY, target)
            p = target / 'cycle-1/multiboot2.bin'
            p.write_bytes(p.read_bytes()[:-1] + b'X')
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                native.load(target)

    def test_result_only_mutations_rejected(self):
        metadata_path = native.ROOT / 'firmware-corpus/qotom-native-root.json'
        original = metadata_path.read_text()
        real_read_text = Path.read_text
        # Exercise ordinary decoder, nested SDT detail, and admission names.
        mutations = {
            'root-rsdp-signature': 'decoder-rejected:invalidLegacyChecksum',
            'root-checksum': 'decoder-rejected:madtSelection.root.invalidLength',
            'native-root': 'admission-rejected:bspMismatch',
            'root-duplicate-cpu': 'accepted',
            'root-missing-cpus': 'admission-rejected:unknownReason',
        }
        for name, wrong_result in mutations.items():
            with self.subTest(case=name), tempfile.TemporaryDirectory() as tmp:
                metadata = json.loads(original)
                metadata['inputs'][name]['result'] = wrong_result
                def read_text(path, *args, **kwargs):
                    if path == metadata_path:
                        return json.dumps(metadata)
                    return real_read_text(path, *args, **kwargs)
                with patch.object(Path, 'read_text', read_text):
                    with self.assertRaisesRegex(ValueError, 'result disagrees with words'):
                        native.rows(Path(tmp))

    def test_all_mutations_pin_same_native_arguments(self):
        cases, executing = native.inputs()
        original = cases['native-root']
        for name, replay in cases.items():
            if name not in ('native-bad-magic', 'native-unaligned-address'):
                self.assertEqual((replay.magic, replay.info_address), (original.magic, original.info_address))
        with tempfile.TemporaryDirectory() as tmp:
            rows = native.rows(Path(tmp))
            self.assertEqual(len(rows), 25)
            self.assertTrue(all(row['executing'] == executing for row in rows))
            self.assertTrue(all(len(row['words']) == 6 for row in rows))
        self.assertEqual(hashlib.sha256(original.info).hexdigest(),
                         json.loads((native.DIRECTORY / 'cycle-1/handoff.json').read_text())['raw_sha256'])


if __name__ == '__main__': unittest.main()
