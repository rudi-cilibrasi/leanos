#!/usr/bin/env python3
"""Exercise collection with fake pciconf output, without hardware access."""
import importlib.util
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('capture_pci', ROOT / 'hardware/lab/capture-pci.py')
pci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pci)
LISTING = 'pcib0@pci0:0:28:0: class=0x060400 rev=0x0e hdr=0x01 vendor=0x8086 device=0x0f48\n'
WORDS = [0x0f488086, 0x00100007, 0x0604000e, 0x00810000, 0, 0,
         0x00030300, 0, 0, 0, 0, 0, 0, 0, 0, 0x00400000]
RAW = ' '.join(f'{word:08x}' for word in WORDS) + '\n'


class CaptureTests(unittest.TestCase):
    def test_retained_capture_hashes_and_decoding(self):
        root = ROOT / 'hardware/lab/observations/qotom-pci-20260910'
        report = json.loads((root / 'inventory.json').read_text())
        commands = json.loads((root / 'commands.json').read_text())
        self.assertEqual(report['commands'], commands)
        self.assertEqual(len(report['functions']), 15)
        for entry in commands:
            self.assertEqual(hashlib.sha256((root / entry['file']).read_bytes()).hexdigest(),
                             entry['sha256'])
        for function in report['functions']:
            raw = (root / (function['selector'].replace(':', '-') + '.txt')).read_text()
            self.assertEqual(function, dict(selector=function['selector'], **pci.decode(raw)))

    def test_raw_multifunction_and_bridge(self):
        result = pci.decode(RAW)
        self.assertTrue(result['multifunction'])
        self.assertEqual(result['command'], 7)
        self.assertEqual(result['bridge'], dict(primary=0, secondary=3, subordinate=3, control=64))

    def test_selector_rejections(self):
        for listing in ('', LISTING * 2, LISTING.replace(':28:', ':32:'),
                        LISTING.replace('@pci', '@BAD'), 'garbage\n'):
            with self.subTest(listing=listing), self.assertRaises(ValueError):
                pci.selectors(listing)

    def test_header_rejections(self):
        for raw in (RAW + ' 0', ' '.join(RAW.split()[:-1]), RAW.replace('0f488086', 'ffffffff'),
                    RAW.replace('0f488086', '100000000'), RAW.replace('0f488086', 'nonsense')):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                pci.decode(raw)

    def test_collection_commands_and_no_overwrite(self):
        commands = []
        def run(argv):
            commands.append(argv)
            return LISTING if argv[-1] == '-l' else RAW
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp) / 'capture'
            report = pci.collect(out, run)
            self.assertFalse(report['dma_containment_established'])
            self.assertFalse(report['platform_admitted'])
            self.assertEqual(commands, [['/usr/sbin/pciconf', '-l'],
                ['/usr/sbin/pciconf', '-r', 'pci0:0:28:0', '0x0:0x3c'],
                ['/usr/sbin/pciconf', '-l']])
            self.assertEqual((out / 'pci0-0-28-0.txt').read_text(), RAW)
            with self.assertRaises(FileExistsError):
                pci.collect(out, run)
            self.assertEqual(len(commands), 3)

    def test_changed_inventory_retains_raw_without_success(self):
        results = iter([LISTING, RAW, LISTING.replace('0f48', '0f4a')])
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp) / 'capture'
            with self.assertRaisesRegex(ValueError, 'changed'):
                pci.collect(out, lambda argv: next(results))
            self.assertTrue((out / 'listing-after.txt').exists())
            self.assertFalse((out / 'inventory.json').exists())


if __name__ == '__main__':
    unittest.main()
