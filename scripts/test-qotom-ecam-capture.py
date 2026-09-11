#!/usr/bin/env python3
import copy
import json
from pathlib import Path
import runpy
import unittest
ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-ecam-capture.py'))
A = runpy.run_path(str(ROOT / 'scripts/check-qotom-acpi-capture.py'))
P = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))['load_protocol'](ROOT / 'hardware/lab/observations/qotom-dsdt-20260911/diagnostic-protocol.tsv')
C = ROOT / 'hardware/lab/observations/qotom-dsdt-20260911/cycle-1'
_, META, FILES = A['extract']((C / 'serial.raw').read_bytes(), (C / 'multiboot2.bin').read_bytes(), dsdt=True)
# Synthetic transport boundary fixture; this is not a native ECAM capture.
PRE = b'boot\ncpu\ncontrol\nbootstrap\nmemory\n'
SCAN = P['PCI-SCAN'].encode() + b' codec=1 status=0 count=0 bus=0 device=0 function=0 offset=0\n'
FINAL = P['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
RAW = PRE + D['ARM'] + SCAN + FINAL


class Capture(unittest.TestCase):
    def test_bound_arm(self):
        raw, info = D['extract'](RAW, P, META, FILES)
        self.assertEqual(raw, PRE + SCAN + FINAL)
        self.assertTrue(info['armed'] and info['firmware_matches'])
        self.assertFalse(info['platform_admitted'])

    def test_records(self):
        for raw in [RAW.replace(D['ARM'], b''), RAW.replace(D['ARM'], D['ARM'] * 2),
                    D['ARM'] + RAW.replace(D['ARM'], b''),
                    RAW.replace(b'access=read32', b'access=write32'), RAW[:-1],
                    RAW.replace(SCAN, SCAN * 2), RAW.replace(SCAN, b'')]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                D['extract'](raw, P, META, FILES)

    def test_firmware(self):
        bad = copy.deepcopy(META); bad['tables'][0]['address'] += 4096
        self.assertFalse(D['firmware_matches'](bad, FILES))
        for name in FILES:
            bad_files = dict(FILES); data = bytearray(bad_files[name]); data[-1] ^= 1
            bad_files[name] = bytes(data)
            with self.subTest(name=name), self.assertRaises(ValueError):
                D['extract'](RAW, P, META, bad_files)
        self.assertFalse(D['firmware_matches'](META, {}))

    def test_rejection(self):
        raw = PRE + P['FINAL'].encode() + b' status=FAIL reason=qotom-ecam-arm\n'
        _, info = D['extract'](raw, P, META, FILES)
        self.assertFalse(info['armed'])  # Matching firmware can still fail the root/control gate.
        with self.assertRaises(ValueError): D['extract'](raw, P, None, {})
        with self.assertRaises(ValueError): D['extract'](raw.replace(PRE, PRE + D['ARM']), P, META, FILES)

    def test_transaction_fault(self):
        raw = PRE + D['ARM'] + P['FINAL'].encode() + b' status=FAIL reason=qotom-ecam-transaction\n'
        _, info = D['extract'](raw, P, META, FILES)
        self.assertTrue(info['transaction_fault'])


if __name__ == '__main__': unittest.main()
