#!/usr/bin/env python3
import runpy
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-entry-integration-capture.py'))
C = ROOT / 'hardware/lab/observations/qotom-native-copy-root-publication-20260912'
P = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))['load_protocol'](
    C / 'diagnostic-protocol.tsv')
BASE = (C / 'cycle-1/serial.raw').read_bytes()
OLD = P['FINAL'].encode() + b' status=FAIL reason=qotom-entry-integration-pending\n'
BASE = BASE[BASE.index(P['BOOT'].encode()):BASE.index(OLD) + len(OLD)]
READY = (b'LEANOS-LAB/1 QOTOM-ENTRY-READY profile=qotom-copy-roots-v1 '
         b'subject=1 address-space=1 gates=2,6,8,13,14,128 root=closed cpl3-authority=0\n')
FINAL = P['FINAL'].encode() + b' status=FAIL reason=qotom-exception-integration-pending\n'


def record(**changes):
    values = {'status': 0, 'entries': 2, 'returns': 1,
              'incoming-root': 0x1a0000, 'closed-root': 0x1a2000,
              'active-root': 0x1a2000, 'frame': 1, 'user-if': 0, 'gprs': 15,
              'close-readback': 1, 'return-reload': 1, 'error-mask': 0,
              'entry-contract': 1, 'cpl3-authority': 0}
    values.update(changes)
    fields = ' '.join(f'{key}={value}' for key, value in values.items())
    return b'LEANOS-LAB/1 QOTOM-ENTRY profile=qotom-copy-roots-v1 ' + fields.encode() + b'\n'


class Capture(unittest.TestCase):
    def test_success(self):
        projected, value = D['extract'](BASE.replace(OLD, READY + record() + FINAL), P)
        self.assertEqual(projected, BASE)
        self.assertEqual(value['entries'], 2)
        self.assertEqual(value['completed_returns'], 1)
        self.assertTrue(value['frame_validated'] and value['close_readback'] and value['return_reload'])
        self.assertFalse(value['cpl3_authority'])

    def test_mutations(self):
        good = READY + record() + FINAL
        mutations = [
            good + record(), good.replace(b'status=0', b'status=00'),
            good.replace(b'entries=2', b'entries=1'),
            good.replace(b'returns=1', b'returns=2'),
            good.replace(b'incoming-root=1703936', b'incoming-root=0'),
            good.replace(b'incoming-root=1703936', b'incoming-root=1712128'),
            good.replace(b'closed-root=1712128', b'closed-root=1712129'),
            good.replace(b'active-root=1712128', b'active-root=1703936'),
            good.replace(b'frame=1', b'frame=0'),
            good.replace(b'user-if=0', b'user-if=1'),
            good.replace(b'gprs=15', b'gprs=14'),
            good.replace(b'close-readback=1', b'close-readback=0'),
            good.replace(b'return-reload=1', b'return-reload=0'),
            good.replace(b'error-mask=0', b'error-mask=1'),
            good.replace(b'entry-contract=1', b'entry-contract=0'),
            good.replace(b'cpl3-authority=0', b'cpl3-authority=1'),
            good.replace(b'gates=2,6,8,13,14,128', b'gates=128'),
            good.replace(b'qotom-exception-integration-pending', b'qotom-entry-integration-pending'),
        ]
        for value in mutations:
            with self.subTest(value=value[-100:]), self.assertRaises(ValueError):
                D['extract'](BASE.replace(OLD, value), P)


if __name__ == '__main__':
    unittest.main()
