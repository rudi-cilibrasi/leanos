#!/usr/bin/env python3
from pathlib import Path
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-exception-integration-capture.py'))
E = runpy.run_path(str(ROOT / 'scripts/check-qotom-entry-integration-capture.py'))
R = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
C = ROOT / 'hardware/lab/observations/qotom-native-copy-root-publication-20260912'
ENTRY_EVIDENCE = ROOT / 'hardware/lab/observations/qotom-native-entry-integration-20260912'
P = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))['load_protocol'](
    ENTRY_EVIDENCE / 'diagnostic-protocol.tsv')
BASE = (C / 'cycle-1/serial.raw').read_bytes()
OLD = P['FINAL'].encode() + b' status=FAIL reason=qotom-entry-integration-pending\n'
BASE = BASE[BASE.index(P['BOOT'].encode()):BASE.index(OLD) + len(OLD)]
READY = (b'LEANOS-LAB/1 QOTOM-ENTRY-READY profile=qotom-copy-roots-v1 '
         b'subject=1 address-space=1 gates=2,6,8,13,14,128 root=closed cpl3-authority=0\n')
MANIFEST = P['ENTRY-MANIFEST'].encode() + E['MANIFEST_SUFFIX']
PORT_CONTROL = P['DIRECT-PORT-CONTROL'].encode() + E['PORT_CONTROL_SUFFIX']


def entry_record():
    return (b'LEANOS-LAB/1 QOTOM-ENTRY profile=qotom-copy-roots-v1 status=0 '
            b'entries=2 returns=1 incoming-root=1703936 closed-root=1712128 '
            b'active-root=1712128 frame=1 user-if=0 gprs=15 close-readback=1 '
            b'return-reload=1 error-mask=0 entry-contract=1 cpl3-authority=0\n')


class Capture(unittest.TestCase):
    def good(self):
        return BASE.replace(OLD, MANIFEST + PORT_CONTROL + READY +
                            entry_record() + D['MARKER'])

    def test_success(self):
        projected, value, entry = D['extract'](self.good(), P)
        self.assertEqual(projected, BASE)
        self.assertEqual(value['terminal_vector'], 6)
        self.assertEqual(value['completed_returns'], 2)
        self.assertEqual(value['closed_root'], entry['closed_root'])
        self.assertTrue(value['close_readback'] and value['user_return_value_validated'])

    def test_mutations(self):
        good = self.good()
        mutations = [
            good + D['MARKER'], good.replace(b'!C6', b'!U6'),
            good.replace(b'!C6', b'!C2'), good[:-1],
            good.replace(b'entries=2', b'entries=3'),
            good.replace(b'returns=1', b'returns=2'),
            good.replace(b'close-readback=1', b'close-readback=0'),
            good.replace(D['MARKER'], P['FINAL'].encode() +
                         b' status=FAIL reason=qotom-exception-integration-pending\n'),
        ]
        for value in mutations:
            with self.subTest(value=value[-120:]), self.assertRaises(ValueError):
                D['extract'](value, P)

    def test_protected_direct_terminal(self):
        digest = 'a' * 64
        prefix = (b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
                  b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
                  b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD sha256=' +
                  digest.encode() + b'\n')
        mode = R['EXPECTED'][:-len(R['EXPECTED_KERNEL'])]
        raw = self.good()
        events = [
            {'hex': prefix.hex(), 'elapsed': 1},
            {'hex': (mode + raw).hex(), 'elapsed': 3},
            {'hex': b'firmware\n'.hex(), 'elapsed': 37},
            {'hex': (b'LEANOS-LAB/1 DEFAULT request=none\n' +
                     R['CHAIN']).hex(), 'elapsed': 38},
        ]
        expected, extracted = R['cpu_diagnostic_bytes'](
            events, P, False, D['MARKER'])
        self.assertEqual(extracted, raw)
        self.assertEqual(expected, mode + raw)
        result = R['classify_protected'](
            events, digest, expected, P['BOOT'].encode(),
            structured_terminal=False, quiet_range=(30, 100))
        self.assertTrue(result['watchdog_protected'])
        with self.assertRaises(ValueError):
            R['classify_protected'](events, digest, expected, P['BOOT'].encode())
        too_late = [*events[:2], {**events[2], 'elapsed': 104},
                    {**events[3], 'elapsed': 105}]
        with self.assertRaises(ValueError):
            R['classify_protected'](
                too_late, digest, expected, P['BOOT'].encode(),
                structured_terminal=False, quiet_range=(30, 100))


if __name__ == '__main__':
    unittest.main()
