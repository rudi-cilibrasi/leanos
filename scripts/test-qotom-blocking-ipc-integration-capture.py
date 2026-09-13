#!/usr/bin/env python3
from pathlib import Path
import runpy
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-blocking-ipc-integration-capture.py'))
E = runpy.run_path(str(ROOT / 'scripts/check-qotom-entry-integration-capture.py'))
X = runpy.run_path(str(ROOT / 'scripts/test-qotom-exception-integration-capture.py'))
P = X['P']


class Capture(unittest.TestCase):
    def good(self):
        exception = X['Capture']().good()
        return exception[:-len(X['D']['MARKER'])] + D['semantic_expectation'](P)

    def test_success(self):
        projected, value, entry = D['extract'](self.good(), P)
        self.assertEqual(projected, X['BASE'])
        self.assertEqual(value['status'], 'PASS')
        self.assertEqual(value['semantic_syscalls'], 8)
        self.assertEqual(value['blocking_model_transitions'], 4)
        self.assertEqual(value['capability_model_transitions'], 4)
        self.assertTrue(value['cpl3_authority'])
        self.assertEqual(entry['completed_returns'], 1)

    def test_template_is_authoritative(self):
        good = self.good()
        template = (ROOT / 'scripts/expectations/blocking-ipc.transcript').read_text()
        changed = template.replace('event=wake subject=2', 'event=wake subject=1')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'changed.transcript'
            path.write_text(changed)
            with self.assertRaises(ValueError):
                D['extract'](good, P, path)

    def test_mutations(self):
        good = self.good()
        suffix = D['semantic_expectation'](P)
        mutations = [
            good + suffix,
            good[:-1],
            good.replace(D['READY'], b''),
            good.replace(b'cpl3-authority=1', b'cpl3-authority=0'),
            good.replace(b'event=block subject=2', b'event=block subject=1'),
            good.replace(b'event=wake subject=2', b'event=wake subject=1'),
            good.replace(b'vector=14 error=5', b'vector=14 error=4'),
            good.replace(b'direction=out length=4', b'direction=out length=3'),
            good.replace(b'canaries=preserved', b'canaries=changed'),
            good.replace(b'status=PASS blocks=1', b'status=FAIL blocks=1'),
            good.replace(P['10/FINAL'].encode(), P['10/IPC'].encode(), 1),
            good[:-len(suffix)] + b'!C6\n' + suffix,
            good[:-len(suffix)] +
                P['FINAL'].encode() + b' status=FAIL reason=forged-prefix\n' + suffix,
        ]
        for value in mutations:
            with self.subTest(value=value[-160:]), self.assertRaises(ValueError):
                D['extract'](value, P)

    def test_malformed_template(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'bad.transcript'
            path.write_text('@10/IPC@ event=enter subject=2\nBAD\n')
            with self.assertRaises(ValueError):
                D['semantic_expectation'](P, path)

    def test_protected_structured_terminal(self):
        digest = 'b' * 64
        prefix = (b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
                  b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
                  b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD sha256=' +
                  digest.encode() + b'\n')
        mode = X['R']['EXPECTED'][:-len(X['R']['EXPECTED_KERNEL'])]
        raw = self.good()
        terminal = (P['10/FINAL'].encode() +
                    b' status=PASS blocks=1 wakes=1 deliveries=1\n')
        events = [
            {'hex': prefix.hex(), 'elapsed': 1},
            {'hex': (mode + raw).hex(), 'elapsed': 3},
            {'hex': b'firmware\n'.hex(), 'elapsed': 38},
            {'hex': (b'LEANOS-LAB/1 DEFAULT request=none\n' +
                     X['R']['CHAIN']).hex(), 'elapsed': 39},
        ]
        expected, extracted = X['R']['cpu_diagnostic_bytes'](
            events, P, False, terminal)
        self.assertEqual(extracted, raw)
        result = X['R']['classify_protected'](
            events, digest, expected, P['BOOT'].encode(),
            structured_terminal=True, quiet_range=(30, 100))
        self.assertTrue(result['watchdog_protected'])
        self.assertEqual(result['quiet_seconds'], 35)


if __name__ == '__main__':
    unittest.main()
