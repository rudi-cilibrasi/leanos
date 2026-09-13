#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
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
        self.assertEqual(value['platform_profile'], 'qotom-j1900-clbtm210-v2')
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
            good.replace(D['PLATFORM'], b''),
            good.replace(b'qotom-j1900-clbtm210-v2', b'qotom-j1900-clbtm210-v1'),
            good.replace(b'vtd=not-applicable', b'vtd=PASS'),
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

    def test_retained_platform_admission_capture(self):
        capture = (ROOT / 'hardware/lab/observations/'
                   'qotom-platform-admission-20260913')
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(
                hashlib.sha256((capture / name).read_bytes()).hexdigest(), digest)
        self.assertFalse(manifest['source_dirty'])
        self.assertEqual(manifest['source_revision'],
                         'c01cdc0a8831ccdbfb53049bbb695a040fd4c5de')
        self.assertEqual(manifest['elf_sha256'],
                         '2ca33caa063698c1648fbc630c27d8c9ccc46031553ef479de881b792b51e9e5')
        raw = (capture / 'cycle-1/serial.raw').read_bytes()
        terminal = (P['10/FINAL'].encode() +
                    b' status=PASS blocks=1 wakes=1 deliveries=1\n')
        self.assertEqual(raw.count(terminal), 1)
        end = raw.index(terminal) + len(terminal)
        _, value, entry = D['extract'](raw[:end], P)
        self.assertEqual(value['platform_profile'],
                         'qotom-j1900-clbtm210-v2')
        self.assertEqual(value['status'], 'PASS')
        self.assertEqual(entry['completed_returns'], 1)
        recovery = json.loads((capture / 'cycle-1/recovery.json').read_text())
        self.assertTrue(recovery['request_consumed'])
        self.assertEqual(recovery['recovery'], 'freebsd-ssh-restored')


if __name__ == '__main__':
    unittest.main()
