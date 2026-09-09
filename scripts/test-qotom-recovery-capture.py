#!/usr/bin/env python3
"""Negative fixtures for the separate lab recovery trace classifier."""
import importlib.util
import hashlib
import json
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('lab', Path(__file__).with_name('run-qotom-recovery-lab.py'))
lab = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lab)


def event(data, elapsed):
    return {'hex': data.hex(), 'elapsed': elapsed}


class CaptureTests(unittest.TestCase):
    def fixture(self):
        return [event(b'firmware\n', 1), event(lab.EXPECTED[:40], 2),
                event(lab.EXPECTED[40:], 3), event(b'firmware\n', 37),
                event(lab.CHAIN + b'hd1\n', 38)]

    def test_complete_recovery(self):
        result = lab.classify(self.fixture())
        self.assertEqual(result['quiet_seconds'], 34)
        self.assertEqual(result['scenario'], 'expected-dma-identity-rejection')

    def test_retained_physical_observations(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        cycles = sorted(root.glob('cycle-*'))
        self.assertEqual(len(cycles), 3)
        for cycle in cycles:
            events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
            raw = (cycle / 'serial.raw').read_bytes()
            self.assertEqual(raw, b''.join(bytes.fromhex(e['hex']) for e in events))
            computed = lab.classify(events)
            recorded = json.loads((cycle / 'result.json').read_text())
            for key in ('scenario', 'quiet_seconds', 'raw_sha256'):
                self.assertEqual(computed[key], recorded[key])
            self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
            self.assertTrue(recorded['request_consumed'])
            self.assertFalse(recorded['hang_recovery'])

    def test_failure_mutations(self):
        valid = self.fixture()
        mutations = {
            'earlier kernel output': [event(b'LEANOS/4 PROBE unexpected\n', 0)] + valid,
            'nonmonotonic time': valid[:3] + [event(b'firmware\n', 2), valid[-1]],
            'wrong reason': [event(lab.EXPECTED.replace(b'dma-identity', b'other'), 3)] + valid[3:],
            'false success': [event(lab.EXPECTED.replace(b'status=FAIL', b'status=PASS'), 3)] + valid[3:],
            'partial trace': [event(lab.EXPECTED[:-2], 3)] + valid[3:],
            'extra terminal': valid[:3] + [event(b'LEANOS/3 FINAL status=PASS\n', 4)] + valid[3:],
            'early reboot': valid[:3] + [event(b'firmware\n', 4), valid[-1]],
            'extra same chunk': [event(lab.EXPECTED + b'extra', 3)] + valid[3:],
            'missing chain': valid[:-1],
            'boot loop': valid + [event(b'LEANOS-LAB/1 SELECT leanos consumed=1\n', 40)],
            'post-terminal kernel output': valid + [event(b'LEANOS/4 PROBE unexpected\n', 40)],
        }
        for name, events in mutations.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                lab.classify(events)


if __name__ == '__main__':
    unittest.main()
