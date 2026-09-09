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
    def test_retained_protected_cycles(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-protected-normal-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        previous = None
        for cycle in sorted(root.glob('cycle-*')):
            recorded = json.loads((cycle / 'result.json').read_text())
            events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
            self.assertEqual((cycle / 'serial.raw').read_bytes(), b''.join(bytes.fromhex(e['hex']) for e in events))
            for key, value in lab.classify_protected(events, recorded['elf_sha256']).items():
                if key != 'recovery':
                    self.assertEqual(value, recorded[key], key)
            self.assertTrue(recorded['request_consumed'] and recorded['hang_recovery'])
            self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
            if previous is not None:
                self.assertEqual(previous, recorded['freebsd_boot_before'])
            previous = recorded['freebsd_boot_after']
        self.assertEqual(len(list(root.glob('cycle-*'))), 3)

    def test_protected_normal_capture(self):
        digest = 'a' * 64
        prefix = (b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
                  b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
                  b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD\n\rsha256=' + b'a' * 30 + b'\n\r' + b'a' * 34 + b'\n')
        default = b'LEANOS-LAB/1 DEFAULT request=none\n'
        valid = [event(prefix, 1), event(lab.EXPECTED, 3), event(b'firmware\n', 37), event(default + lab.CHAIN, 38)]
        self.assertTrue(lab.classify_protected(valid, digest)['watchdog_protected'])
        for bad in (valid[1:], valid + [event(prefix, 39)],
                    [event(prefix.replace(b'ARMED ticks=120', b'ARM-REJECTED'), 1), *valid[1:]],
                    [*valid[:2], event(b'firmware', 120), event(default + lab.CHAIN, 125)],
                    [*valid[:3], event(lab.CHAIN, 38)], valid + [event(b'WATCHDOG-LOAD-FAILED', 39)],
                    [valid[0], event(lab.EXPECTED.replace(b'dma-identity', b'other'), 3), *valid[2:]]):
            with self.subTest(events=bad), self.assertRaises(ValueError):
                lab.classify_protected(bad, digest)
        with self.assertRaises(ValueError):
            lab.classify_protected(valid, 'b' * 64)

    def test_retained_kernel_watchdog(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-kernel-watchdog-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        events = [json.loads(line) for line in (root / 'events.jsonl').read_text().splitlines()]
        self.assertEqual((root / 'serial.raw').read_bytes(), b''.join(bytes.fromhex(e['hex']) for e in events))
        recorded = json.loads((root / 'result.json').read_text())
        for key, value in lab.classify_watchdog(events, recorded['kernel_sha256']).items():
            if key != 'recovery':
                self.assertEqual(value, recorded[key], key)
        self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
        self.assertTrue(recorded['request_consumed'])
        self.assertTrue(recorded['kernel_hang_recovery'])

    def test_kernel_watchdog_capture(self):
        digest = 'a' * 64
        accepted = b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
        armed = b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
        load = b'LEANOS-LAB/1 WATCHDOG-KERNEL-LOAD sha256=' + digest.encode() + b'\n'
        hang = b'LEANOS-LAB/1 KERNEL-HANG stage=before-boot-record interrupts=disabled\n'
        recovery = b'LEANOS-LAB/1 DEFAULT request=none\n' + lab.CHAIN
        valid = [event(accepted + armed, 14), event(load + hang, 16), event(b'firmware', 135), event(recovery, 142)]
        result = lab.classify_watchdog(valid, digest)
        self.assertTrue(result['kernel_hang_recovery'])
        self.assertEqual(result['kernel_quiet_seconds'], 119)
        wrapped = load.replace(b' sha256=', b'\n\rsha256=').replace(digest.encode(), b'a' * 30 + b'\n\r' + b'a' * 34)
        self.assertTrue(lab.classify_watchdog([valid[0], event(wrapped + hang, 16), *valid[2:]], digest)['kernel_hang_recovery'])
        self.assertEqual(lab.watchdog_request('0\n2026-09-09T20:05:00\n', 'watchdog-kernel-' + digest),
                         'watchdog-kernel-' + digest + '-2026-9-9-20-5')
        for bad in (valid[:1] + valid[2:], valid + [event(hang, 150)],
                    [valid[0], event(load + hang + b'extra', 16), *valid[2:]],
                    [*valid[:2], event(b'extra', 20), *valid[2:]],
                    [valid[0], event(load.replace(digest.encode(), b'b' * 64) + hang, 16), *valid[2:]]):
            with self.subTest(events=bad), self.assertRaises(ValueError):
                lab.classify_watchdog(bad, digest)
        with self.assertRaises(ValueError):
            lab.classify_watchdog(valid)

    def test_retained_loader_watchdog(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-dated-watchdog-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        events = [json.loads(line) for line in (root / 'events.jsonl').read_text().splitlines()]
        self.assertEqual((root / 'serial.raw').read_bytes(), b''.join(bytes.fromhex(e['hex']) for e in events))
        recorded = json.loads((root / 'result.json').read_text())
        for key, value in lab.classify_watchdog(events).items():
            if key != 'recovery':
                self.assertEqual(value, recorded[key], key)
        self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
        self.assertTrue(recorded['request_consumed'])
        self.assertFalse(recorded['kernel_hang_recovery'])

    def test_watchdog_request_clock(self):
        self.assertEqual(lab.watchdog_request('0\n2026-09-09T20:05:25\n'), 'watchdog-test-2026-9-9-20-5')
        self.assertIsNone(lab.watchdog_request('0\n2026-09-09T20:05:26\n'))
        for clock in ('1\n2026-09-09T20:05:00\n', '0\n2000-09-09T20:05:00\n',
                      '0\ninvalid\n', '0\n2026-09-09T20:05:00\nextra\n'):
            with self.subTest(clock=clock), self.assertRaises(ValueError):
                lab.watchdog_request(clock)

    def test_watchdog_reset_classification(self):
        accepted = b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n\r'
        armed = b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n\r'
        expired = b'LEANOS-LAB/1 WATCHDOG-WINDOW expired-or-invalid=1 fallback=freebsd\n\r'
        valid = [event(accepted + armed, 14), event(b'firmware\n', 135),
                 event(expired + lab.CHAIN + b'hd1\n\r', 142)]
        result = lab.classify_watchdog(valid)
        self.assertEqual(result['arm_to_recovery_boot_seconds'], 128)
        self.assertEqual(result['recovery_guard'], 'expired-token')
        consumed = [*valid[:2], event(b'LEANOS-LAB/1 DEFAULT request=none\n' + lab.CHAIN, 142)]
        self.assertEqual(lab.classify_watchdog(consumed)['recovery_guard'], 'consumed-request')
        self.assertTrue(result['loader_hang_recovery'])
        self.assertFalse(result['kernel_hang_recovery'])
        mutations = [valid[:2], valid + [event(armed, 145)],
                     valid[:2] + [event(expired + lab.CHAIN, 30)],
                     valid[:2] + [event(expired + lab.CHAIN, 320)],
                     valid + [event(b'WATCHDOG-NO-RESET', 150)],
                     valid + [event(lab.EXPECTED, 150)],
                     [event(expired + lab.CHAIN, 1), event(accepted + armed, 14)],
                     [valid[0], event(b'firmware\n', 1), valid[2]]]
        for events in mutations:
            with self.subTest(events=events), self.assertRaises(ValueError):
                lab.classify_watchdog(events)

    def test_rtc_probe_and_failures(self):
        raw = (b'LEANOS-LAB/1 RTC-BEGIN 2026-9-9-23-59-30\r\n'
               b'LEANOS-LAB/1 RTC-CURRENT accepted=1\r\n'
               b'LEANOS-LAB/1 RTC-END 2026-9-10-0-0-35\r\n'
               b'LEANOS-LAB/1 RTC-EXPIRED rejected=1\r\n' + lab.CHAIN + b'hd1\r\n')
        self.assertEqual(lab.classify_rtc([event(raw, 80)])['rtc_advance_seconds'], 65)
        for newline in (b'\n', b'\n\r'):
            self.assertEqual(lab.classify_rtc([event(raw.replace(b'\r\n', newline), 80)])['rtc_advance_seconds'], 65)
        for bad in (raw + raw, raw.replace(b'accepted=1', b'accepted=0'),
                    raw.replace(b'rejected=1', b'rejected=0'),
                    raw.replace(b'2026-9-10-0-0-35', b'2026-9-9-23-59-30'),
                    raw.replace(b'2026-9-10-0-0-35', b'2026-9-10-0-0-50'),
                    raw.replace(lab.CHAIN, b'no-chain'),
                    raw + b'WATCHDOG-ARMED', raw + lab.EXPECTED,
                    lab.CHAIN + b'hd1\n' + raw.split(lab.CHAIN)[0]):
            with self.subTest(raw=bad), self.assertRaises(ValueError):
                lab.classify_rtc([event(bad, 80)])

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
            'earlier kernel output': [event(lab.record(4, 'PROBE') + b' unexpected\n', 0)] + valid,
            'nonmonotonic time': valid[:3] + [event(b'firmware\n', 2), valid[-1]],
            'wrong reason': [event(lab.EXPECTED.replace(b'dma-identity', b'other'), 3)] + valid[3:],
            'false success': [event(lab.EXPECTED.replace(b'status=FAIL', b'status=PASS'), 3)] + valid[3:],
            'partial trace': [event(lab.EXPECTED[:-2], 3)] + valid[3:],
            'extra terminal': valid[:3] + [event(lab.record(3, 'FINAL') + b' status=PASS\n', 4)] + valid[3:],
            'early reboot': valid[:3] + [event(b'firmware\n', 4), valid[-1]],
            'extra same chunk': [event(lab.EXPECTED + b'extra', 3)] + valid[3:],
            'missing chain': valid[:-1],
            'boot loop': valid + [event(b'LEANOS-LAB/1 SELECT leanos consumed=1\n', 40)],
            'post-terminal kernel output': valid + [event(lab.record(4, 'PROBE') + b' unexpected\n', 40)],
        }
        for name, events in mutations.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                lab.classify(events)


if __name__ == '__main__':
    unittest.main()
