#!/usr/bin/env python3
"""Offline regression fixtures; no physical host, serial adapter or ISO required."""
import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import pty
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('hardware', Path(__file__).with_name('hardware-evidence.py'))
hw = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(hw)
OBSERVATION = hw.HARDWARE / 'observations/qotom-20260909'
ROW = hw.profile('qotom-j1900-clbtm210-v1')
EXPECTED = ('\n'.join(ROW['expected_lines']) + '\n').encode()


class HardwareEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bundle = self.root / 'bundle'
        shutil.copytree(OBSERVATION, self.bundle)

    def metadata(self):
        return hw.read_json(self.bundle / 'bundle.json')

    def save(self, meta):
        hw.write_json(self.bundle / 'bundle.json', meta)

    def rehash(self):
        meta = self.metadata()
        meta['files'] = {name: hw.file_sha(self.bundle / name) for name in hw.PAYLOADS}
        self.save(meta)

    def install_transcript(self, raw):
        (self.bundle / 'serial.raw').write_bytes(raw)
        (self.bundle / 'serial.normalized').write_bytes(raw.replace(b'\r\n', b'\n'))
        events = [] if not raw else [{'elapsed_seconds': 30,
            'utc': '2026-09-09T15:55:19.117385+00:00', 'offset': 0,
            'length': len(raw), 'hex': raw.hex()}]
        (self.bundle / 'events.jsonl').write_text(''.join(json.dumps(x) + '\n' for x in events))
        self.rehash()

    def test_real_observation(self):
        result = hw.verify(self.bundle)
        self.assertEqual(result['classification'], 'exact-rejection')
        self.assertEqual(result['raw_sha256'], '3a0dde9ced8af3a10f91c9976e19e91d9e57fc1ffd60ef63598aba124250c4d6')
        self.assertGreater(result['quiet_seconds'], 150)
        self.assertFalse(result['artifacts_checked'])
        self.assertEqual(result['provenance'], 'imported-observation')

    def test_protocol_mutations_rechecked_after_rehash(self):
        cases = [(b'', 'silence-timeout'), (b'GRUB', 'no-leanos-protocol'),
            (EXPECTED[:-1], 'malformed-or-incomplete-protocol'),
            (EXPECTED.splitlines(keepends=True)[1] + EXPECTED.splitlines(keepends=True)[0],
             'malformed-or-incomplete-protocol'),
            (EXPECTED.replace(b'dma-identity', b'dma-inventory'), 'wrong-rejection'),
            (EXPECTED.replace(b'status=FAIL reason=dma-identity', b'status=PASS'), 'unexpected-success-or-cpl3'),
            (EXPECTED + b'\x00', 'post-terminal-bytes'),
            (EXPECTED + b'\n', 'post-terminal-bytes'),
            (b'BIOS\r\n' + EXPECTED.replace(b'\n', b'\r\n'), 'exact-rejection')]
        for name in ['ENTRY', 'ENTER', 'SYSCALL', 'TIMER', 'SWITCH', 'RESUME']:
            cases.append((EXPECTED.splitlines(keepends=True)[0] + EXPECTED.split(b' ', 1)[0] + f' {name} x\n'.encode()
                          + EXPECTED.splitlines(keepends=True)[1], 'unexpected-success-or-cpl3'))
        for raw, expected in cases:
            with self.subTest(raw=raw):
                self.install_transcript(raw)
                self.assertEqual(hw.verify(self.bundle)['classification'], expected)

    def test_schema_and_manifest_mutations(self):
        original = self.metadata()
        mutations = [lambda m: m.update(tier='pr'), lambda m: m.update(extra=True),
            lambda m: m.update(scenario='any-pc'), lambda m: m.update(source_revision='0' * 40),
            lambda m: m['capture'].update(baud=115200), lambda m: m['capture'].update(timeout_seconds=5),
            lambda m: m['capture'].update(duration_seconds=float('nan')),
            lambda m: m['artifacts'].update(iso='0' * 64),
            lambda m: m['files'].update({'../outside': '0' * 64}),
            lambda m: m['capture'].update(flow_control='rtscts'),
            lambda m: m['capture'].update(started_utc='2026-09-09T15:54:49'),
            lambda m: m['provenance'].update(kind='qemu')]
        for mutate in mutations:
            meta = copy.deepcopy(original)
            mutate(meta)
            self.save(meta)
            with self.subTest(meta=meta), self.assertRaises(hw.EvidenceError):
                hw.verify(self.bundle)
        self.save(original)

    def test_profile_cannot_override_expected_reason(self):
        value = hw.read_json(self.bundle / 'profile.json')
        value['expected_lines'][-1] = ROW['expected_lines'][-1].replace('dma-identity', 'anything')
        hw.write_json(self.bundle / 'profile.json', value)
        self.rehash()
        with self.assertRaisesRegex(hw.EvidenceError, 'profile differs'):
            hw.verify(self.bundle)

    def test_missing_and_corrupt_files(self):
        p = self.bundle / 'serial.raw'
        original = p.read_bytes()
        p.write_bytes(original + b'x')
        with self.assertRaisesRegex(hw.EvidenceError, 'hash mismatch'):
            hw.verify(self.bundle)
        p.unlink()
        with self.assertRaises(OSError):
            hw.verify(self.bundle)

    def test_bad_normalization_and_event_stream(self):
        original = (self.bundle / 'events.jsonl').read_text()
        for field, value in [('offset', 100), ('length', 100), ('elapsed_seconds', -1),
                             ('elapsed_seconds', 190), ('hex', 'zz'),
                             ('utc', '2026-09-10T00:00:00+00:00')]:
            events = [json.loads(x) for x in original.splitlines()]
            events[0][field] = value
            (self.bundle / 'events.jsonl').write_text(''.join(json.dumps(x) + '\n' for x in events))
            self.rehash()
            with self.subTest(field=field, value=value), self.assertRaises(hw.EvidenceError):
                hw.verify(self.bundle)
        (self.bundle / 'events.jsonl').write_text(original)
        (self.bundle / 'serial.normalized').write_bytes(EXPECTED)
        self.rehash()
        with self.assertRaisesRegex(hw.EvidenceError, 'normalized transcript'):
            hw.verify(self.bundle)

    def test_capture_timeout_is_not_pass(self):
        meta = self.metadata()
        meta['capture'].update(finished_utc='2026-09-09T15:56:49.117385+00:00', duration_seconds=120)
        self.save(meta)
        with self.assertRaises(hw.EvidenceError) as ctx:
            hw.verify(self.bundle)
        self.assertEqual(ctx.exception.category, 'capture-timeout')

    def test_terminal_requires_quiet_time(self):
        self.install_transcript(EXPECTED)
        event = json.loads((self.bundle / 'events.jsonl').read_text())
        event.update(elapsed_seconds=175, utc='2026-09-09T15:57:44.117385+00:00')
        (self.bundle / 'events.jsonl').write_text(json.dumps(event) + '\n')
        self.rehash()
        self.assertEqual(hw.verify(self.bundle)['classification'], 'terminal-observation-timeout')

    def test_reset_after_output_rejects(self):
        meta = self.metadata()
        meta['capture']['reset_declared_utc'] = '2026-09-09T15:55:20+00:00'
        self.save(meta)
        with self.assertRaises(hw.EvidenceError) as ctx:
            hw.verify(self.bundle)
        self.assertEqual(ctx.exception.category, 'reset-not-observed')

    def test_recorded_result_is_not_trusted(self):
        hw.write_json(self.bundle / 'result.json', {'classification': 'exact-rejection'})
        self.install_transcript(b'GRUB')
        self.assertEqual(hw.verify(self.bundle)['classification'], 'no-leanos-protocol')

    def test_duplicate_json_and_symlink_reject(self):
        p = self.bundle / 'bundle.json'
        p.write_text('{"schema":"a","schema":"b"}')
        with self.assertRaisesRegex(hw.EvidenceError, 'duplicate JSON key'):
            hw.verify(self.bundle)
        p.unlink()
        p.symlink_to(OBSERVATION / 'bundle.json')
        with self.assertRaisesRegex(hw.EvidenceError, 'plain files'):
            hw.verify(self.bundle)

    def test_artifact_and_source_mismatch(self):
        fake = self.root / 'fake.iso'
        fake.write_bytes(b'not an image')
        with self.assertRaises(hw.EvidenceError) as ctx:
            hw.artifact_check(ROW, fake, fake, ROW['source_revision'])
        self.assertEqual(ctx.exception.category, 'artifact-mismatch')
        with self.assertRaises(hw.EvidenceError) as ctx:
            hw.artifact_check(ROW, fake, fake, '0' * 40)
        self.assertEqual(ctx.exception.category, 'source-mismatch')

    def capture_args(self):
        iso = self.root / 'iso'; iso.write_bytes(b'fixture iso')
        elf = self.root / 'elf'; elf.write_bytes(b'fixture elf')
        tools = self.root / 'tools'; tools.write_bytes(b'fixture tools')
        row = copy.deepcopy(ROW)
        row['artifacts'] = {'iso': hw.file_sha(iso), 'elf': hw.file_sha(elf), 'toolchain': hw.file_sha(tools), 'protocol': ROW['artifacts']['protocol']}
        row['timeout_seconds'] = 11
        args = argparse.Namespace(scenario=row['id'], iso=iso, elf=elf, toolchain=tools,
            protocol=OBSERVATION / 'protocol.tsv', source_revision=row['source_revision'], operator='test fixture',
            output=self.root / 'live', device=str(self.root / 'missing'))
        return args, row

    def test_missing_serial_device(self):
        args, row = self.capture_args()
        with patch.object(hw, 'profile', return_value=row), self.assertRaises(OSError):
            hw.capture(args)

    def test_existing_output_not_overwritten(self):
        args, row = self.capture_args()
        args.output.mkdir(); (args.output / 'sentinel').write_text('keep')
        with patch.object(hw, 'profile', return_value=row), self.assertRaises(FileExistsError):
            hw.capture(args)
        self.assertEqual((args.output / 'sentinel').read_text(), 'keep')
        self.assertFalse(getattr(args, 'capture_created', False))

    def test_live_capture_through_pty(self):
        args, row = self.capture_args()
        master, slave = pty.openpty()
        self.addCleanup(os.close, master); self.addCleanup(os.close, slave)
        args.device = os.ttyname(slave)
        real_select = hw.select.select
        def deliver(read, write, error, timeout):
            hw.write_json(args.output / 'reset.json', {'declared_utc': '2026-09-09T00:00:00.5+00:00'})
            os.write(master, EXPECTED)
            return real_select(read, write, error, 1)
        with patch.object(hw, 'profile', return_value=row), \
                patch.object(hw.time, 'monotonic', side_effect=[0, 0, 0, 1, 11, 11]), \
                patch.object(hw, 'utc', side_effect=['2026-09-09T00:00:00+00:00',
                    '2026-09-09T00:00:01+00:00', '2026-09-09T00:00:11+00:00']), \
                patch.object(hw.select, 'select', side_effect=deliver):
            result = hw.capture(args)
        self.assertEqual(result['classification'], 'exact-rejection')
        self.assertEqual((args.output / 'serial.raw').read_bytes(), EXPECTED)

    def test_cli_verify_without_hardware(self):
        result = subprocess.run([sys.executable, str(Path(hw.__file__)), 'verify', str(self.bundle)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertEqual(json.loads(result.stdout)['classification'], 'exact-rejection')


if __name__ == '__main__':
    unittest.main()
