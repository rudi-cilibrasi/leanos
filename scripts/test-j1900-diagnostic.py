#!/usr/bin/env python3
"""Reject forged CPU/MSR diagnostic captures using actual generated-C replay."""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('diagnostic', ROOT / 'scripts/check-j1900-diagnostic.py')
diagnostic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostic)
parser = argparse.ArgumentParser()
parser.add_argument('--replay', type=Path, default=ROOT / 'build/j1900-cpu-host/host')
args, remaining = parser.parse_known_args()
REPLAY = args.replay.resolve()
PROTOCOL_PATH = ROOT / 'build/boundary-abi/serial-protocol.tsv'
PROTOCOL = diagnostic.load_protocol(PROTOCOL_PATH)
rows = (ROOT / 'hardware/cpu-corpus/qotom-j1900-20260909/cpu-0.tsv').read_text().splitlines()[1:]
CPU = [1, 31] + [int(word, 16) for row in rows for word in row.split('\t')[2:]]
MSRS = [0xd00] + [0] * 7


def capture(cpu=None, msrs=None, selected=65536, readback=1):
    cpu = CPU if cpu is None else cpu
    msrs = MSRS if msrs is None else msrs
    lines = [PROTOCOL['BOOT'] + ' target=qotom-j1900-candidate phase=cpu-diagnostic platform-admitted=0 cpl3=0',
             PROTOCOL['CPU'] + ' profile=j1900-cpu-v1 codec=1 width=22 words='
             + ','.join(map(str, cpu)) + ' selection=' + str(selected)]
    if selected == 65536:
        lines.append(PROTOCOL['CONTROL'] + ' profile=j1900-cpu-v1 codec=1 width=8 words='
                     + ','.join(map(str, msrs)) + ' readback=' + str(readback))
    reason = ('j1900-cpu-profile' if selected != 65536 else
              'qotom-platform-pending' if readback else 'j1900-msr-readback')
    return ('\n'.join(lines + [PROTOCOL['FINAL'] + ' status=FAIL reason=' + reason]) + '\n').encode()


class DiagnosticTests(unittest.TestCase):
    def classify(self, raw):
        return diagnostic.classify(raw, PROTOCOL, REPLAY)

    def test_valid_diagnostic_never_authorizes_platform(self):
        raw = capture()
        result = self.classify(raw)
        self.assertEqual(result['cpu_selection'], 65536)
        self.assertEqual(result['msr_readback'], 1)
        self.assertEqual(result['capture_sha256'], hashlib.sha256(raw).hexdigest())
        self.assertFalse(result['platform_admitted'])
        self.assertFalse(result['cpl3_authorized'])

    def test_raw_cpu_changes_cannot_keep_claimed_success(self):
        for slot, bit in ((0, 1), (1, 0), (3, 0), (6, 0), (9, 5), (11, 7), (21, 20)):
            with self.subTest(slot=slot):
                words = list(CPU)
                words[slot] ^= 1 << bit
                with self.assertRaises(diagnostic.DiagnosticError):
                    self.classify(capture(cpu=words))

    def test_cpu_rejection_replays_without_readback(self):
        words = list(CPU)
        words[6] ^= 1
        result = self.classify(capture(cpu=words, selected=6))
        self.assertEqual(result['terminal_reason'], 'j1900-cpu-profile')
        self.assertIsNone(result['msr_readback'])
        forged = capture(cpu=words, selected=6).splitlines()
        forged.insert(2, capture().splitlines()[2])
        with self.assertRaises(diagnostic.DiagnosticError):
            self.classify(b'\n'.join(forged) + b'\n')

    def test_every_msr_high_bit_cannot_keep_claimed_success(self):
        for slot in range(8):
            with self.subTest(slot=slot):
                words = list(MSRS)
                words[slot] ^= 1 << 63
                with self.assertRaises(diagnostic.DiagnosticError):
                    self.classify(capture(msrs=words))
                result = self.classify(capture(msrs=words, readback=0))
                self.assertEqual(result['terminal_reason'], 'j1900-msr-readback')

    def test_malformed_and_reordered_records(self):
        raw = capture()
        lines = raw.splitlines(keepends=True)
        for malformed in (
            b'', raw[:-1], raw + b'\n', raw + lines[-1], b'x' * 4097,
            raw.replace(b'\n', b'\r\n'), raw + b'\x00', raw + b'\x1b',
            b'\xff' + raw, b''.join(lines[:-1]), b''.join(lines[:2] + lines[3:]),
            b''.join([lines[0], lines[2], lines[1], lines[3]]),
            raw.replace(b'platform-admitted=0', b'platform-admitted=1'),
            raw.replace(b'cpl3=0', b'cpl3=1'), raw.replace(b'status=FAIL', b'status=PASS'),
            raw.replace(b'profile=j1900-cpu-v1', b'profile=q35'),
            raw.replace(b'words=1,31,', b'words=01,31,'),
            raw.replace(b'selection=65536', b'selection=065536'),
            raw.replace(b'width=22', b'width=21'),
            raw.replace(b'readback=1', b'readback=0'),
            raw.replace(b'qotom-platform-pending', b'dma-identity'),
        ):
            with self.subTest(raw=malformed[:80]):
                with self.assertRaises(diagnostic.DiagnosticError):
                    self.classify(malformed)

    def test_capture_word_widths(self):
        cpu = list(CPU)
        cpu[2] = 1 << 32
        msrs = list(MSRS)
        msrs[1] = 1 << 64
        for raw in (capture(cpu=cpu), capture(msrs=msrs)):
            with self.assertRaises(diagnostic.DiagnosticError):
                self.classify(raw)

    def test_native_cli_rejects_malformed_input(self):
        for bad in ('', '-1', '+1', '00', '0x1', str(1 << 64), '1;exit', '1\n'):
            with self.subTest(word=bad):
                result = subprocess.run([str(REPLAY), 'msr', bad, *(['0'] * 7)],
                                        capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 2)
        self.assertEqual(diagnostic.replay_words(REPLAY, 'msr', [(1 << 64) - 1] + [0] * 7), 0)
        for extra in ([], ['unknown'], ['cpu', '1'], ['msr'] + ['0'] * 9):
            if not extra:
                continue  # No arguments intentionally runs the fixed corpus.
            result = subprocess.run([str(REPLAY), *extra], capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 2)

    def test_protocol_must_have_unique_required_identities(self):
        text = PROTOCOL_PATH.read_text()
        cpu = next(line for line in text.splitlines() if line.startswith('record\t24\tCPU\t'))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'protocol.tsv'
            for changed in (text + cpu + '\n', text.replace(cpu + '\n', '')):
                path.write_text(changed)
                with self.assertRaises(diagnostic.DiagnosticError):
                    diagnostic.load_protocol(path)


if __name__ == '__main__':
    unittest.main(argv=[__file__, *remaining])
