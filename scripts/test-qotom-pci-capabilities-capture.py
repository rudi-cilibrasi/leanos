#!/usr/bin/env python3
"""Synthetic capability transport mutations, independent of image emitter."""
import runpy
from pathlib import Path
import unittest

extract = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-capabilities-capture.py')))['extract']
PROTOCOL = {'FINAL': 'LEANOS/3 FINAL', 'PCI-HEADER': 'LEANOS/25 PCI-HEADER'}
NATIVE = b'LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 status=0 index=0 count=16\n'
PENDING = b'LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending\n'
FAILURE = b'LEANOS/3 FINAL status=FAIL reason=qotom-pci-capabilities\n'


def fixture():
    headers = []
    caps = []
    for i in range(16):
        words = [0,i,0] + [0]*16
        words[3] = 0x12348086
        words[4] = 0x100000 if i == 0 else 0
        words[16] = 88 if i == 0 else 0
        headers.append(f'LEANOS/25 PCI-HEADER codec=1 index={i} width=19 words={",".join(map(str,words))}\n'.encode())
        caps.append(f'LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index={i} status=0 offset=0 count={2 if i == 0 else 0}\n'.encode())
        if i == 0:
            caps.extend([b'LEANOS-LAB/1 PCI-CAP index=0 slot=0 offset=88 raw=18441\n',
                         b'LEANOS-LAB/1 PCI-CAP index=0 slot=1 offset=72 raw=5\n'])
    prefix = b''.join(headers) + NATIVE
    return prefix, b''.join(caps)


class Capture(unittest.TestCase):
    def test_success(self):
        prefix, caps = fixture()
        projection, report = extract(prefix + caps + PENDING, PROTOCOL)
        self.assertEqual(projection, prefix + PENDING)
        self.assertEqual(len(report['functions']), 16)
        self.assertEqual(report['functions'][0]['headers'][1]['offset'], 72)
        self.assertFalse(report['dma_quarantine_established'])

    def test_mutations(self):
        prefix, caps = fixture()
        raw = prefix + caps + PENDING
        mutations = [raw.replace(b'offset=88 raw=18441', b'offset=84 raw=18441'),
            raw.replace(b'raw=5\n', b'raw=22533\n'), # cycle to 0x58
            raw.replace(b'raw=5\n', b'raw=255\n'),
            raw.replace(b'raw=5\n', b'raw=4294967296\n'),
            raw.replace(b'slot=1', b'slot=0'),
            raw.replace(b'count=2\n', b'count=1\n'),
            raw.replace(b'count=2\n', b'count=49\n'),
            raw.replace(b'index=0 status=0 offset=0 count=2', b'index=00 status=0 offset=0 count=2'),
            prefix + PENDING, raw + PENDING, raw[:-1],
            raw.replace(NATIVE, b''), raw.replace(NATIVE, NATIVE + NATIVE),
            raw.replace(PENDING, FAILURE), b'x'*131073 + b'\n']
        for mutated in mutations:
            with self.subTest(mutated=mutated[-100:]):
                with self.assertRaises(ValueError): extract(mutated, PROTOCOL)

    def test_failed_observation(self):
        prefix, _ = fixture()
        for status, offset in [(2,72),(3,52),(4,3),(5,88),(6,88)]:
            summary = f'LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index=0 status={status} offset={offset} count=0\n'.encode()
            projection, report = extract(prefix + summary + FAILURE, PROTOCOL)
            self.assertEqual(projection, prefix + PENDING)
            self.assertEqual(report['terminal_reason'], 'qotom-pci-capabilities')
            self.assertFalse(report['failed_reads_replayed'])
            for end in [PENDING, summary + FAILURE]:
                with self.assertRaises(ValueError): extract(prefix + summary + end, PROTOCOL)

    def test_impossible_failure(self):
        prefix, _ = fixture()
        for status, offset, count in [(1,0,0),(2,3,0),(3,72,0),(4,64,0),(5,0,0),(6,3,0),(2,72,1),(7,72,0)]:
            summary = f'LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index=0 status={status} offset={offset} count={count}\n'.encode()
            with self.assertRaises(ValueError): extract(prefix + summary + FAILURE, PROTOCOL)

    def test_earlier_rejection(self):
        raw = b'LEANOS/3 FINAL status=FAIL reason=qotom-native-inventory\n'
        self.assertEqual(extract(raw, PROTOCOL), (raw, None))


if __name__ == '__main__':
    unittest.main()
