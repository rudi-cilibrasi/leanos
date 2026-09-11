#!/usr/bin/env python3
"""Exercise raw handoff transport boundaries and preserve malformed metadata."""
import json
import hashlib
from pathlib import Path
import runpy
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-handoff-capture.py'))


def transport(raw, status=0, address=4096, magic=0x36d76289):
    header = f'LEANOS-LAB/1 HANDOFF status={status} magic={magic} address={address} length={len(raw)} apic=0\n'
    chunks = ''.join(f'LEANOS-LAB/1 HANDOFF-DATA offset={i} hex={raw[i:i+64].hex()}\n'
                     for i in range(0, len(raw), 64))
    return (header + chunks + 'LEANOS-LAB/1 HANDOFF-END\n').encode()


def empty_handoff():
    return struct.pack('<IIII', 16, 0, 0, 8)


class HandoffTests(unittest.TestCase):
    def test_complete_and_rejected(self):
        raw = empty_handoff()
        data = transport(raw)
        consumed, decoded, metadata = D['parse_prefix'](data + b'next record\n')
        self.assertEqual(consumed, len(data))
        self.assertEqual(decoded, raw)
        self.assertTrue(metadata['tag_chain_valid'])
        self.assertFalse(metadata['platform_admitted'] or metadata['display_authorized'])
        _, decoded, metadata = D['parse_prefix'](transport(b'', status=1, address=0, magic=0))
        self.assertEqual(decoded, b'')
        self.assertEqual(metadata['status'], 1)

    def test_full_bound(self):
        # One unknown tag consumes all space before the final end tag.
        raw = struct.pack('<IIII', 65536, 0, 99, 65520) + bytes(65512) + struct.pack('<II', 0, 8)
        self.assertEqual(len(raw), 65536)
        data = transport(raw)
        consumed, decoded, report = D['parse_prefix'](data)
        self.assertLessEqual(consumed, D['MAX_TRANSPORT'])
        self.assertEqual(decoded, raw)
        self.assertTrue(report['tag_chain_valid'])

    def test_display_is_metadata_only(self):
        tag = struct.pack('<IIQIIIBBH', 8, 32, 0xb8000, 160, 80, 25, 16, 2, 0)
        raw = struct.pack('<II', 48, 0) + tag + struct.pack('<II', 0, 8)
        _, decoded, report = D['parse_prefix'](transport(raw))
        self.assertEqual(decoded, raw)
        self.assertEqual(report['tags'][0]['framebuffer']['address'], 0xb8000)
        self.assertFalse(report['display_authorized'])

    def test_malformed_tags_retained(self):
        for raw in (struct.pack('<IIII', 16, 1, 0, 8),
                    struct.pack('<IIII', 16, 0, 8, 0xffffffff),
                    struct.pack('<IIII', 16, 0, 0, 7)):
            _, decoded, report = D['parse_prefix'](transport(raw))
            self.assertEqual(decoded, raw)
            self.assertFalse(report['tag_chain_valid'])

    def test_transport_corruption(self):
        good = transport(empty_handoff())
        bad = [good[:-1], good.replace(b'offset=0', b'offset=1'),
               good.replace(b'hex=10', b'hex=1A'),
               good.replace(b'length=16', b'length=24'),
               good.replace(b'status=0', b'status=1'),
               good.replace(b'apic=0', b'apic=256'),
               good.replace(b'offset=0', b'offset=00'),
               good.replace(b'HANDOFF-END', b'HANDOFF-DATA'),
               transport(empty_handoff(), address=0x1000000-8),
               transport(empty_handoff(), address=4097),
               transport(empty_handoff(), magic=0)]
        for data in bad:
            with self.subTest(data=data), self.assertRaises(ValueError):
                D['parse_prefix'](data)

    def test_protected_recovery_integration(self):
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        capture = ROOT / 'hardware/lab/observations/qotom-pci-diagnostic-20260911'
        recorded = json.loads((capture / 'cycle-1/result.json').read_text())
        raw = (capture / 'cycle-1/serial.raw').read_bytes()
        mode = lab['EXPECTED'][:-len(lab['EXPECTED_KERNEL'])]
        extra = transport(empty_handoff())
        raw = raw.replace(mode, mode + extra)
        final = raw.index(b'LEANOS/3 FINAL')
        end = raw.index(b'\n', final) + 1
        events = [{'hex': raw[:end].hex(), 'elapsed': 1},
                  {'hex': raw[end:].hex(), 'elapsed': 36}]
        args = (events, recorded['elf_sha256'], capture / 'diagnostic-protocol.tsv',
                ROOT / 'build/j1900-cpu-host/host', ROOT / 'build/qotom-pci-inventory-host/host')
        result = lab['classify_cpu_protected'](*args, handoff=True)
        self.assertEqual(result['handoff']['length'], 16)
        self.assertTrue(result['watchdog_protected'])
        self.assertFalse(result['diagnostic']['platform_admitted'])
        with self.assertRaises(ValueError):
            lab['classify_cpu_protected'](*args)

    def test_retained_physical_handoff(self):
        capture = ROOT / 'hardware/lab/observations/qotom-grub-handoff-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(), digest, name)
        raw = (capture / 'cycle-1/serial.raw').read_bytes()
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        self.assertEqual(raw, b''.join(bytes.fromhex(e['hex']) for e in events))
        offset = raw.index(b'LEANOS-LAB/1 HANDOFF status=')
        _, binary, metadata = D['parse_prefix'](raw[offset:])
        self.assertEqual(binary, (capture / 'cycle-1/multiboot2.bin').read_bytes())
        self.assertEqual(metadata, json.loads((capture / 'cycle-1/handoff.json').read_text()))
        recorded = json.loads((capture / 'cycle-1/result.json').read_text())
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        result = lab['classify_cpu_protected'](
            events, recorded['elf_sha256'], capture / 'diagnostic-protocol.tsv',
            ROOT / 'build/j1900-cpu-host/host', ROOT / 'build/qotom-pci-inventory-host/host', True)
        self.assertEqual(result['handoff'], recorded['handoff'])
        self.assertEqual(result['diagnostic']['capture_sha256'], recorded['diagnostic']['capture_sha256'])
        self.assertFalse(result['diagnostic']['platform_admitted'])

    def test_native_read_bounds(self):
        source = r'''
#include <assert.h>
#include "boot_handoff_capture.h"
int main(void) {
    uint8_t header[8] = {16};
    uint32_t m = 0x36d76289u;
    assert(boot_handoff_capture_length(0, 4096, 0, 16) == 0);
    assert(boot_handoff_capture_length(m, 0, 0, 16) == 0);
    assert(boot_handoff_capture_length(m, 4097, 0, 16) == 0);
    assert(boot_handoff_capture_length(m, 0xfffffff8u, 0, 16) == 0);
    assert(boot_handoff_capture_length(m, 4096, 0, 7) == 0);
    assert(boot_handoff_capture_length(m, 4096, header, 8) == 0);
    uint8_t bytes[65536] = {16};
    assert(boot_handoff_capture_length(m, 4096, bytes, sizeof bytes) == 16);
    assert(boot_handoff_capture_length(m, 0x1000000u-8, bytes, sizeof bytes) == 0);
    assert(boot_handoff_capture_length(m, 0x1000000u-16, bytes, sizeof bytes) == 16);
    bytes[0] = 0; bytes[2] = 1;
    assert(boot_handoff_capture_length(m, 4096, bytes, sizeof bytes) == 65536);
    bytes[0] = 8;
    assert(boot_handoff_capture_length(m, 4096, bytes, sizeof bytes) == 0);
    bytes[0] = 15; bytes[2] = 0;
    assert(boot_handoff_capture_length(m, 4096, bytes, sizeof bytes) == 0);
    return 0;
}
'''
        with tempfile.TemporaryDirectory() as tmp:
            code = Path(tmp) / 'bounds.c'
            code.write_text(source)
            binary = Path(tmp) / 'bounds'
            subprocess.run(['gcc', '-std=c11', '-Wall', '-Wextra', '-Werror',
                            '-fsanitize=address,undefined', '-fno-pie', '-no-pie',
                            '-I', str(ROOT / 'include'), str(code), '-o', str(binary)], check=True)
            subprocess.run([str(binary)], check=True)


if __name__ == '__main__':
    unittest.main()
