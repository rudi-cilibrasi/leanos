#!/usr/bin/env python3
import runpy
import json
import struct
from pathlib import Path
import unittest

D = runpy.run_path(str(Path(__file__).with_name('check-qotom-acpi-capture.py')))
FINAL = b'FINAL status=FAIL reason=qotom-platform-pending\n'


def checksum(data, offset):
    result = bytearray(data); result[offset] = 0; result[offset] = -sum(result) & 255
    return bytes(result)


def table(signature, payload=b''):
    raw = bytearray(36) + payload; raw[:4] = signature
    struct.pack_into('<I', raw, 4, len(raw))
    return checksum(raw, 9)


def handoff():
    rsdp = bytearray(36); rsdp[:8] = b'RSD PTR '; rsdp[15] = 2
    struct.pack_into('<I', rsdp, 20, 36); struct.pack_into('<Q', rsdp, 24, 65536)
    rsdp[8] = -sum(rsdp[:20]) & 255; rsdp[32] = -sum(rsdp) & 255
    tag = struct.pack('<II', 15, 44) + rsdp + bytes(4)
    return struct.pack('<II', 64, 0) + tag + struct.pack('<II', 0, 8)


def capture(root=None, child=None, child_address=131072):
    root = table(b'XSDT', struct.pack('<Q', 131072)) if root is None else root
    child = table(b'APIC', bytes(8)) if child is None else child
    lines = [b'CPU\n', b'LEANOS-LAB/1 ACPI-BEGIN root-kind=2 root-address=65536 tables=1\n']
    for index, (address, raw) in enumerate(((65536, root), (child_address, child))):
        lines.append(f'LEANOS-LAB/1 ACPI-TABLE index={index} address={address} length={len(raw)}\n'.encode())
        for offset in range(0, len(raw), 64):
            lines.append(f'LEANOS-LAB/1 ACPI-DATA offset={offset} hex={raw[offset:offset+64].hex()}\n'.encode())
    return b''.join(lines) + b'LEANOS-LAB/1 ACPI-END\n' + FINAL


class ACPITests(unittest.TestCase):
    def test_complete_root_set(self):
        clean, report, files = D['extract'](capture(), handoff())
        self.assertEqual(clean, b'CPU\n' + FINAL)
        self.assertEqual(len(report['tables']), 2)
        self.assertEqual(files['0000000000020000.bin'], table(b'APIC', bytes(8)))
        self.assertFalse(report['platform_admitted'])

    def test_root_and_checksum_rejections(self):
        bad_child = bytearray(table(b'APIC', bytes(8))); bad_child[-1] ^= 1
        for raw in (capture(child=bad_child), capture(child_address=196608),
                    capture(child_address=65536), capture(root=table(b'RSDT', struct.pack('<Q', 131072))),
                    capture(root=table(b'XSDT', struct.pack('<Q', 196608)))):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                D['extract'](raw, handoff())

    def test_transport_rejections(self):
        good = capture()
        for old, new in ((b'index=1', b'index=2'), (b'offset=0', b'offset=1'),
                         (b'tables=1', b'tables=0'), (b'length=44', b'length=65536'),
                         (b'ACPI-END', b'ACPI-STOP'), (b'root-address=65536', b'root-address=65537')):
            with self.subTest(old=old), self.assertRaises(ValueError):
                D['extract'](good.replace(old, new), handoff())
        with self.assertRaises(ValueError):
            D['extract'](good + good, handoff())

    def test_requires_root_provenance(self):
        bad = bytearray(handoff()); bad[16 + 8] ^= 1
        with self.assertRaises(ValueError): D['extract'](capture(), bytes(bad))
        with self.assertRaises(ValueError): D['extract'](capture(), bytes(16))

    def test_protected_recovery_binding(self):
        root = Path(__file__).resolve().parents[1]
        lab = runpy.run_path(str(root / 'scripts/run-qotom-recovery-lab.py'))
        helpers = runpy.run_path(str(root / 'scripts/test-qotom-handoff-capture.py'))
        directory = root / 'hardware/lab/observations/qotom-pci-diagnostic-20260911'
        recorded = json.loads((directory / 'cycle-1/result.json').read_text())
        raw = (directory / 'cycle-1/serial.raw').read_bytes()
        mode = lab['EXPECTED'][:-len(lab['EXPECTED_KERNEL'])]
        raw = raw.replace(mode, mode + helpers['transport'](handoff()))
        protocol = lab['cpu_replay_module'](True).load_protocol(
            directory / 'diagnostic-protocol.tsv')
        terminal = protocol['FINAL'].encode('ascii')
        begin = raw.index(terminal)
        raw = raw[:begin] + capture()[4:-len(FINAL)] + raw[begin:]
        final = raw.index(terminal)
        end = raw.index(b'\n', final) + 1
        events = [{'hex': raw[:end].hex(), 'elapsed': 1}, {'hex': raw[end:].hex(), 'elapsed': 36}]
        args = (events, recorded['elf_sha256'], directory / 'diagnostic-protocol.tsv',
                root / 'build/j1900-cpu-host/host', root / 'build/qotom-pci-inventory-host/host')
        result = lab['classify_cpu_protected'](*args, handoff=True, acpi=True)
        self.assertEqual(len(result['acpi']['tables']), 2)
        self.assertTrue(result['watchdog_protected'])
        self.assertFalse(result['diagnostic']['platform_admitted'])
        with self.assertRaises(ValueError):
            lab['classify_cpu_protected'](*args, handoff=True)

    def test_retained_native_tables(self):
        import hashlib
        root = Path(__file__).resolve().parents[1]
        directory = root / 'hardware/lab/observations/qotom-native-acpi-20260911'
        manifest = json.loads((directory / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((directory / name).read_bytes()).hexdigest(), digest, name)
        events = [json.loads(line) for line in (directory / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(event['hex']) for event in events)
        self.assertEqual(raw, (directory / 'cycle-1/serial.raw').read_bytes())
        binary = (directory / 'cycle-1/multiboot2.bin').read_bytes()
        _, metadata, tables = D['extract'](raw, binary)
        self.assertEqual(metadata, json.loads((directory / 'cycle-1/acpi.json').read_text()))
        self.assertEqual(len(tables), 11)
        self.assertEqual(sum(map(len, tables.values())), 3951)
        for name, data in tables.items():
            self.assertEqual(data, (directory / 'cycle-1/acpi' / name).read_bytes())
        lab = runpy.run_path(str(root / 'scripts/run-qotom-recovery-lab.py'))
        recorded = json.loads((directory / 'cycle-1/result.json').read_text())
        result = lab['classify_cpu_protected'](events, recorded['elf_sha256'],
            directory / 'diagnostic-protocol.tsv', root / 'build/j1900-cpu-host/host',
            root / 'build/qotom-pci-inventory-host/host', True, True, True)
        self.assertEqual(result['acpi'], recorded['acpi'])
        self.assertEqual(result['pci_read_trace']['mismatches'], 2)
        self.assertFalse(result['diagnostic']['platform_admitted'])

    def test_cpu_rejection_needs_no_acpi(self):
        rejected = b'FINAL status=FAIL reason=j1900-cpu-profile\n'
        self.assertEqual(D['extract'](rejected, handoff()), (rejected, None, {}))
        with self.assertRaises(ValueError): D['extract'](FINAL, handoff())


if __name__ == '__main__':
    unittest.main()
