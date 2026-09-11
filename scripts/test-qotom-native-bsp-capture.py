#!/usr/bin/env python3
"""Synthetic BSP records over retained physical ACPI and recovery bytes."""
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
C = ROOT / 'hardware/lab/observations/qotom-native-inventory-20260911'
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-bsp-capture.py'))
R = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
P = R['cpu_replay_module'](True).load_protocol(C / 'diagnostic-protocol.tsv')
BSP = Path(os.environ.get('LEANOS_BSP_REPLAY', ROOT / 'build/qotom-bsp-replay/host'))
CPU = ROOT / 'build/j1900-cpu-host/host'
PCI = ROOT / 'build/qotom-native-inventory-host/host'
META = json.loads((C / 'cycle-1/acpi.json').read_text())
TABLES = {p.name:p.read_bytes() for p in (C / 'cycle-1/acpi').glob('*.bin')}
EVENTS = [json.loads(s) for s in (C / 'cycle-1/events.jsonl').read_text().splitlines()]
RAW = b''.join(bytes.fromhex(e['hex']) for e in EVENTS)
FINAL = P['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
END = RAW.index(FINAL) + len(FINAL)
DIGEST = json.loads((C / 'cycle-1/result.json').read_text())['elf_sha256']
ARM = D['ARM']
VALUES = dict(zip(D['NAMES'],(0xb97a6ae0,132,0,3219913727,1,0xfee00900,0,0,0,132,0,4,0xfee00900)))


def record(**changes):
    values = VALUES | changes
    return (D['PREFIX'] + b'profile=qotom-bsp-v1' + b''.join(
        b' ' + n.encode() + b'=' + str(values[n]).encode() for n in D['NAMES']) + b' platform-admitted=0\n')


def protected(line=None, rejected=False, enabled=True):
    line = record() if line is None else line
    prefix = RAW[:END]
    if rejected:
        prefix = prefix[:prefix.index(ARM)+len(ARM)] + line + P['FINAL'].encode() + b' status=FAIL reason=qotom-native-bsp\n'
    else:
        prefix = prefix.replace(ARM, ARM + line)
    events = [{'elapsed':0,'hex':prefix.hex()},{'elapsed':35,'hex':RAW[END:].hex()}]
    return R['classify_cpu_protected'](events,DIGEST,C / 'diagnostic-protocol.tsv',CPU,PCI,
        handoff=True,acpi=True,bootstrap=True,ecam_memory=True,dsdt=True,
        ecam_read=True,native_inventory=True,native_kernel=True,
        bsp_replay=BSP if enabled else None)


class Capture(unittest.TestCase):
    def test_retained_physical_bsp_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-bsp-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(s) for s in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP)
        self.assertEqual(result['native_bsp'],expected['native_bsp'])
        self.assertEqual(result['native_bsp']['observation'],VALUES)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertEqual(result['quiet_seconds'],expected['quiet_seconds'])
        self.assertTrue(expected['request_consumed'])
        self.assertNotEqual(expected['freebsd_boot_before'],expected['freebsd_boot_after'])

    def test_capability_protected_projection(self):
        # Synthetic capability contents over real inventory/recovery framing.
        # This is transport validation, not a physical capability observation.
        caps = b''
        for line in RAW[:END].splitlines():
            if line.startswith(P['PCI-HEADER'].encode()):
                words = list(map(int, line.split(b' words=')[1].split(b',')))
                index = len(caps.split(b'PCI-CAPS')) - 1
                head = words[16] & 255 if words[4] & 0x100000 else 0
                caps += f'LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index={index} status=0 offset=0 count={1 if head else 0}\n'.encode()
                if head:
                    caps += f'LEANOS-LAB/1 PCI-CAP index={index} slot=0 offset={head} raw=1\n'.encode()
        for rejected in (False, True):
            emitted = (b'LEANOS-LAB/1 PCI-CAPS profile=conventional-v1 index=0 status=2 offset=0 count=0\n'
                       if rejected else caps)
            terminal = P['FINAL'].encode() + b' status=FAIL reason=qotom-pci-capabilities\n' if rejected else FINAL
            prefix = RAW[:END].replace(ARM, ARM + record()).replace(FINAL, emitted + terminal)
            events = [{'elapsed':0,'hex':prefix.hex()},{'elapsed':35,'hex':RAW[END:].hex()}]
            result = R['classify_cpu_protected'](events,DIGEST,C / 'diagnostic-protocol.tsv',CPU,PCI,
                handoff=True,acpi=True,bootstrap=True,ecam_memory=True,dsdt=True,
                ecam_read=True,native_inventory=True,native_kernel=True,
                bsp_replay=BSP,pci_capabilities=True)
            self.assertEqual(result['diagnostic']['inventory_result'],1)
            self.assertEqual(result['diagnostic']['terminal_reason'],
                             'qotom-pci-capabilities' if rejected else 'qotom-platform-pending')
            self.assertIn('pci_capabilities_decoder_sha256',result['diagnostic'])

    def test_retained_physical_capabilities(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-capabilities-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,pci_capabilities=True)
        self.assertEqual(result['pci_capabilities'],expected['pci_capabilities'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertEqual(sum(len(f['headers']) for f in result['pci_capabilities']['functions']),47)

    def test_af_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-capabilities-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(records, terminal=FINAL):
            changed = raw[:end].replace(FINAL, records + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':35,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True)
        records = b''.join(f'LEANOS-LAB/1 PCI-AF profile=af-observation-v1 index={i} status={0 if i==10 else 1} offset={152 if i==10 else 0} raw={256 if i==10 else 0}\n'.encode() for i in range(16))
        result = check(records)
        self.assertEqual(result['af_observation']['functions'][10]['raw'],256)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('af_decoder_sha256',result['diagnostic'])
        self.assertFalse(result['af_observation']['dma_quarantine_established'])
        mutations = [b'', records+records, records.replace(b'index=10',b'index=09'),
            records.replace(b'offset=152',b'offset=156'),
            records.replace(b'raw=256',b'raw=4294967295'),
            records.replace(b'raw=256',b'raw=4294967296'),
            records.replace(b'status=1 offset=0',b'status=2 offset=0',1),
            records.replace(b'offset=152 raw=256',b'offset=0 raw=0').replace(b'index=10 status=0',b'index=10 status=1')]
        for mutation in mutations:
            with self.assertRaises(ValueError): check(mutation)
        failure = b'LEANOS-LAB/1 PCI-AF profile=af-observation-v1 index=0 status=4 offset=0 raw=0\n'
        result = check(failure,P['FINAL'].encode()+b' status=FAIL reason=qotom-pci-af\n')
        self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-pci-af')
        with self.assertRaises(ValueError): check(failure)

    def test_retained_physical_af(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-af-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True)
        self.assertEqual(result['af_observation'],expected['af_observation'])
        self.assertEqual(result['af_observation']['functions'][10],
                         {'index':10,'status':0,'offset':152,'raw':0})
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        start = raw.index(b'LEANOS-LAB/1 PCI-AF profile=af-observation-v1 index=10 ')
        end = raw.index(FINAL) + len(FINAL)
        bad = (raw[:start] +
            b'LEANOS-LAB/1 PCI-AF profile=af-observation-v1 index=10 status=6 offset=0 raw=0\n' +
            P['FINAL'].encode()+b' status=FAIL reason=qotom-pci-af\n')
        synthetic = [{'elapsed':0,'hex':bad.hex()},{'elapsed':35,'hex':raw[end:].hex()}]
        with self.assertRaises(ValueError):
            R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True)

    def test_ehci_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-af-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL):
            changed = raw[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':35,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True)
        record = b'LEANOS-LAB/1 EHCI-CAPS profile=qotom-ehci-v1 index=10 status=0 capbase=16777248 structural=4 capability=26624\n'
        result = check(record)
        self.assertEqual(result['ehci_capabilities']['capability'],26624)
        self.assertFalse(result['ehci_capabilities']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('ehci_decoder_sha256',result['diagnostic'])
        mutations = [b'',record+record,record.replace(b'index=10',b'index=11'),
            record.replace(b'status=0',b'status=1'),record.replace(b'structural=4',b'structural=0'),
            record.replace(b'capbase=16777248',b'capbase=16777249'),
            record.replace(b'capability=26624',b'capability=4294967295'),
            record.replace(b'capability=26624',b'capability=4294967296')]
        for mutation in mutations:
            with self.assertRaises(ValueError): check(mutation)
        for status in (3,4,5,6,7,8):
            failed = f'LEANOS-LAB/1 EHCI-CAPS profile=qotom-ehci-v1 index=10 status={status} capbase=0 structural=0 capability=0\n'.encode()
            result = check(failed,P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-capabilities\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-ehci-capabilities')
            with self.assertRaises(ValueError): check(failed)

    def test_retained_physical_ehci(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True)
        self.assertEqual(result['ehci_capabilities'],expected['ehci_capabilities'])
        self.assertEqual(result['ehci_capabilities']['capability'],0x36881)
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_legacy_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-legacy-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True)
        self.assertEqual(result['ehci_legacy'],expected['ehci_legacy'])
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_handoff_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-handoff-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True)
        self.assertEqual(result['ehci_handoff'],expected['ehci_handoff'])
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_smi_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-smi-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_operational_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-operational-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_bme_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-bme-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True)
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_xhci_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True)
        self.assertEqual(result['xhci_capabilities'],expected['xhci_capabilities'])
        self.assertEqual(result['xhci_capabilities']['status'],0)
        self.assertEqual(result['xhci_capabilities']['words'],[0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000])
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

    def test_retained_xhci_legacy_capture(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-legacy-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True,xhci_legacy=True)
        self.assertEqual(result['xhci_capabilities'],expected['xhci_capabilities'])
        self.assertEqual(result['xhci_capabilities']['status'],0)
        self.assertEqual(result['xhci_capabilities']['words'],[0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000])
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

        self.assertEqual(result['xhci_legacy'],expected['xhci_legacy'])
        self.assertEqual(result['xhci_legacy']['status'],0)
        self.assertEqual(result['xhci_legacy']['legacy_offset'],0x8460)
        self.assertEqual(result['xhci_legacy']['control_status'],0x2001)
        self.assertEqual(result['xhci_legacy']['headers'],[
            {'offset':a,'raw':v} for a,v in [(0x8000,0x02000802),(0x8020,0x03000802),
                (0x8040,0x00010cc1),(0x8070,0x0000fcc0),(0x8460,0x00010801),(0x8480,0x0005000a)]])
        self.assertFalse(result['xhci_legacy']['ownership_established'])

    def test_retained_xhci_handoff_rejection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-handoff-rejection-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True)
        self.assertEqual(result['xhci_capabilities'],expected['xhci_capabilities'])
        self.assertEqual(result['xhci_capabilities']['status'],0)
        self.assertEqual(result['xhci_capabilities']['words'],[0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000])
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

        self.assertEqual(result['xhci_legacy'],expected['xhci_legacy'])
        self.assertEqual(result['xhci_legacy']['status'],0)
        self.assertEqual(result['xhci_legacy']['legacy_offset'],0x8460)
        self.assertEqual(result['xhci_legacy']['control_status'],0x2001)
        self.assertEqual(result['xhci_legacy']['headers'],[
            {'offset':a,'raw':v} for a,v in [(0x8000,0x02000802),(0x8020,0x03000802),
                (0x8040,0x00010cc1),(0x8070,0x0000fcc0),(0x8460,0x00010801),(0x8480,0x0005000a)]])
        self.assertFalse(result['xhci_legacy']['ownership_established'])

        self.assertEqual(result['xhci_handoff'],expected['xhci_handoff'])
        self.assertEqual(result['xhci_handoff']['status'],10)
        self.assertEqual(result['xhci_handoff']['write_attempted'],1)
        self.assertEqual(result['xhci_handoff']['polls'],2)
        self.assertEqual(result['xhci_handoff']['last_support'],0x01000801)
        self.assertEqual(result['xhci_handoff']['final_control'],0)
        self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-xhci-handoff')
        self.assertFalse(result['xhci_handoff']['firmware_exclusion_established'])

    def test_retained_xhci_handoff_detail(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-handoff-detail-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True)
        self.assertEqual(result['xhci_capabilities'],expected['xhci_capabilities'])
        self.assertEqual(result['xhci_capabilities']['status'],0)
        self.assertEqual(result['xhci_capabilities']['words'],[0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000])
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

        self.assertEqual(result['xhci_legacy'],expected['xhci_legacy'])
        self.assertEqual(result['xhci_legacy']['status'],0)
        self.assertEqual(result['xhci_legacy']['legacy_offset'],0x8460)
        self.assertEqual(result['xhci_legacy']['control_status'],0x2001)
        self.assertEqual(result['xhci_legacy']['headers'],[
            {'offset':a,'raw':v} for a,v in [(0x8000,0x02000802),(0x8020,0x03000802),
                (0x8040,0x00010cc1),(0x8070,0x0000fcc0),(0x8460,0x00010801),(0x8480,0x0005000a)]])
        self.assertFalse(result['xhci_legacy']['ownership_established'])

        self.assertEqual(result['xhci_handoff'],expected['xhci_handoff'])
        self.assertEqual(result['xhci_handoff']['status'],10)
        self.assertEqual(result['xhci_handoff']['write_attempted'],1)
        self.assertEqual(result['xhci_handoff']['polls'],1)
        self.assertEqual(result['xhci_handoff']['last_support'],0x01000801)
        self.assertEqual(result['xhci_handoff']['final_control'],0)
        self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-xhci-handoff')
        self.assertFalse(result['xhci_handoff']['firmware_exclusion_established'])

        self.assertEqual(result['xhci_handoff']['verification'],{'kind':5,'index':2,'expected':0x10cc1,'observed':0xcc1})

    def test_retained_xhci_handoff_success(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-handoff-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True)
        self.assertEqual(result['xhci_capabilities'],expected['xhci_capabilities'])
        self.assertEqual(result['xhci_capabilities']['status'],0)
        self.assertEqual(result['xhci_capabilities']['words'],[0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000])
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

        self.assertEqual(result['xhci_legacy'],expected['xhci_legacy'])
        self.assertEqual(result['xhci_legacy']['status'],0)
        self.assertEqual(result['xhci_legacy']['legacy_offset'],0x8460)
        self.assertEqual(result['xhci_legacy']['control_status'],0x2001)
        self.assertEqual(result['xhci_legacy']['headers'],[
            {'offset':a,'raw':v} for a,v in [(0x8000,0x02000802),(0x8020,0x03000802),
                (0x8040,0x00010cc1),(0x8070,0x0000fcc0),(0x8460,0x00010801),(0x8480,0x0005000a)]])
        self.assertFalse(result['xhci_legacy']['ownership_established'])

        self.assertEqual(result['xhci_handoff'],expected['xhci_handoff'])
        self.assertEqual(result['xhci_handoff']['status'],0)
        self.assertEqual(result['xhci_handoff']['write_attempted'],1)
        self.assertEqual(result['xhci_handoff']['polls'],2)
        self.assertEqual(result['xhci_handoff']['last_support'],0x01000801)
        self.assertEqual(result['xhci_handoff']['final_control'],0x2000)
        self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-platform-pending')
        self.assertFalse(result['xhci_handoff']['firmware_exclusion_established'])

        self.assertEqual(result['xhci_handoff']['verification'],{'kind':0,'index':0,'expected':0,'observed':0})

    def test_retained_xhci_smi(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-smi-20260911'
        manifest = json.loads((capture / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((capture / name).read_bytes()).hexdigest(),digest)
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        result = R['classify_cpu_protected'](events,expected['elf_sha256'],
            capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
            bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
            native_inventory=True,native_kernel=True,bsp_replay=BSP,
            pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True,xhci_smi=True)
        self.assertEqual(result['xhci_capabilities'],expected['xhci_capabilities'])
        self.assertEqual(result['xhci_capabilities']['status'],0)
        self.assertEqual(result['xhci_capabilities']['words'],[0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000])
        self.assertEqual(result['ehci_bme'],expected['ehci_bme'])
        self.assertEqual(result['ehci_bme']['status'],0)
        self.assertEqual(result['ehci_bme']['write_attempted'],1)
        self.assertEqual(result['ehci_bme']['before_command'],0x406)
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertEqual(result['ehci_operational'],expected['ehci_operational'])
        self.assertEqual(result['ehci_operational']['status'],0)
        self.assertEqual(result['ehci_operational']['command'],0x80000)
        self.assertEqual(result['ehci_operational']['status_register'],0x1000)
        self.assertEqual(result['ehci_operational']['interrupt_enable'],0)
        self.assertEqual(result['ehci_operational']['configured'],0)
        self.assertEqual(result['ehci_smi'],expected['ehci_smi'])
        self.assertEqual(result['ehci_smi']['status'],0)
        self.assertEqual(result['ehci_smi']['before_control'],0x2000)
        self.assertEqual(result['ehci_smi']['after_control'],0)
        self.assertEqual(result['ehci_handoff']['status'],0)
        self.assertEqual(result['ehci_handoff']['last_support'],0x1000001)
        self.assertEqual(result['ehci_handoff']['final_control'],0x2000)
        self.assertEqual(result['ehci_legacy']['headers'],[{'offset':104,'raw':65537}])
        self.assertEqual(result['ehci_legacy']['control_status'],0x82005)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)

        self.assertEqual(result['xhci_legacy'],expected['xhci_legacy'])
        self.assertEqual(result['xhci_legacy']['status'],0)
        self.assertEqual(result['xhci_legacy']['legacy_offset'],0x8460)
        self.assertEqual(result['xhci_legacy']['control_status'],0x2001)
        self.assertEqual(result['xhci_legacy']['headers'],[
            {'offset':a,'raw':v} for a,v in [(0x8000,0x02000802),(0x8020,0x03000802),
                (0x8040,0x00010cc1),(0x8070,0x0000fcc0),(0x8460,0x00010801),(0x8480,0x0005000a)]])
        self.assertFalse(result['xhci_legacy']['ownership_established'])

        self.assertEqual(result['xhci_handoff'],expected['xhci_handoff'])
        self.assertEqual(result['xhci_handoff']['status'],0)
        self.assertEqual(result['xhci_handoff']['write_attempted'],1)
        self.assertEqual(result['xhci_handoff']['polls'],2)
        self.assertEqual(result['xhci_handoff']['last_support'],0x01000801)
        self.assertEqual(result['xhci_handoff']['final_control'],0x2000)
        self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-platform-pending')
        self.assertFalse(result['xhci_handoff']['firmware_exclusion_established'])

        self.assertEqual(result['xhci_handoff']['verification'],{'kind':0,'index':0,'expected':0,'observed':0})

        self.assertEqual(result['xhci_smi'],expected['xhci_smi'])
        self.assertEqual(result['xhci_smi']['status'],0)
        self.assertEqual(result['xhci_smi']['write_attempted'],1)
        self.assertEqual(result['xhci_smi']['before_control'],0x2000)
        self.assertEqual(result['xhci_smi']['after_control'],0)
        self.assertFalse(result['xhci_smi']['firmware_exclusion_established'])
        self.assertFalse(result['xhci_smi']['dma_quarantine_established'])

    def test_legacy_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(records, terminal=FINAL):
            changed = raw[:end].replace(FINAL, records + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':35,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,ehci_legacy=True)
        records = (b'LEANOS-LAB/1 EHCI-LEGACY profile=qotom-legacy-v1 index=10 status=0 count=1 offset=104 control=1\n'
                   b'LEANOS-LAB/1 EHCI-EXT index=0 offset=104 raw=16842753\n')
        result = check(records)
        self.assertEqual(result['ehci_legacy']['legacy_offset'],104)
        self.assertEqual(result['ehci_legacy']['control_status'],1)
        self.assertFalse(result['ehci_legacy']['ownership_established'])
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('ehci_legacy_decoder_sha256',result['diagnostic'])
        mutations = [b'',records+records,records.replace(b'count=1',b'count=49'),
            records.replace(b'offset=104',b'offset=108'),records.replace(b'raw=16842753',b'raw=26625'),
            records.replace(b'raw=16842753',b'raw=0'),records.replace(b'control=1',b'control=4294967295'),
            records.replace(b'control=1',b'control=4294967296'),records.replace(b'index=0',b'index=1')]
        for mutation in mutations:
            with self.assertRaises(ValueError): check(mutation)
        for status in range(2,12):
            failed = f'LEANOS-LAB/1 EHCI-LEGACY profile=qotom-legacy-v1 index=10 status={status} count=0 offset=0 control=0\n'.encode()
            result = check(failed,P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-legacy\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-ehci-legacy')
            with self.assertRaises(ValueError): check(failed)

    def test_handoff_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-legacy-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL):
            changed = raw[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':35,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True)
        def record(status,attempted,polls,support,control):
            return f'LEANOS-LAB/1 EHCI-HANDOFF profile=qotom-handoff-v1 index=10 status={status} attempted={attempted} polls={polls} support={support} control={control}\n'.encode()
        success = record(0,1,1,0x1000001,0)
        result = check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('ehci_handoff_decoder_sha256',result['diagnostic'])
        self.assertFalse(result['ehci_handoff']['firmware_exclusion_established'])
        failures = [(2,0,0,0,0),(3,0,0,0,0),(5,1,0,0x10001,0),
            (6,1,0,0x10001,0),(6,1,99,0x1010001,0),
            (7,1,1,0x10001,0),(7,1,100,0x1010001,0),
            (8,1,1,0x10001,0),(9,1,100,0x1010001,0),
            (10,1,1,0x1000001,0),(10,1,1,0x1010001,0),
            (11,0,0,0,0),(12,0,0,0,0),(13,0,0,0,0)]
        for values in failures:
            result = check(record(*values),P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-handoff\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-ehci-handoff')
            with self.assertRaises(ValueError): check(record(*values))
        for changed in [b'',success+success,success.replace(b'attempted=1',b'attempted=0'),
                success.replace(b'polls=1',b'polls=0'),success.replace(b'polls=1',b'polls=101'),
                success.replace(b'status=0',b'status=00'),record(0,1,1,0x1010001,0),
                record(0,1,1,0x1000001,0xffffffff),record(1,0,0,0,0),record(4,0,0,0,0)]:
            with self.assertRaises(ValueError): check(changed)

    def test_xhci_handoff_verification_details(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-legacy-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL, source=None):
            changed = (raw[:end] if source is None else source).replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,
                ehci_bme=True,xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True)
        failure=P['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-handoff\n'
        def detailed(kind=1,index=0,before=0,after=2,status=10,support=0x01000801):
            return (f'LEANOS-LAB/1 XHCI-HANDOFF profile=qotom-xhci-handoff-v2 index=3 status={status}'
                f' attempted=1 polls=2 support={support} control=0 verify={kind} verify-index={index}'
                f' expected={before} observed={after}\n').encode()
        for fields in [(1,0,0,2),(1,0,0,6),(1,0,0,10),(2,0,6,5),(3,0,0x8460,0),
                (4,1,0x8020,0x8024),(5,0,0x02000802,0x02010802)]:
            result=check(detailed(*fields),failure)
            self.assertEqual(result['xhci_handoff']['verification'],dict(zip(
                ('kind','index','expected','observed'),fields)))
            self.assertEqual(result['xhci_handoff']['schema'],'leanos-qotom-xhci-handoff-observation-v2')
            with self.assertRaises(ValueError):check(detailed(*fields))
        for support in (0x801,0x10801,0x1010801):
            result=check(detailed(6,4,0x01000801,support,support=support),failure)
            self.assertEqual(result['xhci_handoff']['verification']['kind'],6)
        success=detailed(0,0,0,0,status=0)
        self.assertEqual(check(success)['xhci_handoff']['status'],0)
        for fields in [(0,0,0,0),(1,0,0,1),(1,1,0,2),(1,0,1,2),(1,0,0,11),
                (2,0,6,6),(2,0,5,4),(2,0,6,49),(3,0,0x8460,0x8460),
                (3,0,0x8460,0x8001),(4,6,0x8020,0x8024),(4,1,0x8020,0x8020),
                (5,0,0x02000802,0x02000802),(5,4,0x10801,0x01010801),
                (5,0,0x02000802,0xffffffff),(6,4,0x01000801,0x01000801),(7,0,0,2),
                (1,0,0,0x100000000)]:
            with self.assertRaises(ValueError):check(detailed(*fields),failure)
        with self.assertRaises(ValueError):check(detailed(status=0))
        with self.assertRaises(ValueError):check(detailed(support=0x10801),failure)
        for bad in [success.replace(b'v2',b'v1'),success.replace(b'v2',b'v3'),
                success[:success.index(b' verify=')]+b'\n',
                success.replace(b'verify=0',b'verify=00'),success.replace(b' observed=0',b'')]:
            with self.assertRaises(ValueError):check(bad)

    def test_xhci_handoff_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-legacy-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL, source=None):
            changed = (raw[:end] if source is None else source).replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,
                ehci_bme=True,xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True)
        def record(status,attempted,polls,support,control):
            return f'LEANOS-LAB/1 XHCI-HANDOFF profile=qotom-xhci-handoff-v1 index=3 status={status} attempted={attempted} polls={polls} support={support} control={control}\n'.encode()
        success = record(0,1,1,0x1000801,0)
        result = check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('xhci_handoff_decoder_sha256',result['diagnostic'])
        self.assertFalse(result['xhci_handoff']['firmware_exclusion_established'])
        failures = [(2,0,0,0,0),(3,0,0,0,0),(5,1,0,0x10801,0),
            (6,1,0,0x10801,0),(6,1,99,0x1010801,0),
            (7,1,1,0x10801,0),(7,1,100,0x1010801,0),
            (8,1,1,0x10801,0),(9,1,100,0x1010801,0),
            (10,1,1,0x1000801,0),(10,1,1,0x1010801,0),
            (11,0,0,0,0),(12,0,0,0,0),(13,0,0,0,0),(14,0,0,0,0)]
        for values in failures:
            result = check(record(*values),P['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-handoff\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-xhci-handoff')
            with self.assertRaises(ValueError): check(record(*values))
        for changed in [b'',success+success,success.replace(b'attempted=1',b'attempted=0'),
                success.replace(b'polls=1',b'polls=0'),success.replace(b'polls=1',b'polls=101'),
                success.replace(b'status=0',b'status=00'),record(0,1,1,0x1010801,0),
                record(0,1,1,0x1000801,0xffffffff),record(1,0,0,0,0),record(4,0,0,0,0)]:
            with self.assertRaises(ValueError): check(changed)

        failure=P['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-handoff\n'
        with self.assertRaises(ValueError):check(success,failure)
        changed=raw[:end].replace(b'count=6 offset=33888 control=8193',b'count=6 offset=33888 control=8192')
        self.assertNotEqual(changed,raw[:end])
        with self.assertRaises(ValueError):check(success,source=changed)
        self.assertEqual(check(record(14,0,0,0,0),failure,changed)['xhci_handoff']['status'],14)
        for values in [(5,1,1,0x10801,0),(6,1,100,0x1010801,0),
                (7,1,0,0x10801,0),(8,1,1,0x1000801,0),(9,1,99,0x1010801,0),
                (10,1,1,0x1000802,0),(11,1,0,0,0),(15,0,0,0,0)]:
            with self.assertRaises(ValueError):check(record(*values),failure)

    def test_smi_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-handoff-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL):
            changed = raw[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True)
        def record(status,attempted,before,after):
            return f'LEANOS-LAB/1 EHCI-SMI profile=qotom-smi-v1 index=10 status={status} attempted={attempted} before={before} after={after}\n'.encode()
        success = record(0,1,0x2000,0)
        result = check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('ehci_smi_decoder_sha256',result['diagnostic'])
        self.assertFalse(result['ehci_smi']['firmware_exclusion_established'])
        result = check(record(0,1,0xe03f2000,0xe03f0000))
        self.assertEqual(result['ehci_smi']['after_control'],0xe03f0000)
        for values in [(3,0,0,0),(4,0,0,0),(5,1,0x2000,0),(6,1,0x2000,0),
                       (7,1,0x2000,0x2000),(7,1,0x2000,0x40),(8,0,0,0),(9,0,0,0)]:
            result = check(record(*values),P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-smi\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-ehci-smi')
            with self.assertRaises(ValueError): check(record(*values))
        for changed in [b'',success+success,success.replace(b'attempted=1',b'attempted=0'),
                success.replace(b'status=0',b'status=00'),record(0,1,0x2001,0),
                record(0,1,0x2000,1),record(0,1,0x2000,0x40),record(0,1,0x2000,0xffffffff),
                record(1,0,0,0),record(2,0,0,0),record(0,1,0x100002000,0)]:
            with self.assertRaises(ValueError): check(changed)

    def test_xhci_smi_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-handoff-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL):
            changed = raw[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,
                xhci_capabilities=True,xhci_legacy=True,xhci_handoff=True,xhci_smi=True)
        def record(status,attempted,before,after):
            return f'LEANOS-LAB/1 XHCI-SMI profile=qotom-xhci-smi-v1 index=3 status={status} attempted={attempted} before={before} after={after}\n'.encode()
        success = record(0,1,0x2000,0)
        result = check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('xhci_smi_decoder_sha256',result['diagnostic'])
        self.assertFalse(result['xhci_smi']['firmware_exclusion_established'])
        result = check(record(0,1,0xe0112000,0xe0110000))
        self.assertEqual(result['xhci_smi']['after_control'],0xe0110000)
        for values in [(3,0,0,0),(4,0,0,0),(5,1,0x2000,0),(6,1,0x2000,0),
                       (7,1,0x2000,0x2000),(7,1,0x2000,0x40),(8,0,0,0),(9,0,0,0),(10,0,0,0)]:
            result = check(record(*values),P['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-smi\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-xhci-smi')
            with self.assertRaises(ValueError): check(record(*values))
        for changed in [b'',success+success,success.replace(b'attempted=1',b'attempted=0'),
                success.replace(b'status=0',b'status=00'),record(0,1,0x2001,0),
                record(0,1,0x2000,1),record(0,1,0x2000,0x40),record(0,1,0x2000,0xffffffff),
                record(1,0,0,0),record(2,0,0,0),record(11,0,0,0),record(0,1,0x100002000,0)]:
            with self.assertRaises(ValueError): check(changed)

    def test_operational_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-smi-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL):
            changed = raw[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True)
        def record(status=0,command=0x80001,sampled=0x8000,interrupts=0x3f,configured=1):
            return f'LEANOS-LAB/1 EHCI-OPERATIONAL profile=qotom-operational-v1 index=10 status={status} command={command} status_register={sampled} interrupt_enable={interrupts} configured={configured}\n'.encode()
        success = record()
        result = check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('ehci_operational_decoder_sha256',result['diagnostic'])
        self.assertEqual(result['ehci_operational']['command'],0x80001)
        self.assertFalse(result['ehci_operational']['atomic_snapshot'])
        self.assertFalse(result['ehci_operational']['dma_quarantine_established'])
        for status in range(3,10):
            failed = record(status,0,0,0,0)
            result = check(failed,P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-operational\n')
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-ehci-operational')
            with self.assertRaises(ValueError): check(failed)
        for changed in [b'',success+success,success.replace(b'status=0',b'status=00'),
                record(1,0,0,0,0),record(2,0,0,0,0),record(10,0,0,0,0),
                record(command=0xffffffff),record(sampled=0xffffffff),
                record(interrupts=0x100000000),record(configured=-1),
                success.replace(b'index=10',b'index=9'),success.replace(b'profile=qotom-operational-v1',b'profile=unknown')]:
            with self.assertRaises(ValueError): check(changed)
        with self.assertRaises(ValueError):
            check(success,P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-operational\n')

    def test_bme_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-operational-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL, source=raw):
            changed = source[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':source[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True)
        def record(status=0,attempted=1,before=0x406,after=0x402):
            return f'LEANOS-LAB/1 EHCI-BME profile=qotom-bme-v1 index=10 status={status} attempted={attempted} before={before} after={after}\n'.encode()
        success=record()
        result=check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('ehci_bme_decoder_sha256',result['diagnostic'])
        self.assertEqual(result['ehci_bme']['after_command'],0x402)
        self.assertFalse(result['ehci_bme']['dma_quarantine_established'])
        failure=P['FINAL'].encode()+b' status=FAIL reason=qotom-ehci-bme\n'
        cases=[(n,0,0,0) for n in (3,4,5,9,10,11)]+[(6,1,0x406,0),(7,1,0x406,0),(7,1,0x406,0x406),
            (8,1,0x406,0x402),(8,1,0x406,0x406)]
        for values in cases:
            result=check(record(*values),failure)
            self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-ehci-bme')
            with self.assertRaises(ValueError):check(record(*values))
        for bad in [b'',success+success,success.replace(b'status=0',b'status=00'),record(1),record(2),record(12),
                record(attempted=0),record(before=0x402),record(after=0x406),record(after=65536),record(after=-1)]:
            with self.assertRaises(ValueError):check(bad)
        for bad in [record(3,1,0x406,0),record(6,1,0x406,0x402),record(7,1,0x406,0x402),record(8,0,0,0)]:
            with self.assertRaises(ValueError):check(bad,failure)
        with self.assertRaises(ValueError):check(success,failure)
        running=raw.replace(b'command=524288 status_register=4096',b'command=524289 status_register=4096')
        with self.assertRaises(ValueError):check(success,source=running)
        self.assertEqual(check(record(11,0,0,0),failure,source=running)['ehci_bme']['status'],11)

    def test_xhci_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-ehci-bme-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL):
            changed = raw[:end].replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,ehci_bme=True,xhci_capabilities=True)
        values=[0x1000080,0x07000820,0x84000054,0x40001,0x200071e1,0x3000,0x2000]
        def record(status=0,words=None):
            if words is None:words=values
            return f'LEANOS-LAB/1 XHCI-CAPS profile=qotom-xhci-v1 index=3 status={status} words={",".join(map(str,words))}\n'.encode()
        success=record()
        result=check(success)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertIn('xhci_capabilities_decoder_sha256',result['diagnostic'])
        self.assertEqual(result['xhci_capabilities']['words'],values)
        self.assertFalse(result['xhci_capabilities']['ownership_established'])
        failure=P['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-capabilities\n'
        for status in range(3,9):
            self.assertEqual(check(record(status,[0]*7),failure)['diagnostic']['terminal_reason'],'qotom-xhci-capabilities')
            with self.assertRaises(ValueError):check(record(status,[0]*7))
            with self.assertRaises(ValueError):check(record(status),failure)
        for bad in [b'',success+success,success.replace(b'status=0',b'status=00'),record(1),record(2),record(9),
                record(words=[0]*7),record(words=values[:-1]),record(words=values+[0]),
                success.replace(b'index=3',b'index=4'),success.replace(b'profile=qotom-xhci-v1',b'profile=unknown')]:
            with self.assertRaises(ValueError):check(bad)
        for i in range(7):
            changed=values.copy();changed[i]=0xffffffff
            with self.assertRaises(ValueError):check(record(words=changed))
        with self.assertRaises(ValueError):check(success,failure)

    def test_xhci_legacy_protected_projection(self):
        capture = ROOT / 'hardware/lab/observations/qotom-native-xhci-20260911'
        expected = json.loads((capture / 'cycle-1/result.json').read_text())
        events = [json.loads(line) for line in (capture / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(e['hex']) for e in events)
        end = raw.index(FINAL) + len(FINAL)
        def check(record, terminal=FINAL, source=None):
            prefix = raw[:end] if source is None else source
            changed = prefix.replace(FINAL, record + terminal)
            synthetic = [{'elapsed':0,'hex':changed.hex()},{'elapsed':37,'hex':raw[end:].hex()}]
            return R['classify_cpu_protected'](synthetic,expected['elf_sha256'],
                capture / 'diagnostic-protocol.tsv',CPU,PCI,handoff=True,acpi=True,
                bootstrap=True,ecam_memory=True,dsdt=True,ecam_read=True,
                native_inventory=True,native_kernel=True,bsp_replay=BSP,
                pci_capabilities=True,af_observation=True,ehci_capabilities=True,
                ehci_legacy=True,ehci_handoff=True,ehci_smi=True,ehci_operational=True,
                ehci_bme=True,xhci_capabilities=True,xhci_legacy=True)
        def record(status=0,headers=((0x8000,0x1000401),(0x8010,2)),offset=0x8000,control=0x2000):
            summary = f'LEANOS-LAB/1 XHCI-LEGACY profile=qotom-xhci-legacy-v1 index=3 status={status} count={len(headers)} offset={offset} control={control}\n'
            return summary.encode()+b''.join(f'LEANOS-LAB/1 XHCI-EXT index={i} offset={a} raw={v}\n'.encode() for i,(a,v) in enumerate(headers))
        success=record()
        result=check(success)
        self.assertEqual(result['xhci_legacy']['legacy_offset'],0x8000)
        self.assertEqual(result['xhci_legacy']['control_status'],0x2000)
        self.assertIn('xhci_legacy_decoder_sha256',result['diagnostic'])
        self.assertFalse(result['xhci_legacy']['hardware_operations_replayed'])
        self.assertFalse(result['xhci_legacy']['ownership_established'])
        self.assertEqual(check(record(headers=((0x8000,2),),offset=0,control=0))['xhci_legacy']['legacy_offset'],0)
        maximum=[(0x8000+i*4,0x1c0) for i in range(47)]+[(0x80bc,1)]
        self.assertEqual(len(check(record(headers=maximum,offset=0x80bc))['xhci_legacy']['headers']),48)
        failure=P['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-legacy\n'
        for status in range(2,13):
            rejected=record(status,(),0,0)
            self.assertEqual(check(rejected,failure)['diagnostic']['terminal_reason'],'qotom-xhci-legacy')
            with self.assertRaises(ValueError):check(rejected)
            with self.assertRaises(ValueError):check(record(status),failure)
        for bad in [b'',success+success,success.replace(b'status=0',b'status=00'),
                record(1,(),0,0),record(13,(),0,0),record(headers=()),
                record(headers=((0x8004,1),)),record(headers=((0x8000,0),)),
                record(headers=((0x8000,255),)),record(headers=((0x8000,0xffffffff),)),
                record(headers=((0x8000,0x401),(0x8010,1))),
                record(headers=((0x8000,0x101),(0x8004,2))),
                record(headers=((0x8000,0x402),(0x8014,1))),
                record(headers=((0x8000,0x402),)),record(offset=0x8004),
                record(control=0xffffffff),record(control=0x100000000),
                record(headers=((0x8000,2),),offset=0,control=1),
                success.replace(b'index=3',b'index=4'),success.replace(b'index=1 offset',b'index=2 offset'),
                success.replace(b'profile=qotom-xhci-legacy-v1',b'profile=unknown'),
                record(headers=maximum+[(0x80c0,2)],offset=0x80bc)]:
            with self.assertRaises(ValueError):check(bad)
        with self.assertRaises(ValueError):check(success,failure)
        # Mutate the captured HCC word by its actual decimal representation.
        changed=raw[:end].replace(str(0x200077c1).encode(),str(0x200077c0).encode())
        with self.assertRaises(ValueError):check(success,source=changed)
        self.assertEqual(check(record(12,(),0,0),failure,changed)['xhci_legacy']['status'],12)

    def test_selected_capture_provenance(self):
        manifest = json.loads((C / 'manifest.json').read_text())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((C / name).read_bytes()).hexdigest(),digest)

    def test_complete_protected_match(self):
        result = protected()
        self.assertEqual(result['native_bsp']['observation'],VALUES)
        self.assertEqual(result['diagnostic']['inventory_result'],1)
        self.assertFalse(result['native_bsp']['platform_admitted'])
        self.assertIn('bsp_replay_executable_sha256',result['diagnostic'])
        with self.assertRaises(ValueError): protected(enabled=False)

    def test_bound_bsp_rejection(self):
        line = record(available=0,**{'apic-base':0,'status':4,'detail':1,'admitted-id':0,'count':0,'bound-base':0})
        result = protected(line,rejected=True)
        self.assertEqual(result['diagnostic']['terminal_reason'],'qotom-native-bsp')
        self.assertEqual(result['diagnostic']['replay_scope'],'cpu-msr-before-bsp-failure')
        self.assertFalse(result['ecam']['transaction_fault'])
        with self.assertRaises(ValueError): protected(line)
        with self.assertRaises(ValueError): protected(record(),rejected=True)

    def test_result_and_source_mutations(self):
        for name in D['NAMES']:
            with self.subTest(name=name), self.assertRaises((ValueError,subprocess.CalledProcessError)):
                protected(record(**{name:VALUES[name]+1}))

    def test_framing(self):
        for line in (b'',b'\n'+record(),record()+record(),record().replace(b'status=0',b'status=00'),
                     record().replace(b'platform-admitted=0',b'platform-admitted=1'),
                     record().replace(b'profile=qotom-bsp-v1',b'profile=unknown'),
                     record().replace(b'length=132',b'length='+b'9'*600),
                     record(**{'apic-base':2**64})):
            with self.subTest(line=line[:80]),self.assertRaises(ValueError): protected(line)

    def test_earlier_foreign_firmware_failure(self):
        # No native BSP record is permitted before the exact firmware gate.
        early = b'prefix\n'+P['FINAL'].encode()+b' status=FAIL reason=qotom-ecam-arm\n'
        self.assertEqual(D['extract'](early,P,None,{},BSP),(early,None))
        with self.assertRaises(ValueError): D['extract'](record()+early,P,None,{},BSP)

    def test_replay_input_bounds(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'madt.bin'
            for content in (b'',b'APIC',bytes(65537),TABLES['00000000b97a6ae0.bin'][:-1]):
                p.write_bytes(content)
                self.assertNotEqual(subprocess.run([str(BSP),str(p),'0','544','1',str(0xfee00900),'0'],capture_output=True).returncode,0)
            p.write_bytes(TABLES['00000000b97a6ae0.bin'])
            for bad in ('-1','00','18446744073709551616','1x'):
                self.assertNotEqual(subprocess.run([str(BSP),str(p),bad,'544','1',str(0xfee00900),'0'],capture_output=True).returncode,0)


if __name__ == '__main__': unittest.main()
