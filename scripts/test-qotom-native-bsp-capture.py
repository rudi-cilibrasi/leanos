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
