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
