#!/usr/bin/env python3
"""Synthetic PCIe Device records over the retained physical xHCI BME prefix."""
import json
import re
from pathlib import Path
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / 'hardware/lab/observations/qotom-native-xhci-bme-20260911'
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-pcie-device-capture.py'))
R = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
PROTOCOL = R['cpu_replay_module'](True).load_protocol(CAPTURE / 'diagnostic-protocol.tsv')
SERIAL = (CAPTURE / 'cycle-1/serial.raw').read_bytes()
FINAL = PROTOCOL['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
RAW = SERIAL[SERIAL.index(PROTOCOL['BOOT'].encode()):SERIAL.index(FINAL)+len(FINAL)]
assert RAW.endswith(FINAL)
PREFIX = RAW[:-len(FINAL)]
CAPS = json.loads((CAPTURE / 'cycle-1/pci-capabilities.json').read_text())


def record(index,status,offset=0,capability=0,control=0):
    return (f'LEANOS-LAB/1 PCIE-DEVICE profile=qotom-pcie-device-v1 index={index} '
        f'status={status} offset={offset} capability={capability} control-status={control}\n').encode()


RECORDS = []
for function in CAPS['functions']:
    entries = [e for e in function['headers'] if e['raw'] & 255 == 0x10]
    RECORDS.append(record(function['index'],0,entries[0]['offset'],0x10000000,0x200000)
        if entries else record(function['index'],1))


class Capture(unittest.TestCase):
    def test_success_and_raw_payloads(self):
        for cap in (0,1,0x10000000,0xfffffffe):
            for ctl in (0,1,0x200000,0xfffffffe):
                records=RECORDS.copy();records[13]=record(13,0,0x70,cap,ctl)
                projection,result=D['extract'](PREFIX+b''.join(records)+FINAL,PROTOCOL)
                self.assertEqual(projection,RAW)
                self.assertEqual(len(result['functions']),16)
                self.assertEqual(result['functions'][13]['device_capabilities'],cap)
                self.assertEqual(result['functions'][13]['device_control_status'],ctl)
                self.assertFalse(result['dma_quarantine_established'])

    def test_reachable_failures(self):
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-pcie-device')
        for index in range(16):
            for status in ((3,4,6,7,8) if index in (6,7,8,9,13,14,15) else (3,4)):
                raw=PREFIX+b''.join(RECORDS[:index])+record(index,status)
                _,result=D['extract'](raw+failure,PROTOCOL)
                self.assertEqual(result['functions'][-1]['status'],status)
                with self.assertRaises(ValueError):D['extract'](raw+FINAL,PROTOCOL)

    def test_advertised_shape_rejection(self):
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-pcie-device')
        pattern=rb'(LEANOS-LAB/1 PCI-CAP index=13 slot=[0-9]+ offset=112 raw=)([0-9]+)(\n)'
        for flags in (0,3,0x102,0x42,0x8002,0x4002):
            def changed(match):
                raw=(int(match[2])&0xffff)|(flags<<16)
                return match[1]+str(raw).encode()+match[3]
            prefix,count=re.subn(pattern,changed,PREFIX)
            self.assertEqual(count,1)
            before=prefix+b''.join(RECORDS[:13])
            _,result=D['extract'](before+record(13,5)+failure,PROTOCOL)
            self.assertEqual(result['functions'][-1]['status'],5)
            for status in (0,6,7,8):
                with self.assertRaises(ValueError):
                    D['extract'](before+record(13,status)+failure,PROTOCOL)

    def test_rejects_invalid_records(self):
        for records in ([],RECORDS[:-1],RECORDS+RECORDS[-1:],RECORDS[1:]):
            with self.assertRaises(ValueError):D['extract'](PREFIX+b''.join(records)+FINAL,PROTOCOL)
        for bad in (record(13,1),record(13,2),record(13,5),record(13,9),record(13,0,0x74),
                record(13,0,0x70,0xffffffff),record(13,0,0x70,0,0xffffffff),record(13,0,0x70,1<<32),
                record(13,3,0x70),record(13,0,0x70).replace(b'status=0',b'status=00')):
            records=RECORDS.copy();records[13]=bad
            with self.assertRaises(ValueError):D['extract'](PREFIX+b''.join(records)+FINAL,PROTOCOL)
        for status in (0,5,6,7,8):
            records=RECORDS.copy();records[0]=record(0,status)
            with self.assertRaises(ValueError):D['extract'](PREFIX+b''.join(records)+FINAL,PROTOCOL)
        with self.assertRaises(ValueError):D['extract'](PREFIX+b''.join(RECORDS)+FINAL+b'x',PROTOCOL)
        with self.assertRaises(ValueError):D['extract'](b'x'*131073,PROTOCOL)


if __name__ == '__main__':
    unittest.main()
