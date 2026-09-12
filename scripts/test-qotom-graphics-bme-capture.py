#!/usr/bin/env python3
import hashlib
import json
import runpy
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
G=runpy.run_path(str(ROOT/'scripts/test-qotom-graphics-state-capture.py'))
D=runpy.run_path(str(ROOT/'scripts/check-qotom-graphics-bme-capture.py'))
P=G['P'];BASE=G['BASE'];FINAL=G['FINAL'];record=G['record']
STATE=BASE.replace(FINAL,record()+FINAL)
PHYSICAL=ROOT/'hardware/lab/observations/qotom-native-graphics-bme-20260912'

def bme(status=0,attempted=1,before=7,after=3):
    return (b'LEANOS-LAB/1 GRAPHICS-BME profile=qotom-valleyview-bme-v1 index=1 status='+
        str(status).encode()+b' attempted='+str(attempted).encode()+b' before='+
        str(before).encode()+b' after='+str(after).encode()+b'\n')

class Capture(unittest.TestCase):
    def test_success(self):
        projection,result=D['extract'](STATE.replace(FINAL,bme()+FINAL),P)
        self.assertEqual(projection,STATE)
        self.assertEqual((result['status'],result['write_attempted'],result['before_command'],
            result['after_command']),(0,1,7,3))
        self.assertFalse(result['dma_quarantine_established'] or result['transaction_drain_established'])
    def test_failures(self):
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-graphics-bme')
        values={3:(0,0,0),4:(0,0,0),5:(0,0,0),6:(1,7,0),
            7:(1,7,7),8:(1,7,3),9:(0,0,0),10:(0,0,0)}
        for status,args in values.items():
            _,result=D['extract'](STATE.replace(FINAL,bme(status,*args)+failure),P)
            self.assertEqual(result['status'],status)
    def test_rejections(self):
        good=bme()
        malformed=(good.replace(b'index=1',b'index=2'),good.replace(b'status=0',b'status=00'),
            good.replace(b'attempted=1',b'attempted=2'),good+good)
        for value in malformed:
            with self.assertRaises(ValueError):D['extract'](STATE.replace(FINAL,value+FINAL),P)
        with self.assertRaises(ValueError):D['extract'](STATE,P)
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-graphics-bme')
        with self.assertRaises(ValueError):D['extract'](STATE.replace(FINAL,bme()+failure),P)

    def test_retained_physical_capture(self):
        raw=(PHYSICAL/'cycle-1/serial.raw').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
            '4998a356f2daa79903d8d8c4a6242ce8ceec9ed88b68733318fb8834e65b6f34')
        self.assertEqual(raw.count(bme()),1)
        result=json.loads((PHYSICAL/'cycle-1/graphics-bme.json').read_text())
        self.assertEqual((result['status'],result['write_attempted'],
            result['before_command'],result['after_command']),(0,1,7,3))
        self.assertTrue(result['display_decode_preserved'])
        self.assertFalse(result['dma_quarantine_established'] or
            result['transaction_drain_established'])
        recovery=json.loads((PHYSICAL/'cycle-1/recovery.json').read_text())
        self.assertEqual(recovery['elf_sha256'],
            '7a5adf357d7bfd9d52839f84889e240680d2d1db7fdc43c0c4fcfdc5cbf638ca')
        self.assertTrue(recovery['request_consumed'])
        self.assertEqual(recovery['recovery'],'freebsd-ssh-restored')
        manifest=json.loads((PHYSICAL/'build-manifest.json').read_text())
        self.assertEqual(manifest['source_revision'],
            'd9a08d23f0a03224c219c637d70b1e62b2441a4d')
        self.assertFalse(manifest['source_dirty'])

    def test_retained_sticky_status_rejection(self):
        raw=(PHYSICAL/'broadcom-status-rejection/cycle-1/serial.raw').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
            '6db7ffc9898bbddaef448e670c106d2934a2b8c3e218bff43c1c7bcbbcef42ca')
        self.assertEqual(raw.count(b'PCIE-PENDING profile=qotom-pcie-pending-v1 '
            b'index=6 status=0 polls=2 device-status=16\n'),1)
        self.assertEqual(raw.count(b'BROADCOM-D3 profile=qotom-broadcom-d3-v1 '
            b'index=14 status=12 command-attempted=0'),1)
        self.assertNotIn(b'GRAPHICS-BME profile=',raw)

if __name__=='__main__':unittest.main()
