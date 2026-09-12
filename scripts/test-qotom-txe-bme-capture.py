#!/usr/bin/env python3
import hashlib
import json
import runpy
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
G=runpy.run_path(str(ROOT/'scripts/test-qotom-graphics-bme-capture.py'))
D=runpy.run_path(str(ROOT/'scripts/check-qotom-txe-bme-capture.py'))
P=G['P'];FINAL=G['FINAL'];bme=G['bme']
STATE=G['STATE'].replace(FINAL,bme()+FINAL)
PHYSICAL=ROOT/'hardware/lab/observations/qotom-native-txe-bme-20260912'

def record(status=0,attempted=1,before=0x106,after=0x102):
    return (b'LEANOS-LAB/1 TXE-BME profile=qotom-txe-host-bme-v1 index=4 status='+
        str(status).encode()+b' attempted='+str(attempted).encode()+b' before='+
        str(before).encode()+b' after='+str(after).encode()+b'\n')

class Capture(unittest.TestCase):
    def test_success(self):
        projection,result=D['extract'](STATE.replace(FINAL,record()+FINAL),P)
        self.assertEqual(projection,STATE)
        self.assertEqual((result['status'],result['write_attempted'],
            result['before_command'],result['after_command']),(0,1,0x106,0x102))
        self.assertTrue(result['host_visible_bme_cleared'])
        self.assertFalse(result['txe_private_dma_stopped'] or
            result['dma_quarantine_established'])
    def test_failures(self):
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-txe-bme')
        values={3:(0,0,0),4:(0,0,0),5:(0,0,0),6:(1,0x106,0),
            7:(1,0x106,0x106),8:(1,0x106,0x102),9:(0,0,0)}
        for status,args in values.items():
            _,result=D['extract'](STATE.replace(FINAL,record(status,*args)+failure),P)
            self.assertEqual(result['status'],status)
    def test_rejections(self):
        good=record();failure=FINAL.replace(b'qotom-platform-pending',b'qotom-txe-bme')
        for bad in (good.replace(b'index=4',b'index=3'),
                    good.replace(b'status=0',b'status=00'),
                    good.replace(b'attempted=1',b'attempted=2'),good+good):
            with self.assertRaises(ValueError):D['extract'](STATE.replace(FINAL,bad+FINAL),P)
        with self.assertRaises(ValueError):D['extract'](STATE,P)
        with self.assertRaises(ValueError):D['extract'](STATE.replace(FINAL,good+failure),P)

    def test_retained_physical_capture(self):
        raw=(PHYSICAL/'cycle-1/serial.raw').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
            '92be7c5330bc9b9285e4be55131f2c97f70d24dc8b62f1330fe5f31e8283e13a')
        self.assertEqual(raw.count(record()),1)
        result=json.loads((PHYSICAL/'cycle-1/txe-bme.json').read_text())
        self.assertEqual((result['status'],result['write_attempted'],
            result['before_command'],result['after_command']),(0,1,0x106,0x102))
        self.assertTrue(result['host_visible_bme_cleared'])
        self.assertFalse(result['txe_private_dma_stopped'] or
            result['firmware_exclusion_established'] or
            result['dma_quarantine_established'] or
            result['transaction_drain_established'])
        recovery=json.loads((PHYSICAL/'cycle-1/recovery.json').read_text())
        self.assertEqual(recovery['elf_sha256'],
            'c2cbec01015efb0057c2c844e354e5ba40531c0642bdbe09ffe5b15a0b6f7931')
        self.assertTrue(recovery['request_consumed'])
        self.assertEqual(recovery['recovery'],'freebsd-ssh-restored')
        build=json.loads((PHYSICAL/'build-manifest.json').read_text())
        self.assertEqual(build['source_revision'],
            'bd16603d8be2ca58de8eafde93f91cb18e79a4d3')
        self.assertEqual(build['prepared_revision'],
            '4f6fe9358eaf2a6274f152005578957335acd724')
        self.assertFalse(build['source_dirty'])

    def test_retained_stale_grub_digest_rejection(self):
        raw=(PHYSICAL/'stale-grub-rejection/cycle-1/serial.raw').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
            '2aec611884e7dd5676744c292eec80e583b9c195f1c88a0a8e89762b082760a6')
        self.assertEqual(raw.count(
            b'WATCHDOG-WINDOW expired-or-invalid=1 fallback=freebsd'),1)
        self.assertNotIn(b'TXE-BME profile=',raw)

if __name__=='__main__':unittest.main()
