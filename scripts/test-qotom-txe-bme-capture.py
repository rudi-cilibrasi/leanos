#!/usr/bin/env python3
import runpy
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
G=runpy.run_path(str(ROOT/'scripts/test-qotom-graphics-bme-capture.py'))
D=runpy.run_path(str(ROOT/'scripts/check-qotom-txe-bme-capture.py'))
P=G['P'];FINAL=G['FINAL'];bme=G['bme']
STATE=G['STATE'].replace(FINAL,bme()+FINAL)

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

if __name__=='__main__':unittest.main()
