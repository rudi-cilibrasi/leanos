#!/usr/bin/env python3
import runpy
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
G=runpy.run_path(str(ROOT/'scripts/test-qotom-graphics-state-capture.py'))
D=runpy.run_path(str(ROOT/'scripts/check-qotom-graphics-bme-capture.py'))
P=G['P'];BASE=G['BASE'];FINAL=G['FINAL'];record=G['record']
STATE=BASE.replace(FINAL,record()+FINAL)

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

if __name__=='__main__':unittest.main()
