#!/usr/bin/env python3
import json
import runpy
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
CAP=ROOT/'hardware/lab/observations/qotom-native-broadcom-d3-20260912'
D=runpy.run_path(str(ROOT/'scripts/check-qotom-graphics-state-capture.py'))
R=runpy.run_path(str(ROOT/'scripts/run-qotom-recovery-lab.py'))
P=R['cpu_replay_module'](True).load_protocol(CAP/'diagnostic-protocol.tsv')
events=[json.loads(line) for line in (CAP/'cycle-1/events.jsonl').read_text().splitlines()]
raw=b''.join(bytes.fromhex(event['hex']) for event in events)
FINAL=P['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
BASE=raw[:raw.index(FINAL)+len(FINAL)]

def record(status=0,words=None):
    if words is None:words=([0,0,0,0,0x200]*3)*2
    return (b'LEANOS-LAB/1 GRAPHICS-STATE profile=qotom-valleyview-rings-v1 '
        b'index=1 status='+str(status).encode()+b' width=30 words='+
        b','.join(str(word).encode() for word in words)+b'\n')

class Capture(unittest.TestCase):
    def test_success(self):
        projection,result=D['extract'](BASE.replace(FINAL,record()+FINAL),P)
        self.assertEqual(projection,BASE)
        self.assertTrue(result['stable'] and result['rings_invalid_and_idle'] and result['rings_empty'])
        self.assertTrue(result['display_decode_preserved'] and result['graphics_bme_preserved'])
        self.assertFalse(result['dma_quarantine_established'])
    def test_dynamic_observation(self):
        words=list(range(30));words[4]=words[9]=words[14]=0x200
        _,result=D['extract'](BASE.replace(FINAL,record(words=words)+FINAL),P)
        self.assertFalse(result['stable'] or result['rings_empty'])
    def test_failures(self):
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-graphics-state')
        for status in range(1,8):
            _,result=D['extract'](BASE.replace(FINAL,record(status,[0]*30)+failure),P)
            self.assertEqual(result['status'],status)
    def test_rejections(self):
        good=record()
        bad=(good.replace(b'index=1',b'index=2',1),
             good.replace(b'width=30',b'width=29',1),
             good.replace(b'status=0',b'status=00',1),
             good.replace(b'words=0',b'words=4294967296',1),
             good+good)
        for item in bad:
            with self.assertRaises(ValueError):D['extract'](BASE.replace(FINAL,item+FINAL),P)
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-graphics-state')
        with self.assertRaises(ValueError):D['extract'](BASE.replace(FINAL,record(1)+failure),P)

if __name__=='__main__':unittest.main()
