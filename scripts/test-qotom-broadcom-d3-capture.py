#!/usr/bin/env python3
import json
import runpy
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
CAP=ROOT/'hardware/lab/observations/qotom-native-broadcom-d3-20260912'
D=runpy.run_path(str(ROOT/'scripts/check-qotom-broadcom-d3-capture.py'))
R=runpy.run_path(str(ROOT/'scripts/run-qotom-recovery-lab.py'))
P=R['cpu_replay_module'](True).load_protocol(CAP/'diagnostic-protocol.tsv')
events=[json.loads(s) for s in (CAP/'cycle-1/events.jsonl').read_text().splitlines()]
RAW=b''.join(bytes.fromhex(e['hex']) for e in events)
FINAL=P['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
END=RAW.index(FINAL)+len(FINAL)
BASE,PHYSICAL=D['extract'](RAW[:END],P)

def record(status=0,values=(1,6,0,2,25,0x4008,1,0x400b)):
    names=('command-attempted','command-before','command-after','polls','device-status',
        'pmcsr-before','d3-attempted','pmcsr-after')
    return ('LEANOS-LAB/1 BROADCOM-D3 profile=qotom-broadcom-d3-v1 index=14 status='+str(status)+
        ''.join(f' {name}={value}' for name,value in zip(names,values))+'\n').encode()

class Capture(unittest.TestCase):
    def test_success(self):
        self.assertEqual(PHYSICAL['status'],0)
        self.assertTrue(PHYSICAL['command_disabled_observed'] and PHYSICAL['d3hot_observed'])
        raw=BASE.replace(FINAL,record()+FINAL)
        projection,result=D['extract'](raw,P)
        self.assertEqual(projection,BASE)
        self.assertTrue(result['command_disabled_observed'] and result['d3hot_observed'])
        self.assertFalse(result['posted_write_drain_established'])
    def test_reachable_failures(self):
        failure=FINAL.replace(b'qotom-platform-pending',b'qotom-broadcom-d3')
        values={1:(0,0,0,0,0,0,0,0),2:(0,0,0,0,0,0,0,0),3:(0,0,0,0,0,0,0,0),
            4:(0,0,0,0,0,0,0,0),5:(1,6,0,0,0,0,0,0),6:(1,6,7,0,0,0,0,0),
            7:(1,6,0,100,57,0,0,0),8:(1,6,0,2,25,0,0,0),
            9:(1,6,0,2,25,0x4008,1,0),10:(1,6,0,2,25,0x4008,1,0x4008),
            11:(1,6,0,2,25,0x4008,1,0x400b),12:(0,0,0,0,0,0,0,0),13:(0,0,0,0,0,0,0,0)}
        for status,value in values.items():
            raw=BASE.replace(FINAL,record(status,value)+failure)
            _,result=D['extract'](raw,P);self.assertEqual(result['status'],status)
            with self.assertRaises(ValueError):D['extract'](raw.replace(failure,FINAL),P)
    def test_rejections(self):
        good=record()
        bad_records=(good.replace(b'index=14',b'index=13',1),
            good.replace(b'status=0',b'status=00',1),
            good.replace(b'command-after=0',b'command-after=4',1),
            good.replace(b'polls=2',b'polls=1',1),
            good.replace(b'device-status=25',b'device-status=57',1),
            good.replace(b'pmcsr-after=16395',b'pmcsr-after=16392',1),
            good+good)
        mutations=tuple(BASE.replace(FINAL,bad+FINAL) for bad in bad_records)+(
            BASE.replace(FINAL,good+FINAL.replace(
                b'qotom-platform-pending',b'qotom-broadcom-d3',1)),
            BASE.replace(FINAL,record(7)+FINAL.replace(
                b'qotom-platform-pending',b'qotom-broadcom-d3',1)),
            BASE.replace(FINAL,record(10)+FINAL.replace(
                b'qotom-platform-pending',b'qotom-broadcom-d3',1)))
        for raw in mutations:
            with self.assertRaises(ValueError):D['extract'](raw,P)

if __name__=='__main__':unittest.main()
