#!/usr/bin/env python3
"""Validate ordered Realtek BME clears without inferring DMA quarantine."""
import re
import runpy
from pathlib import Path

D = runpy.run_path(str(Path(__file__).with_name('check-qotom-realtek-state-capture.py')))
PREFIX = b'LEANOS-LAB/1 REALTEK-BME '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('Realtek BME capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-realtek-bme\n'
    if not indices:
        _, previous = D['extract'](raw,protocol)
        if (previous is not None and len(previous['functions']) == 2 and
                all(f['status'] == 0 for f in previous['functions'])) or lines[-1] == failure:
            raise ValueError('missing Realtek BME records')
        return raw,None
    if len(indices) > 2 or indices != list(range(len(lines)-len(indices)-1,len(lines)-1)):
        raise ValueError('Realtek BME record order')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection,protocol)
    if previous is None or len(previous['functions']) != 2 or any(f['status'] for f in previous['functions']):
        raise ValueError('Realtek BME without successful stopped-state observations')
    functions=[]
    for slot,position in enumerate(indices):
        match=re.fullmatch(PREFIX+rb'profile=qotom-realtek-bme-v1 index='+DEC+
            rb' status='+DEC+rb' attempted='+DEC+rb' before='+DEC+rb' after='+DEC+rb'\n',
            lines[position])
        if not match:
            raise ValueError('Realtek BME framing')
        index,status,attempted,before,after=map(int,match.groups())
        if index!=13+slot*2 or status>10 or status in (1,2) or attempted>1 or max(before,after)>65535:
            raise ValueError('Realtek BME scalar bounds')
        if status in (3,4,5,9,10):
            valid=(attempted,before,after)==(0,0,0)
        else:
            valid=attempted==1 and before==7
            if status==0:valid=valid and after==3
            elif status==6:valid=valid and after==0
            elif status==7:valid=valid and after!=3
        if not valid or (status and slot!=len(indices)-1):
            raise ValueError('Realtek BME result or writes after failure')
        functions.append({'index':index,'status':status,'write_attempted':attempted,
            'before_command':before,'after_command':after})
    failed=functions[-1]['status']!=0
    if (not failed and len(functions)!=2) or lines[-1]!=(failure if failed else pending):
        raise ValueError('Realtek BME incomplete success or terminal contradiction')
    return projection,{'schema':'leanos-qotom-realtek-bme-observation-v1','functions':functions,
        'terminal_reason':'qotom-realtek-bme' if failed else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False,'transaction_drain_established':False}
