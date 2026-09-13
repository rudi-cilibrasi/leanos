#!/usr/bin/env python3
"""Validate the TXE host-visible BME transition without claiming TXE DMA stop."""
import re
import runpy
from pathlib import Path

D=runpy.run_path(str(Path(__file__).with_name('check-qotom-graphics-bme-capture.py')))
PREFIX=b'LEANOS-LAB/1 TXE-BME '
DEC=rb'(0|[1-9][0-9]{0,9})'

def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):raise ValueError('TXE BME capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-txe-bme\n'
    if not positions:
        _,previous=D['extract'](raw,protocol)
        if (previous is not None and previous['status']==0) or lines[-1]==failure:
            raise ValueError('missing TXE BME record')
        return raw,None
    if positions!=[len(lines)-2]:raise ValueError('TXE BME record order')
    match=re.fullmatch(PREFIX+rb'profile=qotom-txe-host-bme-v1 index='+DEC+
        rb' status='+DEC+rb' attempted='+DEC+rb' before='+DEC+rb' after='+DEC+b'\n',
        lines[-2])
    if not match:raise ValueError('TXE BME framing')
    index,status,attempted,before,after=map(int,match.groups())
    if index!=4 or status>9 or status in (1,2) or attempted>1 or max(before,after)>65535:
        raise ValueError('TXE BME scalar bounds')
    projection=b''.join(lines[:-2])+pending
    _,previous=D['extract'](projection,protocol)
    if previous is None or previous['status']!=0 or previous['after_command']!=3:
        raise ValueError('TXE BME without successful graphics BME transition')
    if status in (3,4,5,9):valid=(attempted,before,after)==(0,0,0)
    elif status==6:valid=(attempted,before,after)==(1,0x106,0)
    elif status==7:valid=attempted==1 and before==0x106 and after!=0x102
    else:valid=attempted==1 and before==0x106 and (status==8 or after==0x102)
    if not valid:raise ValueError('TXE BME result')
    if lines[-1]!=(pending if status==0 else failure):
        raise ValueError('TXE BME terminal contradiction')
    return projection,{'schema':'leanos-qotom-txe-host-bme-observation-v1',
        'index':index,'status':status,'write_attempted':attempted,
        'before_command':before,'after_command':after,
        'memory_decode_preserved':True,'serr_enable_preserved':True,
        'hardware_operations_replayed':False,'host_visible_bme_cleared':status==0,
        'txe_private_dma_stopped':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False,'transaction_drain_established':False,
        'terminal_reason':'qotom-platform-pending' if status==0 else 'qotom-txe-bme'}
