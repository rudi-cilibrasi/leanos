#!/usr/bin/env python3
"""Validate the bounded graphics BME transition without claiming quarantine."""
import re
import runpy
from pathlib import Path

D=runpy.run_path(str(Path(__file__).with_name('check-qotom-graphics-state-capture.py')))
PREFIX=b'LEANOS-LAB/1 GRAPHICS-BME '
DEC=rb'(0|[1-9][0-9]{0,9})'

def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):raise ValueError('graphics BME capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-graphics-bme\n'
    if not positions:
        _,previous=D['extract'](raw,protocol)
        if (previous is not None and previous['status']==0) or lines[-1]==failure:
            raise ValueError('missing graphics BME record')
        return raw,None
    if positions!=[len(lines)-2]:raise ValueError('graphics BME record order')
    match=re.fullmatch(PREFIX+rb'profile=qotom-valleyview-bme-v1 index='+DEC+
        rb' status='+DEC+rb' attempted='+DEC+rb' before='+DEC+rb' after='+DEC+b'\n',
        lines[-2])
    if not match:raise ValueError('graphics BME framing')
    index,status,attempted,before,after=map(int,match.groups())
    if index!=1 or status>10 or status in (1,2) or attempted>1 or max(before,after)>65535:
        raise ValueError('graphics BME scalar bounds')
    projection=b''.join(lines[:-2])+pending
    _,previous=D['extract'](projection,protocol)
    if previous is None or previous['status']!=0 or not previous['stable'] or \
       not previous['rings_invalid_and_idle'] or not previous['rings_empty']:
        raise ValueError('graphics BME without quiet graphics observation')
    if status in (3,4,5,9,10):valid=(attempted,before,after)==(0,0,0)
    elif status==6:valid=(attempted,before,after)==(1,7,0)
    elif status==7:valid=attempted==1 and before==7 and after!=3
    else:valid=attempted==1 and before==7 and (status==8 or after==3)
    if not valid:raise ValueError('graphics BME result')
    if lines[-1]!=(pending if status==0 else failure):
        raise ValueError('graphics BME terminal contradiction')
    return projection,{'schema':'leanos-qotom-graphics-bme-observation-v1',
        'index':index,'status':status,'write_attempted':attempted,
        'before_command':before,'after_command':after,
        'display_decode_preserved':True,'hardware_operations_replayed':False,
        'firmware_exclusion_established':False,'dma_quarantine_established':False,
        'transaction_drain_established':False,
        'terminal_reason':'qotom-platform-pending' if status==0 else 'qotom-graphics-bme'}
