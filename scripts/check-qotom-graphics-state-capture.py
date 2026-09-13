#!/usr/bin/env python3
"""Validate the bounded Valleyview graphics-ring protected record."""
import re
import runpy
from pathlib import Path

D=runpy.run_path(str(Path(__file__).with_name('check-qotom-broadcom-d3-capture.py')))
PREFIX=b'LEANOS-LAB/1 GRAPHICS-STATE '
DEC=rb'(0|[1-9][0-9]{0,9})'

def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):raise ValueError('graphics state capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-graphics-state\n'
    if not positions:
        _,previous=D['extract'](raw,protocol)
        if previous is not None or lines[-1]==failure:raise ValueError('missing graphics state record')
        return raw,None
    if positions!=[len(lines)-2]:raise ValueError('graphics state record order')
    pattern=(PREFIX+b'profile=qotom-valleyview-rings-v1 index='+DEC+
        b' status='+DEC+b' width='+DEC+b' words='+DEC)
    for _ in range(29):pattern+=b','+DEC
    match=re.fullmatch(pattern+b'\n',lines[-2])
    if not match:raise ValueError('graphics state framing')
    fields=list(map(int,match.groups()));index,status,width=fields[:3];words=fields[3:]
    if index!=1 or status>7 or width!=30 or any(word>UINT32_MAX for word in words):
        raise ValueError('graphics state scalar bounds')
    projection=b''.join(lines[:-2])+pending
    _,previous=D['extract'](projection,protocol)
    if previous is None or previous['status']!=0 or not previous['d3hot_observed']:
        raise ValueError('graphics state without Broadcom D3hot success')
    if status==0:
        if lines[-1]!=pending:raise ValueError('graphics success terminal contradiction')
    elif any(words) or lines[-1]!=failure:
        raise ValueError('graphics failure result or terminal contradiction')
    samples=[]
    for sample in range(2):
        engines=[]
        for engine,name in enumerate(('rcs','vcs','bcs')):
            values=words[sample*15+engine*5:sample*15+engine*5+5]
            engines.append({'engine':name,'tail':values[0],'head':values[1],
                'start':values[2],'control':values[3],'mode':values[4]})
        samples.append(engines)
    accepted=status==0
    stable=accepted and all(samples[0][i]==samples[1][i] for i in range(3))
    idle=accepted and all(not (engine['control']&1) and (engine['mode']&0x200)
             for sample in samples for engine in sample)
    empty=accepted and all(engine['head']==engine['tail'] for sample in samples for engine in sample)
    return projection,{'schema':'leanos-qotom-graphics-state-observation-v1',
        'index':index,'status':status,'samples':samples,'stable':stable,
        'rings_invalid_and_idle':idle,'rings_empty':empty,
        'display_decode_preserved':accepted,'graphics_bme_preserved':accepted,
        'hardware_operations_replayed':False,'dma_quarantine_established':False,
        'firmware_exclusion_established':False,
        'terminal_reason':'qotom-platform-pending' if status==0 else 'qotom-graphics-state'}

UINT32_MAX=4294967295
