#!/usr/bin/env python3
"""Validate ordered, routed Realtek observations without inferring shutdown."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-rootport-bme-capture.py')))
PREFIX = b'LEANOS-LAB/1 REALTEK-STATE '
DEC = rb'(0|[1-9][0-9]{0,9})'
NAMES = ('transmit_before','command_before','interrupt_mask','receive','command_after','transmit_after')


def extract(raw, protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('Realtek capture bounds')
    lines=raw.splitlines(keepends=True)
    indices=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-realtek-state\n'
    if not indices:
        _,previous=D['extract'](raw,protocol)
        if (previous is not None and all(f['status']==0 for f in previous['functions'])) or lines[-1]==failure:
            raise ValueError('missing Realtek records')
        return raw,None
    if len(indices)>2 or indices!=list(range(len(lines)-len(indices)-1,len(lines)-1)):
        raise ValueError('Realtek record order')
    projection=b''.join(lines[:indices[0]])+pending
    _,previous=D['extract'](projection,protocol)
    if previous is None or len(previous['functions'])!=4 or any(f['status'] for f in previous['functions']):
        raise ValueError('Realtek without successful root ports')
    def header(index):
        prefix=protocol['PCI-HEADER'].encode()+f' codec=1 index={index} width=19 words='.encode()
        found=[line for line in lines if line.startswith(prefix)]
        if len(found)!=1:raise ValueError('missing Realtek route header')
        words=list(map(int,found[0][len(prefix):].strip().split(b',')))
        if len(words)!=19:raise ValueError('Realtek route header width')
        return words
    functions=[]
    for slot,position in enumerate(indices):
        pattern=PREFIX+rb'profile=qotom-realtek-state-v1 index='+DEC+rb' status='+DEC
        for name in NAMES:pattern+=b' '+name.replace('_','-').encode()+b'='+DEC
        match=re.fullmatch(pattern+rb'\n',lines[position])
        if not match:raise ValueError('Realtek framing')
        index,status,*values=map(int,match.groups())
        if index!=13+slot*2 or status>13 or status in (1,2) or any(v>0xffffffff for v in values):
            raise ValueError('Realtek scalar bounds')
        if status!=13:
            h=header(index);bus=1+slot*2;bar=0xd0804000 if bus==1 else 0xd0604000
            if h[:3]!=[bus,0,0] or h[3]!=0x816810ec or h[4]&0xffff!=7 or h[5]!=0x02000007 or \
                    h[6]&0xff0000 or h[9]!=(bar|4) or h[10] or h[11]!=((bar-0x4000)|12) or h[12]:
                raise ValueError('Realtek endpoint binding')
            if status!=10:
                h=header(6+slot*2)
                if h[:3]!=[0,28,slot*2] or h[9]!=((bus<<16)|(bus<<8)) or \
                        h[11]!=(0xd080d080 if bus==1 else 0xd060d060) or h[12]!=0x1fff1 or h[13] or h[14]:
                    raise ValueError('Realtek bridge binding')
        if status:
            if any(values) or slot!=len(indices)-1:raise ValueError('Realtek failed output or reads after failure')
        else:
            for i,value in enumerate(values):
                maximum=255 if i in (1,4) else 65535 if i==2 else 0xffffffff
                if value>=maximum:raise ValueError('Realtek absent/width')
                if i in (0,5) and value&0x7cc00000!=0x2c800000:raise ValueError('Realtek chip revision')
                if i in (1,4) and value&16:raise ValueError('Realtek reset active')
        functions.append({'index':index,'status':status,**dict(zip(NAMES,values))})
    failed=functions[-1]['status']!=0
    if (not failed and len(functions)!=2) or lines[-1]!=(failure if failed else pending):
        raise ValueError('Realtek incomplete success or terminal contradiction')
    return projection,{'schema':'leanos-qotom-realtek-state-observation-v1','functions':functions,
        'terminal_reason':'qotom-realtek-state' if failed else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False,'transaction_drain_established':False}
