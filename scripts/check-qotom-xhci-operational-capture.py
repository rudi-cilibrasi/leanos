"""Validate bounded raw operational samples; do not infer controller quiescence."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-smi-capture.py')))
PREFIX = b'LEANOS-LAB/1 XHCI-OPERATIONAL '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('operational capture bounds')
    lines=raw.splitlines(keepends=True)
    indices=[i for i,l in enumerate(lines) if l.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-xhci-operational\n'
    if not indices:
        _,smi=D['extract'](raw,protocol)
        if (smi is not None and smi['status']==0) or lines[-1]==failure:
            raise ValueError('missing operational observation')
        return raw,None
    if len(indices)!=1 or indices[0]!=len(lines)-2:
        raise ValueError('operational record order or duplicates')
    projection=b''.join(lines[:indices[0]])+pending
    _,smi=D['extract'](projection,protocol)
    if smi is None or smi['status']:
        raise ValueError('operational sample without successful SMI observation')
    match=re.fullmatch(PREFIX+rb'profile=qotom-xhci-operational-v1 index=3 status='+DEC+
        rb' sampled='+DEC+rb' command='+DEC+rb' final='+DEC+rb'\n',lines[indices[0]])
    if not match:
        raise ValueError('operational framing')
    status,before,command,after=map(int,match.groups())
    if status>11 or status in (1,2) or max(before,command,after)>0xffffffff:
        raise ValueError('operational bounds or impossible native status')
    if status<9 and (smi['before_control'],smi['after_control'])!=(0x2000,0):
        raise ValueError('operational reader without exact SMI binding')
    valid=(before,command,after)==(0,0,0) if status else (
        max(before,command,after)!=0xffffffff and not (before|after)&0x800)
    if not valid or lines[-1]!=(failure if status else pending):
        raise ValueError('operational result/terminal contradiction')
    return projection,{'schema':'leanos-qotom-xhci-operational-observation-v1',
        'status':status,'status_before':before,'command':command,'status_after':after,
        'terminal_reason':'qotom-xhci-operational' if status else 'qotom-platform-pending',
        'atomic_snapshot':False,'hardware_operations_replayed':False,
        'firmware_exclusion_established':False,'dma_quarantine_established':False}
