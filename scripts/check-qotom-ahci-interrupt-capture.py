"""Validate global interrupt masking without inferring SATA DMA containment."""
import re
import runpy
from pathlib import Path
D=runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-port-capture.py')))
PREFIX=b'LEANOS-LAB/1 AHCI-INTERRUPTS '
DEC=rb'(0|[1-9][0-9]{0,9})'


def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('AHCI interrupt bounds')
    lines=raw.splitlines(keepends=True)
    indices=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-ahci-interrupts\n'
    if not indices:
        _,prior=D['extract'](raw,protocol)
        if (prior is not None and prior['status']==0) or lines[-1]==failure:
            raise ValueError('missing AHCI interrupt observation')
        return raw,None
    if len(indices)!=1 or indices[0]!=len(lines)-2:
        raise ValueError('AHCI interrupt order or duplicates')
    projection=b''.join(lines[:indices[0]])+pending
    without_port,prior=D['extract'](projection,protocol)
    if prior is None or prior['status']:
        raise ValueError('AHCI interrupt without successful port observation')
    _,caps=D['D']['extract'](without_port,protocol)
    match=re.fullmatch(PREFIX+rb'profile=qotom-ahci-interrupts-v1 index=2 status='+DEC+
        rb' attempted='+DEC+rb' before='+DEC+rb' after='+DEC+rb'\n',lines[indices[0]])
    if not match:raise ValueError('AHCI interrupt framing')
    status,attempted,before,after=map(int,match.groups())
    if status>11 or status in (1,2) or attempted>1 or max(before,after)>0xffffffff:
        raise ValueError('AHCI interrupt bounds or impossible native status')
    if status<9 and (caps['control']!=0x80000002 or tuple(prior[k] for k in
            ('command_before','interrupt','task_file','sata_status','active','issued','command_after'))!=
            (6,0,0x50,0x123,0,0,6)):
        raise ValueError('AHCI interrupt helper without bound stopped profile')
    if status in (3,4,9,10,11):
        valid=(attempted,before,after)==(0,0,0)
    else:
        valid=attempted==1 and before==0x80000002
        if status in (0,8):valid=valid and after==0x80000000
        elif status in (5,6):valid=valid and after==0
        else:valid=valid and after!=0x80000000
    if not valid or lines[-1]!=(failure if status else pending):
        raise ValueError('AHCI interrupt payload or terminal contradiction')
    return projection,{'schema':'leanos-qotom-ahci-interrupt-observation-v1',
        'status':status,'write_attempted':attempted,'before_control':before,'after_control':after,
        'terminal_reason':'qotom-ahci-interrupts' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False}
