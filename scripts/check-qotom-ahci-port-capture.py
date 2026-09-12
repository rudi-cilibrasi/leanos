"""Validate AHCI port samples without inferring controller quiescence."""
import re
import runpy
from pathlib import Path
D=runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-capture.py')))
PREFIX=b'LEANOS-LAB/1 AHCI-PORT '
DEC=rb'(0|[1-9][0-9]{0,9})'
NAMES=('command-before','interrupt','task-file','sata-status','active','issued','command-after')


def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('AHCI port bounds')
    lines=raw.splitlines(keepends=True)
    indices=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-ahci-port\n'
    if not indices:
        _,prior=D['extract'](raw,protocol)
        if (prior is not None and prior['status']==0) or lines[-1]==failure:
            raise ValueError('missing AHCI port observation')
        return raw,None
    if len(indices)!=1 or indices[0]!=len(lines)-2:
        raise ValueError('AHCI port order or duplicates')
    projection=b''.join(lines[:indices[0]])+pending
    _,prior=D['extract'](projection,protocol)
    if prior is None or prior['status']:
        raise ValueError('AHCI port without accepted global observation')
    pattern=PREFIX+rb'profile=qotom-ahci-port-v1 index=2 port=1 status='+DEC
    pattern+=b''.join(b' '+name.encode()+b'='+DEC for name in NAMES)+b'\n'
    match=re.fullmatch(pattern,lines[indices[0]])
    if not match:raise ValueError('AHCI port framing')
    status,*values=map(int,match.groups())
    if status>9 or status in (1,2) or max(values)>0xffffffff:
        raise ValueError('AHCI port bounds or impossible native status')
    if status<8 and (tuple(prior[k] for k in ('capability','ports','version','extended')) !=
            (0xc720ff01,2,0x10300,0x38) or prior['control'] not in (0x80000000,0x80000002)):
        raise ValueError('AHCI port helper without bound global profile')
    if (status and any(values)) or (not status and 0xffffffff in values):
        raise ValueError('AHCI port payload contradiction')
    if lines[-1]!=(failure if status else pending):
        raise ValueError('AHCI port terminal contradiction')
    return projection,{'schema':'leanos-qotom-ahci-port-observation-v1','status':status,
        **dict(zip((n.replace('-','_') for n in NAMES),values)),
        'terminal_reason':'qotom-ahci-port' if status else 'qotom-platform-pending',
        'atomic_snapshot':False,'hardware_operations_replayed':False,'dma_quarantine_established':False}
