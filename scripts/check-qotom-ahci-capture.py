"""Validate raw AHCI capability/control observations after PCIe capture."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-pcie-device-capture.py')))
PREFIX = b'LEANOS-LAB/1 AHCI-CAPS '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('AHCI capture bounds')
    lines=raw.splitlines(keepends=True)
    indices=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-ahci-capabilities\n'
    if not indices:
        _,previous=D['extract'](raw,protocol)
        if (previous is not None and previous['terminal_reason']=='qotom-platform-pending') or lines[-1]==failure:
            raise ValueError('missing AHCI observation')
        return raw,None
    if len(indices)!=1 or indices[0]!=len(lines)-2:
        raise ValueError('AHCI order or duplicates')
    projection=b''.join(lines[:indices[0]])+pending
    _,previous=D['extract'](projection,protocol)
    if previous is None or previous['terminal_reason']!='qotom-platform-pending':
        raise ValueError('AHCI without successful PCIe capture')
    match=re.fullmatch(PREFIX+rb'profile=qotom-ahci-v1 index=2 status='+DEC+
        rb' capability='+DEC+rb' control='+DEC+rb' ports='+DEC+rb' version='+DEC+rb' extended='+DEC+rb'\n',lines[indices[0]])
    if not match:
        raise ValueError('AHCI framing')
    status,*values=map(int,match.groups())
    if status>7 or status in (1,2) or max(values)>0xffffffff:
        raise ValueError('AHCI bounds or impossible native argument/header failure')
    if status:
        if any(values):raise ValueError('AHCI failed observation publishes payload')
    elif 0xffffffff in values:
        raise ValueError('AHCI all-ones payload')
    # A helper invocation follows the exact immutable header binding at arm.
    # Arm failure itself may report rejection of this binding.
    if status!=7:
        prefix=protocol['PCI-HEADER'].encode()+b' codec=1 index=2 width=19 words='
        headers=[line for line in lines if line.startswith(prefix)]
        if len(headers)!=1:raise ValueError('AHCI missing PCI header')
        words=list(map(int,headers[0][len(prefix):].strip().split(b',')))
        if (len(words)!=19 or words[:3]!=[0,19,0] or words[3]!=0x0f238086 or
                words[5]!=0x0106010e or words[6]&0x00ff0000 or not words[4]&2 or words[12]!=0xd0916000):
            raise ValueError('AHCI helper without bound header')
    if lines[-1]!=(failure if status else pending):
        raise ValueError('AHCI terminal contradiction')
    return projection,{'schema':'leanos-qotom-ahci-capability-observation-v1','status':status,
        **dict(zip(('capability','control','ports','version','extended'),values)),
        'terminal_reason':'qotom-ahci-capabilities' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'dma_quarantine_established':False}
