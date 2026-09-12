#!/usr/bin/env python3
"""Validate ordered root-port request-gating results without inferring drain."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-txe-status-capture.py')))
PREFIX = b'LEANOS-LAB/1 ROOTPORT-BME '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('root-port capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-rootport-bme\n'
    if not indices:
        _, previous = D['extract'](raw,protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing root-port records')
        return raw,None
    if len(indices)>4 or indices != list(range(len(lines)-len(indices)-1,len(lines)-1)):
        raise ValueError('root-port record order')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection,protocol)
    if previous is None or previous['status']:
        raise ValueError('root-port without successful TXE status')
    functions=[]
    for slot,position in enumerate(indices):
        match=re.fullmatch(PREFIX+rb'profile=qotom-rootport-bme-v1 index='+DEC+
            rb' status='+DEC+rb' attempted='+DEC+rb' before='+DEC+rb' after='+DEC+rb'\n',lines[position])
        if not match:
            raise ValueError('root-port framing')
        index,status,attempted,before,after=map(int,match.groups())
        if index!=6+slot or status>8 or status in (1,2) or attempted>1 or max(before,after)>65535:
            raise ValueError('root-port scalar bounds')
        if status<8:
            prefix=protocol['PCI-HEADER'].encode()+f' codec=1 index={index} width=19 words='.encode()
            headers=[line for line in lines if line.startswith(prefix)]
            if len(headers)!=1:
                raise ValueError('missing root-port header')
            words=list(map(int,headers[0][len(prefix):].strip().split(b',')))
            if len(words)!=19 or words[:3]!=[0,28,slot] or words[3]!=0x0f488086+slot*0x20000 or \
                    words[4]&0xffff!=7 or words[5]!=0x0604000e or words[6]&0xff0000!=0x810000:
                raise ValueError('root-port header binding')
            pcie_prefix=f'LEANOS-LAB/1 PCIE-DEVICE profile=qotom-pcie-device-v1 index={index} '.encode()
            samples=[line for line in lines if line.startswith(pcie_prefix)]
            sample=re.fullmatch(pcie_prefix+rb'status=0 offset=64 capability=32768 control-status='+DEC+rb'\n',samples[0]) if len(samples)==1 else None
            if not sample or int(sample.group(1))&~0x1f0000:
                raise ValueError('root-port prior PCIe binding')
        if status in (3,4,8):
            valid=(attempted,before,after)==(0,0,0)
        else:
            valid=attempted==1 and before==7
            if status==0:valid=valid and after==3
            elif status==5:valid=valid and after==0
            elif status==6:valid=valid and after!=3
        if not valid or (status and slot!=len(indices)-1):
            raise ValueError('root-port result or writes after failure')
        functions.append({'index':index,'status':status,'write_attempted':attempted,
            'before_command':before,'after_command':after})
    failed=functions[-1]['status']!=0
    if (not failed and len(functions)!=4) or lines[-1]!=(failure if failed else pending):
        raise ValueError('root-port incomplete success or terminal contradiction')
    return projection,{'schema':'leanos-qotom-rootport-bme-observation-v1','functions':functions,
        'terminal_reason':'qotom-rootport-bme' if failed else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False,'transaction_drain_established':False}
