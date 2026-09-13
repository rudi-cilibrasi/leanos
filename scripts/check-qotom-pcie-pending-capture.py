#!/usr/bin/env python3
"""Validate bounded post-BME PCIe Transactions Pending observations."""
import re
import runpy
from pathlib import Path

D = runpy.run_path(str(Path(__file__).with_name('check-qotom-realtek-bme-capture.py')))
PREFIX = b'LEANOS-LAB/1 PCIE-PENDING '
PRIOR_PREFIX = b'LEANOS-LAB/1 PCIE-DEVICE '
DEC = rb'(0|[1-9][0-9]{0,9})'
INDICES = (6,7,8,9,13,15)


def prior_device_statuses(lines, end):
    pattern = re.compile(PRIOR_PREFIX +
        rb'profile=qotom-pcie-device-v1 index=' + DEC + rb' status=' + DEC +
        rb' offset=' + DEC + rb' capability=' + DEC + rb' control-status=' + DEC + rb'\n')
    statuses = {}
    for line in lines[:end]:
        if not line.startswith(PRIOR_PREFIX):
            continue
        match = pattern.fullmatch(line)
        if not match:
            raise ValueError('PCIe pending prior framing')
        index, status, _, _, control_status = map(int, match.groups())
        if index in INDICES:
            if index in statuses or status != 0 or control_status > 0xffffffff:
                raise ValueError('PCIe pending prior observation')
            statuses[index] = control_status >> 16
    if set(statuses) != set(INDICES):
        raise ValueError('PCIe pending missing prior observations')
    return statuses


def extract(raw, protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('PCIe pending capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-pcie-pending\n'
    if not positions:
        _,previous=D['extract'](raw,protocol)
        if (previous is not None and len(previous['functions'])==2 and
                all(f['status']==0 for f in previous['functions'])) or lines[-1]==failure:
            raise ValueError('missing PCIe pending records')
        return raw,None
    if len(positions)>len(INDICES) or positions!=list(range(len(lines)-len(positions)-1,len(lines)-1)):
        raise ValueError('PCIe pending record order')
    prior_statuses=prior_device_statuses(lines,positions[0])
    projection=b''.join(lines[:positions[0]])+pending
    _,previous=D['extract'](projection,protocol)
    if previous is None or len(previous['functions'])!=2 or any(f['status'] for f in previous['functions']):
        raise ValueError('PCIe pending without successful Realtek BME')
    functions=[]
    for slot,position in enumerate(positions):
        match=re.fullmatch(PREFIX+rb'profile=qotom-pcie-pending-v1 index='+DEC+
            rb' status='+DEC+rb' polls='+DEC+rb' device-status='+DEC+rb'\n',lines[position])
        if not match:raise ValueError('PCIe pending framing')
        index,status,polls,device_status=map(int,match.groups())
        if index!=INDICES[slot] or status>9 or status==1 or polls>100 or device_status>65535:
            raise ValueError('PCIe pending scalar bounds')
        base=prior_statuses[index]&~0x20
        if polls==0:
            valid=device_status==0
        else:
            valid=device_status in (base,base|0x20)
        if status==0:
            valid=valid and 2<=polls<=100 and device_status==base
        elif status in (2,8,9):
            valid=valid and polls==0 and device_status==0
        elif status==6:
            valid=valid and 1<=polls<100
        elif status==7:
            valid=valid and polls==100 and device_status==(base|0x20)
        else:
            valid=valid and polls<100
        if not valid or (status and slot!=len(positions)-1):
            raise ValueError('PCIe pending result or observations after failure')
        functions.append({'index':index,'status':status,'polls':polls,
            'device_status':device_status,'transactions_pending':bool(device_status&0x20)})
    failed=functions[-1]['status']!=0
    if (not failed and len(functions)!=len(INDICES)) or lines[-1]!=(failure if failed else pending):
        raise ValueError('PCIe pending incomplete success or terminal contradiction')
    return projection,{'schema':'leanos-qotom-pcie-pending-observation-v1',
        'functions':functions,
        'terminal_reason':'qotom-pcie-pending' if failed else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False,'nonposted_quiet_observed':not failed,
        'posted_write_drain_established':False,'transaction_drain_established':False}
