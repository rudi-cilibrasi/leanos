#!/usr/bin/env python3
"""Validate the bounded Broadcom Command-off/D3hot protected record."""
import re
import runpy
from pathlib import Path

D=runpy.run_path(str(Path(__file__).with_name('check-qotom-pcie-pending-capture.py')))
PREFIX=b'LEANOS-LAB/1 BROADCOM-D3 '
DEC=rb'(0|[1-9][0-9]{0,9})'
FIELDS=(b'index=',b' status=',b' command-attempted=',b' command-before=',
    b' command-after=',b' polls=',b' device-status=',b' pmcsr-before=',
    b' d3-attempted=',b' pmcsr-after=')

def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):raise ValueError('Broadcom D3 capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    failure=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-broadcom-d3\n'
    if not positions:
        _,previous=D['extract'](raw,protocol)
        if previous is not None or lines[-1]==failure:raise ValueError('missing Broadcom D3 record')
        return raw,None
    if positions!=[len(lines)-2]:raise ValueError('Broadcom D3 record order')
    pattern=PREFIX+b'profile=qotom-broadcom-d3-v1 '+FIELDS[0]+DEC
    for field in FIELDS[1:]:pattern+=field+DEC
    pattern+=b'\n'
    match=re.fullmatch(pattern,lines[-2])
    if not match:raise ValueError('Broadcom D3 framing')
    index,status,attempted,before,after,polls,device,pm_before,d3_attempted,pm_after=map(int,match.groups())
    if (index!=14 or status>13 or attempted>1 or d3_attempted>1 or before>65535 or
            after>65535 or polls>100 or device>65535 or pm_before>65535 or pm_after>65535):
        raise ValueError('Broadcom D3 scalar bounds')
    projection=b''.join(lines[:-2])+pending
    _,previous=D['extract'](projection,protocol)
    if (previous is None or len(previous['functions'])!=6 or
            any(f['status'] for f in previous['functions'])):
        raise ValueError('Broadcom D3 without PCIe pending success')
    command_done=attempted==1 and before==6 and after==0
    pending_done=command_done and 2<=polls<=100 and device==25
    d3_done=pending_done and pm_before==0x4008 and d3_attempted==1 and pm_after==0x400b
    if status==0:
        valid=d3_done and lines[-1]==pending
    else:
        valid=lines[-1]==failure
        if status in (1,2,4,12,13):valid=valid and not any((attempted,before,after,polls,device,pm_before,d3_attempted,pm_after))
        elif status==3:valid=valid and ((not any((attempted,before,after,polls,device,pm_before,d3_attempted,pm_after))) or command_done)
        elif status==5:valid=valid and attempted==1 and before==6 and not any((after,polls,device,pm_before,d3_attempted,pm_after))
        elif status==6:valid=valid and attempted==1 and before==6 and not any((polls,device,pm_before,d3_attempted,pm_after))
        elif status==7:valid=valid and command_done and not pending_done and not any((pm_before,d3_attempted,pm_after))
        elif status==8:valid=valid and pending_done and not any((pm_before,d3_attempted,pm_after))
        elif status==9:valid=valid and pending_done and pm_before==0x4008 and d3_attempted==1 and pm_after==0
        elif status==10:valid=(valid and pending_done and pm_before==0x4008 and
            d3_attempted==1 and pm_after!=0x400b)
        elif status==11:valid=valid and d3_done
        else:valid=False
    if not valid:raise ValueError('Broadcom D3 result or terminal contradiction')
    return projection,{'schema':'leanos-qotom-broadcom-d3-observation-v1','index':index,
        'status':status,'command_write_attempted':bool(attempted),'before_command':before,
        'after_command':after,'pending_polls':polls,'device_status':device,
        'transactions_pending':bool(device&0x20),'before_pmcsr':pm_before,
        'd3_write_attempted':bool(d3_attempted),'after_pmcsr':pm_after,
        'command_disabled_observed':command_done,'d3hot_observed':d3_done,
        'pme_disabled_observed':d3_done,'terminal_reason':'qotom-platform-pending' if status==0 else 'qotom-broadcom-d3',
        'hardware_operations_replayed':False,'posted_write_drain_established':False,
        'firmware_exclusion_established':False,'dma_quarantine_established':False}
