"""Validate an xHCI extended list against its preceding MMIO pointer."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-capture.py')))
SUMMARY = b'LEANOS-LAB/1 XHCI-LEGACY '
ENTRY = b'LEANOS-LAB/1 XHCI-EXT '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('xHCI legacy capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i,l in enumerate(lines) if l.startswith(SUMMARY)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-xhci-legacy\n'
    if not indices:
        _, caps = D['extract'](raw, protocol)
        if caps is not None and caps['status'] == 0:
            raise ValueError('missing legacy list')
        if any(l.startswith(ENTRY) for l in lines) or lines[-1] == failure:
            raise ValueError('legacy entries without summary')
        return raw, None
    if len(indices) != 1:
        raise ValueError('duplicate legacy summary')
    start = indices[0]
    projection = b''.join(lines[:start]) + pending
    _, caps = D['extract'](projection, protocol)
    if caps is None or caps['status']:
        raise ValueError('legacy list without complete xHCI capability observation')
    match = re.fullmatch(SUMMARY + rb'profile=qotom-xhci-legacy-v1 index=3 status=' + DEC +
        rb' count=' + DEC + rb' offset=' + DEC + rb' control=' + DEC + rb'\n',lines[start])
    if not match:
        raise ValueError('legacy summary framing')
    status,count,offset,control = map(int,match.groups())
    if status > 12 or status == 1 or count > 48 or offset > 0xffff or control > 0xffffffff:
        raise ValueError('legacy scalar bounds')
    if status <= 10 and caps['words'] != [0x01000080,0x07000820,0x84000054,0x0200000a,0x200077c1,0x3000,0x2000]:
        raise ValueError('legacy collector without captured capability binding')
    headers=[]
    if status:
        if count or offset or control:
            raise ValueError('legacy rejection publishes partial observation')
    else:
        expected=(caps['words'][4]>>16)*4
        seen=set()
        legacy=0
        for i in range(count):
            if start+1+i >= len(lines):
                raise ValueError('truncated legacy list')
            match = re.fullmatch(ENTRY + rb'index=' + str(i).encode() + rb' offset=' + DEC +
                                rb' raw=' + DEC + rb'\n',lines[start+1+i])
            if not match:
                raise ValueError('extended header order or framing')
            address,value=map(int,match.groups())
            if (address!=expected or address<0x8000 or address>0xfffc or address&3 or address in seen or
                    value>0xffffffff or value&255 in (0,255)):
                raise ValueError('extended link bounds, cycle or ID')
            seen.add(address)
            if value&255==1:
                if legacy or address>0xfff8:
                    raise ValueError('duplicate or out-of-bounds legacy structure')
                legacy=address
            headers.append({'offset':address,'raw':value})
            next_offset=(value>>8)&255
            expected=address+next_offset*4 if next_offset else 0
        if expected or offset!=legacy or (legacy and legacy+4 in seen):
            raise ValueError('extended termination, selected legacy or overlap')
        if (not legacy and control) or control==0xffffffff:
            raise ValueError('legacy control without structure or absent read')
    if start+1+count != len(lines)-1 or lines[-1] != (failure if status else pending):
        raise ValueError('legacy terminal or trailing data')
    return projection, {'schema':'leanos-qotom-xhci-legacy-observation-v1',
        'status':status,'headers':headers,'legacy_offset':offset,'control_status':control,
        'terminal_reason':'qotom-xhci-legacy' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'ownership_established':False,'dma_quarantine_established':False}
