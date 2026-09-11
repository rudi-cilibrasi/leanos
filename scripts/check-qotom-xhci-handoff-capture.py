"""Validate bounded handoff diagnostics; never infer firmware/DMA exclusion."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-legacy-capture.py')))
PREFIX = b'LEANOS-LAB/1 XHCI-HANDOFF '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('handoff capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i,l in enumerate(lines) if l.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-xhci-handoff\n'
    if not indices:
        _, legacy = D['extract'](raw, protocol)
        if (legacy is not None and legacy['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing handoff observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('handoff record order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    cap_projection, legacy = D['extract'](projection, protocol)
    if legacy is None or legacy['status']:
        raise ValueError('handoff without successful legacy capture')
    _, caps = D['D']['extract'](cap_projection, protocol)
    match = re.fullmatch(PREFIX + rb'profile=qotom-xhci-handoff-v([12]) index=3 status=' + DEC +
        rb' attempted=' + DEC + rb' polls=' + DEC + rb' support=' + DEC +
        rb' control=' + DEC + rb'(?: verify=' + DEC + rb' verify-index=' + DEC +
        rb' expected=' + DEC + rb' observed=' + DEC + rb')?\n',lines[indices[0]])
    if not match:
        raise ValueError('handoff framing')
    version,status,attempted,polls,support,control = map(int,match.groups()[:6])
    details=match.groups()[6:]
    if (version==1 and any(v is not None for v in details)) or (version==2 and any(v is None for v in details)):
        raise ValueError('handoff version/detail mismatch')
    if (status > 14 or status in (1,4) or attempted > 1 or polls > 100 or
            support > 0xffffffff or control > 0xffffffff):
        raise ValueError('handoff scalar bounds or impossible native status')
    if status < 11:
        if (legacy['headers'] != [{'offset':a,'raw':v} for a,v in [
                (0x8000,0x02000802),(0x8020,0x03000802),(0x8040,0x00010cc1),
                (0x8070,0x0000fcc0),(0x8460,0x00010801),(0x8480,0x0005000a)]] or
                legacy['legacy_offset'] != 0x8460 or legacy['control_status'] != 0x2001 or
                caps['words'] != [0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000]):
            raise ValueError('handoff without exact writer binding')
    if status in (2,3,11,12,13,14):
        valid = (attempted,polls,support,control) == (0,0,0,0)
    elif status == 0:
        valid = attempted == 1 and polls >= 1 and support == 0x1000801 and control != 0xffffffff
    elif status == 5:
        valid = (attempted,polls,support,control) == (1,0,0x10801,0)
    elif status == 6:
        valid = attempted == 1 and polls < 100 and control == 0 and support == (0x10801 if polls == 0 else 0x1010801)
    elif status == 7:
        valid = attempted == 1 and polls >= 1 and control == 0 and support == (0x10801 if polls == 1 else 0x1010801)
    elif status == 8:
        valid = attempted == 1 and polls >= 1 and control == 0 and (support & ~0x1010000 != 0x801 or not support & 0x1000000)
    elif status == 9:
        valid = (attempted,polls,support,control) == (1,100,0x1010801,0)
    else: # final refresh/list/semaphore rejection
        valid = attempted == 1 and polls >= 1 and control == 0 and support in (0x801,0x10801,0x1000801,0x1010801)
    if not valid or lines[-1] != (failure if status else pending):
        raise ValueError('handoff result/terminal contradiction')
    result = {'schema':f'leanos-qotom-xhci-handoff-observation-v{version}',
        'status':status,'write_attempted':attempted,'polls':polls,
        'last_support':support,'final_control':control,
        'terminal_reason':'qotom-xhci-handoff' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False}

    if version==2:
        kind,index,before,after=map(int,details)
        if max(kind,index,before,after)>0xffffffff:
            raise ValueError('verification scalar bounds')
        if status!=10:
            valid=(kind,index,before,after)==(0,0,0,0)
        elif kind==1:
            valid=index==0 and before==0 and 2<=after<=10
        elif kind==2:
            valid=index==0 and before==len(legacy['headers']) and 1<=after<=48 and after!=before
        elif kind==3:
            valid=index==0 and before==legacy['legacy_offset'] and after!=before and (
                after==0 or 0x8000<=after<=0xfff8 and not after&3)
        elif kind in (4,5):
            valid=index<len(legacy['headers'])
            if valid:
                entry=legacy['headers'][index]
                if kind==4:
                    valid=before==entry['offset'] and 0x8000<=after<=0xfffc and not after&3 and before!=after
                else:
                    mask=0x01010000 if entry['offset']==legacy['legacy_offset'] else 0
                    valid=before==entry['raw'] and bool((before^after)&~mask) and after&255 not in (0,255)
                    if entry['offset']==legacy['legacy_offset']:
                        valid=valid and after&255==1 and (after>>8)&255!=1
                    else:
                        valid=valid and after&255!=1
        elif kind==6:
            valid=(index<len(legacy['headers']) and legacy['headers'][index]['offset']==legacy['legacy_offset'] and
                before==0x01000801 and after==support and after in (0x801,0x10801,0x1010801))
        else:
            valid=False
        if status==10 and kind!=6 and support!=0x01000801:
            valid=False
        if not valid:
            raise ValueError('verification detail contradicts handoff or prior list')
        result['verification']={'kind':kind,'index':index,'expected':before,'observed':after}
    return projection,result
