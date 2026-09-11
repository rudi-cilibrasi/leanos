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
    match = re.fullmatch(PREFIX + rb'profile=qotom-xhci-handoff-v1 index=3 status=' + DEC +
        rb' attempted=' + DEC + rb' polls=' + DEC + rb' support=' + DEC +
        rb' control=' + DEC + rb'\n',lines[indices[0]])
    if not match:
        raise ValueError('handoff framing')
    status,attempted,polls,support,control = map(int,match.groups())
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
    return projection, {'schema':'leanos-qotom-xhci-handoff-observation-v1',
        'status':status,'write_attempted':attempted,'polls':polls,
        'last_support':support,'final_control':control,
        'terminal_reason':'qotom-xhci-handoff' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False}
