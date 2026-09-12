"""Validate SMI-disable observations after a complete handoff capture."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-handoff-capture.py')))
PREFIX = b'LEANOS-LAB/1 EHCI-SMI '
DEC = rb'(0|[1-9][0-9]{0,9})'
ENABLE = 0xe03f
STATUS = 0xe03f0000


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('SMI capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i,l in enumerate(lines) if l.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-ehci-smi\n'
    if not indices:
        _, handoff = D['extract'](raw, protocol)
        if (handoff is not None and handoff['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing SMI observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('SMI record order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, handoff = D['extract'](projection, protocol)
    if handoff is None or handoff['status']:
        raise ValueError('SMI write without successful handoff observation')
    match = re.fullmatch(PREFIX + rb'profile=qotom-smi-v1 index=10 status=' + DEC +
        rb' attempted=' + DEC + rb' before=' + DEC + rb' after=' + DEC + rb'\n',lines[indices[0]])
    if not match:
        raise ValueError('SMI record framing')
    status,attempted,before,after = map(int,match.groups())
    if status > 9 or status in (1,2) or attempted > 1 or max(before,after) > 0xffffffff:
        raise ValueError('SMI bounds or impossible native status')
    if status < 8 and handoff['final_control'] & ~(ENABLE|STATUS):
        raise ValueError('SMI writer armed with reserved control bits')
    if status in (3,4,8,9):
        valid = (attempted,before,after) == (0,0,0)
    else:
        valid = (attempted == 1 and not before & ~(ENABLE|STATUS) and
                 (before ^ handoff['final_control']) & ENABLE == 0)
        if status == 0:
            valid = valid and after & ~STATUS == 0
        elif status in (5,6):
            valid = valid and after == 0
        else:
            valid = valid and after != 0xffffffff and after & ~STATUS != 0
    if not valid or lines[-1] != (failure if status else pending):
        raise ValueError('SMI result/terminal contradiction')
    return projection, {'schema':'leanos-qotom-ehci-smi-observation-v1',
        'status':status,'write_attempted':attempted,'before_control':before,'after_control':after,
        'terminal_reason':'qotom-ehci-smi' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False}
