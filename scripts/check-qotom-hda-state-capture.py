"""Validate HDA ring/stream samples without claiming engine or fabric quiescence."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-capture.py')))
PREFIX = b'LEANOS-LAB/1 HDA-STATE '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('HDA state capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-hda-state\n'
    if not indices:
        _, previous = D['extract'](raw, protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing HDA state observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('HDA state order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection, protocol)
    if previous is None or previous['status']:
        raise ValueError('HDA state without successful globals')
    keys = ('corb','rirb','position') + tuple(f'stream{i}' for i in range(8))
    pattern = PREFIX + rb'profile=qotom-hda-state-v1 index=5 status=' + DEC
    pattern += b''.join(b' '+key.encode()+b'='+DEC for key in keys) + b'\n'
    match = re.fullmatch(pattern,lines[indices[0]])
    if not match:
        raise ValueError('HDA state framing')
    status, *values = map(int, match.groups())
    if status > 10 or status in (1,2) or max(values) > 0xffffffff:
        raise ValueError('HDA state scalar bounds or impossible native status')
    if status < 9 and tuple(previous[k] for k in
            ('control_before','capability','version_minor','version_major','interrupt','control_after')) != (1,0x4401,0,1,0,1):
        raise ValueError('HDA state without bound global profile')
    valid = not any(values) if status else (max(values[:2]) < 255 and max(values[2:]) < 0xffffffff)
    if not valid or lines[-1] != (failure if status else pending):
        raise ValueError('HDA state result/terminal contradiction')
    return projection, {'schema':'leanos-qotom-hda-state-observation-v1',
        'status':status,'corb':values[0],'rirb':values[1],'position':values[2],'streams':values[3:],
        'terminal_reason':'qotom-hda-state' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'atomic_snapshot':False,
        'dma_quarantine_established':False}
