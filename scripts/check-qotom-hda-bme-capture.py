"""Validate bounded BME-clear diagnostics without claiming DMA containment."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-state-capture.py')))
PREFIX = b'LEANOS-LAB/1 HDA-BME '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('BME capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-hda-bme\n'
    if not indices:
        _, previous = D['extract'](raw, protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing BME observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('BME order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection, protocol)
    if previous is None or previous['status']:
        raise ValueError('BME without successful HDA state observation')
    match = re.fullmatch(PREFIX + rb'profile=qotom-hda-bme-v1 index=5 status=' + DEC +
        rb' attempted=' + DEC + rb' before=' + DEC + rb' after=' + DEC + rb'\n',lines[indices[0]])
    if not match:
        raise ValueError('BME framing')
    status, attempted, before, after = map(int, match.groups())
    if status > 11 or status in (1,2) or attempted > 1 or max(before,after) > 65535:
        raise ValueError('BME scalar bounds or impossible native status')
    if status < 9:
        if tuple(previous[k] for k in ('corb','rirb','position')) != (0,0,0) or previous['streams'] != [0x40000]*8:
            raise ValueError('BME write authority without stopped HDA state')
        prefix = protocol['PCI-HEADER'].encode() + b' codec=1 index=5 width=19 words='
        headers = [line for line in lines if line.startswith(prefix)]
        if len(headers) != 1 or int(headers[0][len(prefix):].split(b',')[4]) & 0xffff != 0x6:
            raise ValueError('BME write authority without captured Command')
    if status in (3,4,5,9,10,11):
        valid = (attempted,before,after) == (0,0,0)
    else:
        valid = attempted == 1 and before == 0x6
        if status == 0:
            valid = valid and after == 0x2
        elif status == 6:
            valid = valid and after == 0
        elif status == 7:
            valid = valid and after != 0x2
    if not valid or lines[-1] != (failure if status else pending):
        raise ValueError('BME result/terminal contradiction')
    return projection, {'schema':'leanos-qotom-hda-bme-observation-v1',
        'status':status,'write_attempted':attempted,'before_command':before,'after_command':after,
        'terminal_reason':'qotom-hda-bme' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False}
