"""Validate width-specific HDA global samples, without inferring DMA shutdown."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-bme-capture.py')))
PREFIX = b'LEANOS-LAB/1 HDA '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('HDA capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-hda\n'
    if not indices:
        _, previous = D['extract'](raw, protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing HDA observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('HDA order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection, protocol)
    if previous is None or previous['status']:
        raise ValueError('HDA without successful SATA BME observation')
    match = re.fullmatch(PREFIX + rb'profile=qotom-hda-v1 index=5 status=' + DEC +
        rb' before=' + DEC + rb' capability=' + DEC + rb' minor=' + DEC +
        rb' major=' + DEC + rb' interrupt=' + DEC + rb' after=' + DEC + rb'\n',lines[indices[0]])
    if not match:
        raise ValueError('HDA framing')
    status, before, capability, minor, major, interrupt, after = map(int, match.groups())
    values = (before,capability,minor,major,interrupt,after)
    if status > 9 or status in (1,2) or max(values) > 0xffffffff:
        raise ValueError('HDA scalar bounds or impossible native status')
    if status:
        valid = not any(values)
    else:
        valid = (before & 1 and after & 1 and before != 0xffffffff and after != 0xffffffff and
                 capability < 65535 and minor < 255 and major < 255 and interrupt != 0xffffffff)
    if not valid or lines[-1] != (failure if status else pending):
        raise ValueError('HDA result/terminal contradiction')
    return projection, {'schema':'leanos-qotom-hda-observation-v1',
        'status':status,'control_before':before,'capability':capability,
        'version_minor':minor,'version_major':major,'interrupt':interrupt,'control_after':after,
        'terminal_reason':'qotom-hda' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'atomic_snapshot':False,
        'dma_quarantine_established':False}
