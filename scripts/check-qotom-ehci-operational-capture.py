"""Decode sequential EHCI operational observations after successful SMI disable."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-smi-capture.py')))
PREFIX = b'LEANOS-LAB/1 EHCI-OPERATIONAL '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('operational capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-ehci-operational\n'
    if not indices:
        _, smi = D['extract'](raw, protocol)
        if (smi is not None and smi['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing operational observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('operational order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, smi = D['extract'](projection, protocol)
    if smi is None or smi['status']:
        raise ValueError('operational samples without successful SMI disable')
    match = re.fullmatch(PREFIX + rb'profile=qotom-operational-v1 index=10 status=' + DEC +
        rb' command=' + DEC + rb' status_register=' + DEC + rb' interrupt_enable=' + DEC +
        rb' configured=' + DEC + rb'\n', lines[indices[0]])
    if not match:
        raise ValueError('operational framing')
    status, command, sampled_status, interrupts, configured = map(int, match.groups())
    values = (command, sampled_status, interrupts, configured)
    if status > 9 or status in (1, 2) or max(values) > 0xffffffff:
        raise ValueError('operational scalar bounds or impossible native status')
    if (status and any(values)) or (not status and 0xffffffff in values):
        raise ValueError('operational failed publication or absent device')
    if lines[-1] != (failure if status else pending):
        raise ValueError('operational terminal contradiction')
    return projection, {'schema': 'leanos-qotom-ehci-operational-observation-v1',
        'status': status, 'command': command, 'status_register': sampled_status,
        'interrupt_enable': interrupts, 'configured': configured,
        'terminal_reason': 'qotom-ehci-operational' if status else 'qotom-platform-pending',
        'hardware_operations_replayed': False, 'atomic_snapshot': False,
        'dma_quarantine_established': False, 'firmware_exclusion_established': False}
