"""Decode bounded xHCI capabilities after the complete EHCI BME experiment."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-bme-capture.py')))
PREFIX = b'LEANOS-LAB/1 XHCI-CAPS '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('xHCI capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-xhci-capabilities\n'
    if not indices:
        _, previous = D['extract'](raw, protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing xHCI observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('xHCI order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection, protocol)
    if previous is None or previous['status']:
        raise ValueError('xHCI without successful EHCI BME prefix')
    match = re.fullmatch(PREFIX + rb'profile=qotom-xhci-v1 index=3 status=' + DEC +
        rb' words=' + DEC + (b','+DEC)*6 + rb'\n', lines[indices[0]])
    if not match:
        raise ValueError('xHCI framing')
    status,*words = map(int,match.groups())
    if status > 8 or status in (1,2) or max(words) > 0xffffffff:
        raise ValueError('xHCI scalar bounds or impossible native status')
    if status:
        valid = not any(words)
    else:
        valid = words[0] == 0x1000080 and 0xffffffff not in words
    if not valid or lines[-1] != (failure if status else pending):
        raise ValueError('xHCI result/terminal contradiction')
    prefix = protocol['PCI-HEADER'].encode() + b' codec=1 index=3 width=19 words='
    headers = [line for line in lines if line.startswith(prefix)]
    if len(headers) != 1:
        raise ValueError('xHCI missing captured header')
    header = [int(value) for value in headers[0][len(prefix):].strip().split(b',')]
    if status != 8 and (header[:4] != [0,20,0,0x0f358086] or
            not header[4]&2 or header[5] != 0x0c03300e or header[6]&0xff0000 or
            header[7:9] != [0xd0900004,0]):
        raise ValueError('xHCI without captured BAR-pair binding')
    return projection, {'schema':'leanos-qotom-xhci-capability-observation-v1',
        'status':status,'words':words,
        'terminal_reason':'qotom-xhci-capabilities' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'ownership_established':False,
        'dma_quarantine_established':False}
