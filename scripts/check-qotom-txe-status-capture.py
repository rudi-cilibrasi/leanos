#!/usr/bin/env python3
"""Validate raw TXE firmware observations without inferring DMA state."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-bme-capture.py')))
PREFIX = b'LEANOS-LAB/1 TXE-STATUS '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('TXE status capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-txe-status\n'
    if not indices:
        _, previous = D['extract'](raw, protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing TXE status observation')
        return raw, None
    if len(indices) != 1 or indices[0] != len(lines)-2:
        raise ValueError('TXE status order or duplicates')
    projection = b''.join(lines[:indices[0]]) + pending
    _, previous = D['extract'](projection, protocol)
    if previous is None or previous['status']:
        raise ValueError('TXE status without successful HDA BME observation')
    match = re.fullmatch(PREFIX + rb'profile=qotom-txe-status-v1 index=4 status=' + DEC +
        rb' firmware0=' + DEC + rb' firmware1=' + DEC + rb'\n', lines[indices[0]])
    if not match:
        raise ValueError('TXE status framing')
    status, firmware0, firmware1 = map(int, match.groups())
    if status > 7 or status == 1 or max(firmware0,firmware1) >= 0xffffffff:
        raise ValueError('TXE status scalar bounds')
    if status not in (2,7):
        prefix = protocol['PCI-HEADER'].encode() + b' codec=1 index=4 width=19 words='
        headers = [line for line in lines if line.startswith(prefix)]
        if len(headers) != 1:
            raise ValueError('TXE status missing bound header')
        words = list(map(int, headers[0][len(prefix):].strip().split(b',')))
        if len(words) != 19 or words[:3] != [0,26,0] or words[3] != 0x0f188086 or \
                words[4] & 0xffff != 0x0106 or words[5] != 0x1080000e or words[6] & 0xff0000:
            raise ValueError('TXE status without captured native binding')
    if status and (firmware0 or firmware1):
        raise ValueError('failed TXE status must publish zero')
    if lines[-1] != (failure if status else pending):
        raise ValueError('TXE status terminal contradiction')
    return projection, {'schema':'leanos-qotom-txe-status-observation-v1',
        'status':status,'firmware0':firmware0,'firmware1':firmware1,
        'terminal_reason':'qotom-txe-status' if status else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'firmware_exclusion_established':False,
        'dma_quarantine_established':False,'atomic_snapshot':False}
