#!/usr/bin/env python3
"""Separate bounded lab CF8 observations from the generated PCI protocol."""
import re

PREFIX = b'LEANOS-LAB/1 PCI-READ '
NAMES = ('reads', 'mismatches', 'requested', 'observed', 'value',
         'first_requested', 'first_observed', 'first_value')
PATTERN = PREFIX + b' '.join(name.encode() + rb'=(0|[1-9][0-9]*)' for name in NAMES) + b'\n'


def extract(raw, protocol):
    scan = protocol['PCI-SCAN'].encode()
    if scan not in raw:
        if PREFIX in raw:
            raise ValueError('PCI trace without scan')
        return raw, None
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    if len(indices) != 1:
        raise ValueError('missing or repeated PCI trace')
    index = indices[0]
    if index != 3 or index + 1 >= len(lines) or not lines[index - 1].startswith(protocol['CONTROL'].encode() + b' ') or not lines[index + 1].startswith(scan + b' '):
        raise ValueError('PCI trace position')
    if len(lines[index]) > 512:
        raise ValueError('PCI trace bound')
    match = re.fullmatch(PATTERN, lines[index])
    if not match:
        raise ValueError('PCI trace format')
    data = dict(zip(NAMES, map(int, match.groups())))
    if any(value > 0xffffffff for value in data.values()):
        raise ValueError('PCI trace width')
    if not 1 <= data['reads'] <= 65536 + 16 * 15 or data['mismatches'] > data['reads']:
        raise ValueError('PCI trace count')
    def valid_address(value):
        return value & 0xff000003 == 0x80000000
    if not valid_address(data['requested']):
        raise ValueError('PCI requested address')
    first = [data['first_' + name] for name in ('requested', 'observed', 'value')]
    if data['mismatches']:
        if not valid_address(first[0]) or first[0] == first[1]:
            raise ValueError('PCI first mismatch')
    elif any(first) or data['requested'] != data['observed']:
        raise ValueError('PCI zero mismatch inconsistency')
    del lines[index]
    return b''.join(lines), data
