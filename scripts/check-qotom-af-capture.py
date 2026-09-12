"""Validate AF record framing against complete preceding capability lists."""
import re
import runpy
from pathlib import Path

PREFIX = b'LEANOS-LAB/1 PCI-AF '
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-capabilities-capture.py')))


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('AF capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-pci-af\n'
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    if not indices:
        _, caps = D['extract'](raw, protocol)
        if (caps is not None and caps['terminal_reason'] == 'qotom-platform-pending') or lines[-1] == failure:
            raise ValueError('missing AF records')
        return raw, None
    first = indices[0]
    projection = b''.join(lines[:first]) + pending
    _, caps = D['extract'](projection, protocol)
    if caps is None or caps['terminal_reason'] != 'qotom-platform-pending':
        raise ValueError('AF without complete capability capture')
    cursor = first
    observations = []
    rejected = False
    for function in caps['functions']:
        i = function['index']
        if cursor >= len(lines):
            raise ValueError('truncated AF record')
        match = re.fullmatch(PREFIX + rb'profile=af-observation-v1 index=' + str(i).encode() +
            rb' status=(0|[1-9][0-9]?) offset=(0|[1-9][0-9]{0,2}) raw=(0|[1-9][0-9]{0,9})\n', lines[cursor])
        if not match:
            raise ValueError('AF record order or framing')
        status, offset, value = map(int, match.groups())
        if status > 7 or status == 2 or offset > 255 or value > 0xffffffff:
            raise ValueError('AF result bounds or impossible argument failure')
        entries = [e for e in function['headers'] if e['raw'] & 255 == 0x13]
        if status == 0:
            if len(entries) != 1:
                raise ValueError('AF success requires unique advertised structure')
            af = entries[0]
            if (af['raw'] >> 16 != 0x0306 or af['offset'] > 248 or
                    offset != af['offset'] or value == 0xffffffff or
                    any(e['offset'] == offset + 4 for e in function['headers'])):
                raise ValueError('AF successful shape or payload mismatch')
        else:
            if offset or value:
                raise ValueError('AF failure publishes payload')
            if status == 1 and entries:
                raise ValueError('AF absence contradicts preceding list')
            if status in (5,7):
                if len(entries) != 1:
                    raise ValueError('AF payload failure without unique AF')
                af = entries[0]
                if (af['raw'] >> 16 != 0x0306 or af['offset'] > 248 or
                        any(e['offset'] == af['offset'] + 4 for e in function['headers'])):
                    raise ValueError('AF payload failure before valid structure')
            if status == 6:
                malformed = len(entries) > 1 or any(
                    af['raw'] >> 16 != 0x0306 or af['offset'] > 248 or
                    any(e['offset'] == af['offset'] + 4 for e in function['headers'])
                    for af in entries)
                if not malformed:
                    raise ValueError('AF shape failure without malformed advertised structure')
            rejected = status != 1
        observations.append({'index': i, 'status': status, 'offset': offset, 'raw': value})
        cursor += 1
        if rejected:
            break
    if cursor != len(lines) - 1 or lines[cursor] != (failure if rejected else pending):
        raise ValueError('AF terminal or trailing records')
    return projection, {'schema': 'leanos-pci-af-observation-v1', 'functions': observations,
        'terminal_reason': 'qotom-pci-af' if rejected else 'qotom-platform-pending',
        'failed_reads_replayed': False, 'reset_performed': False, 'dma_quarantine_established': False}
