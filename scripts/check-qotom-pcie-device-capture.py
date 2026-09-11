"""Validate PCIe Device observations after the complete xHCI BME prefix."""
import re
import runpy
from pathlib import Path

D = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-bme-capture.py')))
C = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-capabilities-capture.py')))
PREFIX = b'LEANOS-LAB/1 PCIE-DEVICE '
DEC = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('PCIe Device capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-pcie-device\n'
    if not indices:
        _, previous = D['extract'](raw, protocol)
        if (previous is not None and previous['status'] == 0) or lines[-1] == failure:
            raise ValueError('missing PCIe Device records')
        return raw, None
    first = indices[0]
    projection = b''.join(lines[:first]) + pending
    _, previous = D['extract'](projection, protocol)
    if previous is None or previous['status']:
        raise ValueError('PCIe Device without successful xHCI BME')
    # The recursive prefix check validates AF and every subsequent USB stage.
    # Project only the already-validated capability prefix to obtain its lists.
    af = projection.index(b'LEANOS-LAB/1 PCI-AF ')
    _, caps = C['extract'](projection[:af] + pending, protocol)
    if caps is None or caps['terminal_reason'] != 'qotom-platform-pending':
        raise ValueError('PCIe Device without complete capability lists')
    cursor = first
    observations = []
    rejected = False
    for function in caps['functions']:
        i = function['index']
        if cursor >= len(lines):
            raise ValueError('truncated PCIe Device record')
        match = re.fullmatch(PREFIX + rb'profile=qotom-pcie-device-v1 index=' + str(i).encode() +
            rb' status=' + DEC + rb' offset=' + DEC + rb' capability=' + DEC + rb' control-status=' + DEC + rb'\n', lines[cursor])
        if not match:
            raise ValueError('PCIe Device framing or order')
        status, offset, capability, control = map(int, match.groups())
        if status > 8 or status == 2 or offset > 255 or max(capability,control) > 0xffffffff:
            raise ValueError('PCIe Device bounds or impossible argument failure')
        header_prefix = protocol['PCI-HEADER'].encode() + b' codec=1 index=' + str(i).encode() + b' width=19 words='
        headers = [line for line in lines[:first] if line.startswith(header_prefix)]
        if len(headers) != 1:
            raise ValueError('missing PCI header for PCIe Device')
        words = list(map(int,headers[0][len(header_prefix):].strip().split(b',')))
        if len(words) != 19:
            raise ValueError('PCI header width')
        layout = (words[6] >> 16) & 0x7f
        entries = [e for e in function['headers'] if e['raw'] & 255 == 0x10]
        valid = False
        if len(entries) == 1:
            cap = entries[0]
            flags = cap['raw'] >> 16
            version, kind = flags & 15, (flags >> 4) & 15
            valid = (version in (1,2) and not flags & 0xc000 and cap['offset'] <= 244 and
                ((layout == 0 and kind in (0,1) and not flags & 0x100) or (layout == 1 and kind == 4)) and
                not any(e['offset'] in (cap['offset']+4,cap['offset']+8) for e in function['headers']))
        if status == 0:
            if not valid or offset != entries[0]['offset'] or 0xffffffff in (capability,control):
                raise ValueError('PCIe Device success shape or payload')
        else:
            if offset or capability or control:
                raise ValueError('PCIe Device failure publishes payload')
            if status == 1 and entries:
                raise ValueError('PCIe Device absence contradicts list')
            if status == 5 and (not entries or valid):
                raise ValueError('PCIe Device shape failure without malformed structure')
            if status in (6,7,8) and not valid:
                raise ValueError('PCIe Device payload/final failure before valid structure')
        rejected = status not in (0,1)
        observations.append({'index':i,'status':status,'offset':offset,
            'device_capabilities':capability,'device_control_status':control})
        cursor += 1
        if rejected:
            break
    if cursor != len(lines)-1 or lines[cursor] != (failure if rejected else pending):
        raise ValueError('PCIe Device terminal or trailing records')
    return projection, {'schema':'leanos-qotom-pcie-device-observation-v1','functions':observations,
        'terminal_reason':'qotom-pcie-device' if rejected else 'qotom-platform-pending',
        'hardware_operations_replayed':False,'reset_performed':False,'dma_quarantine_established':False}
