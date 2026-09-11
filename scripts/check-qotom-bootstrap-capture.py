#!/usr/bin/env python3
"""Decode a lab BSP sample without asserting AP dormancy or admission."""
import re

PREFIX = b'LEANOS-LAB/1 BOOTSTRAP '
NUMBER = rb'(0|[1-9][0-9]*)'
PATTERN = PREFIX + b'cpuid-edx=' + NUMBER + b' available=([01]) apic-base=' + NUMBER + b'\n'


def extract(raw, protocol, *, ecam_failure=False):
    lines = raw.splitlines(keepends=True)
    rejected_ecam = ecam_failure and any(raw.endswith(protocol['FINAL'].encode() +
        b' status=FAIL reason=' + reason + b'\n') for reason in
        (b'qotom-ecam-arm', b'qotom-ecam-transaction'))
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    scan = protocol['PCI-SCAN'].encode() + b' '
    if not rejected_ecam and not any(line.startswith(scan) for line in lines):
        if indices:
            raise ValueError('bootstrap sample without completed CPU/MSR gate')
        return raw, None
    if indices != [3] or not lines[2].startswith(protocol['CONTROL'].encode() + b' '):
        raise ValueError('missing, repeated, or misplaced bootstrap sample')
    if len(lines[3]) > 160:
        raise ValueError('bootstrap record bound')
    match = re.fullmatch(PATTERN, lines[3])
    if match is None:
        raise ValueError('bootstrap record format')
    edx, available, value = map(int, match.groups())
    if edx > 0xffffffff or value > 0xffffffffffffffff:
        raise ValueError('bootstrap value width')
    if available != int(edx & 0x220 == 0x220) or (not available and value):
        raise ValueError('bootstrap read availability')
    cpu = re.fullmatch(re.escape(protocol['CPU'].encode()) +
        rb' profile=j1900-cpu-v1 codec=1 width=22 words=([0-9]+(?:,[0-9]+){21}) selection=65536\n', lines[1])
    if cpu is None or int(cpu[1].split(b',')[9]) != edx or not lines[2].endswith(b' readback=1\n'):
        raise ValueError('bootstrap CPU/MSR binding')
    del lines[3]
    return b''.join(lines), {
        'schema': 'leanos-bootstrap-lab-v1', 'cpuid_edx': edx,
        'available': bool(available), 'ia32_apic_base': value,
        'bsp': bool(value & (1 << 8)) if available else None,
        'apic_enabled': bool(value & (1 << 11)) if available else None,
        'x2apic_enabled': bool(value & (1 << 10)) if available else None,
        'platform_admitted': False, 'ap_dormancy_established': False,
    }
