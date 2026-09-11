#!/usr/bin/env python3
"""Retain a same-stream PAT/control sample without admitting any MMIO mapping."""
import re

PREFIX = b'LEANOS-LAB/1 ECAM-MEMORY '
NUMBER = rb'(0|[1-9][0-9]*)'
PATTERN = (PREFIX + b'cpuid-edx=' + NUMBER + b' available=([01]) pat=' + NUMBER +
           b' cr0=' + NUMBER + b' cr3=' + NUMBER + b' cr4=' + NUMBER + b'\n')
BOOTSTRAP = b'LEANOS-LAB/1 BOOTSTRAP cpuid-edx=' + NUMBER + rb' available=[01] apic-base=' + NUMBER + b'\n'


def extract(raw, protocol, *, ecam_failure=False, bsp_failure=False):
    lines = raw.splitlines(keepends=True)
    rejected_ecam = ecam_failure and any(raw.endswith(protocol['FINAL'].encode() +
        b' status=FAIL reason=' + reason + b'\n') for reason in
        (b'qotom-ecam-arm', b'qotom-ecam-transaction'))
    rejected_ecam = rejected_ecam or (bsp_failure and raw.endswith(
        protocol['FINAL'].encode() + b' status=FAIL reason=qotom-native-bsp\n'))
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    if not rejected_ecam and not any(line.startswith(protocol['PCI-SCAN'].encode() + b' ') for line in lines):
        if indices:
            raise ValueError('ECAM memory sample without completed CPU gate')
        return raw, None
    if indices != [4] or not lines[2].startswith(protocol['CONTROL'].encode() + b' '):
        raise ValueError('missing, repeated, or misplaced ECAM memory sample')
    if len(lines[4]) > 256:
        raise ValueError('ECAM memory record bound')
    match = re.fullmatch(PATTERN, lines[4])
    bootstrap = re.fullmatch(BOOTSTRAP, lines[3])
    if match is None or bootstrap is None:
        raise ValueError('ECAM memory record format/order')
    edx, available, pat, cr0, cr3, cr4 = map(int, match.groups())
    if edx > 0xffffffff or any(x > 0xffffffffffffffff for x in (pat, cr0, cr3, cr4)):
        raise ValueError('ECAM memory value width')
    if available != int(edx & 0x10020 == 0x10020) or (not available and pat):
        raise ValueError('PAT read availability')
    cpu = re.fullmatch(re.escape(protocol['CPU'].encode()) +
        rb' profile=j1900-cpu-v1 codec=1 width=22 words=([0-9]+(?:,[0-9]+){21}) selection=65536\n', lines[1])
    if (cpu is None or int(cpu[1].split(b',')[9]) != edx or int(bootstrap[1]) != edx or
            not lines[2].endswith(b' readback=1\n')):
        raise ValueError('ECAM memory CPU/control binding')
    del lines[4]
    return b''.join(lines), {
        'schema': 'leanos-ecam-memory-lab-v1', 'cpuid_edx': edx,
        'available': bool(available), 'ia32_pat': pat, 'cr0': cr0, 'cr3': cr3, 'cr4': cr4,
        'pat_entries': [(pat >> (8*i)) & 255 for i in range(8)] if available else None,
        'memory_type_admitted': False, 'platform_admitted': False,
    }
