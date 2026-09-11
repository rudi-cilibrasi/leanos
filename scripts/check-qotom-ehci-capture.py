"""Validate bounded EHCI capability records after the complete AF capture."""
import re
import runpy
from pathlib import Path
D = runpy.run_path(str(Path(__file__).with_name('check-qotom-af-capture.py')))
PREFIX = b'LEANOS-LAB/1 EHCI-CAPS '


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('EHCI capture bounds')
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-ehci-capabilities\n'
    if not indices:
        _, af = D['extract'](raw, protocol)
        if af is not None and af['terminal_reason'] == 'qotom-platform-pending':
            raise ValueError('missing EHCI capability record')
        if lines[-1] == failure:
            raise ValueError('EHCI fault without complete observation')
        return raw, None
    if indices != [len(lines)-2]:
        raise ValueError('EHCI record order or count')
    projection = b''.join(lines[:-2]) + pending
    _, af = D['extract'](projection, protocol)
    if af is None or af['terminal_reason'] != 'qotom-platform-pending':
        raise ValueError('EHCI capture before complete AF observation')
    decimal = rb'(0|[1-9][0-9]{0,9})'
    match = re.fullmatch(PREFIX + rb'profile=qotom-ehci-v1 index=10 status=' + decimal +
        rb' capbase=' + decimal + rb' structural=' + decimal + rb' capability=' + decimal + rb'\n', lines[-2])
    if not match:
        raise ValueError('EHCI record framing')
    status, capbase, structural, capability = map(int, match.groups())
    if status > 8 or status in (1,2) or any(v > 0xffffffff for v in (capbase,structural,capability)):
        raise ValueError('EHCI status or scalar bounds')
    if status == 0:
        length = capbase & 255
        if (capbase >> 16 != 0x100 or capbase & 0xff00 or length < 16 or length & 3 or
                not structural & 15 or 0xffffffff in (capbase,structural,capability)):
            raise ValueError('EHCI capability format')
    elif capbase or structural or capability:
        raise ValueError('EHCI failure publishes partial sample')
    if lines[-1] != (failure if status else pending):
        raise ValueError('EHCI terminal mismatch')
    return projection, {'schema':'leanos-qotom-ehci-capability-observation-v1',
        'status':status, 'capbase':capbase, 'structural':structural, 'capability':capability,
        'terminal_reason':'qotom-ehci-capabilities' if status else 'qotom-platform-pending',
        'failed_reads_replayed':False, 'ownership_established':False,
        'dma_quarantine_established':False}
