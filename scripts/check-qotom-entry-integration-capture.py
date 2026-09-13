#!/usr/bin/env python3
"""Validate the Qotom no-SMAP CPL3 entry/return checkpoint."""
import re

READY = b'LEANOS-LAB/1 QOTOM-ENTRY-READY '
PREFIX = b'LEANOS-LAB/1 QOTOM-ENTRY '
DEC = rb'(0|[1-9][0-9]{0,19})'
MANIFEST_SUFFIX = (b' ordinary=8 extended=6,7 contained=0,3 auxiliary=1 '
                   b'terminal=2 extra=0 rsp0=entry-stack ist1=df-stack '
                   b'ist2=nmi-stack result=PASS\n')
PORT_CONTROL_SUFFIX = (b' tr=40 limit=103 iomap=104 bitmap=absent iopl=0 '
                       b'stage=pre-cpl3 result=PASS\n')


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('Qotom entry capture bounds')
    lines = raw.splitlines(keepends=True)
    final = (protocol['FINAL'].encode() +
             b' status=FAIL reason=qotom-exception-integration-pending\n')
    prior = (protocol['FINAL'].encode() +
             b' status=FAIL reason=qotom-entry-integration-pending\n')
    ready = (READY + b'profile=qotom-copy-roots-v1 subject=1 address-space=1 '
             b'gates=2,6,8,13,14,128 root=closed cpl3-authority=0\n')
    manifest_prefix = protocol['ENTRY-MANIFEST'].encode() + b' '
    port_control_prefix = protocol['DIRECT-PORT-CONTROL'].encode() + b' '
    manifest = protocol['ENTRY-MANIFEST'].encode() + MANIFEST_SUFFIX
    port_control = protocol['DIRECT-PORT-CONTROL'].encode() + PORT_CONTROL_SUFFIX
    if (len(lines) < 5 or lines[-5] != manifest or
            lines[-4] != port_control or lines[-3] != ready or
            lines[-1] != final):
        raise ValueError('Qotom entry record order or terminal')
    if [i for i, line in enumerate(lines) if line.startswith(manifest_prefix)] != [len(lines)-5]:
        raise ValueError('Qotom entry manifest multiplicity')
    if [i for i, line in enumerate(lines) if line.startswith(port_control_prefix)] != [len(lines)-4]:
        raise ValueError('Qotom direct-port control multiplicity')
    if [i for i, line in enumerate(lines) if line.startswith(READY)] != [len(lines)-3]:
        raise ValueError('Qotom entry readiness multiplicity')
    if [i for i, line in enumerate(lines) if line.startswith(PREFIX)] != [len(lines)-2]:
        raise ValueError('Qotom entry result multiplicity')
    pattern = (PREFIX + rb'profile=qotom-copy-roots-v1 status=' + DEC +
        rb' entries=' + DEC + rb' returns=' + DEC +
        rb' incoming-root=' + DEC + rb' closed-root=' + DEC +
        rb' active-root=' + DEC + rb' frame=' + DEC + rb' user-if=' + DEC + rb' gprs=' + DEC +
        rb' close-readback=' + DEC + rb' return-reload=' + DEC +
        rb' error-mask=' + DEC + rb' entry-contract=' + DEC +
        rb' cpl3-authority=' + DEC + rb'\n')
    match = re.fullmatch(pattern, lines[-2])
    if not match:
        raise ValueError('Qotom entry framing')
    values = list(map(int, match.groups()))
    if any(value > 0xffffffffffffffff for value in values):
        raise ValueError('Qotom entry word width')
    (status, entries, returns, incoming_root, closed_root, active_root,
     frame, user_if, gprs, close_readback, return_reload, errors, contract, authority) = values
    roots_valid = (incoming_root != 0 and closed_root != 0 and
                   incoming_root != closed_root and active_root == closed_root and
                   incoming_root < 0x1000000 and closed_root < 0x1000000 and
                   incoming_root & 0xfff == 0 and closed_root & 0xfff == 0)
    if ((status, entries, returns, frame, user_if, gprs, close_readback,
         return_reload, errors, contract, authority) != (0, 2, 1, 1, 0, 15, 1, 1, 0, 1, 0)
            or not roots_valid):
        raise ValueError('Qotom entry result')
    metadata = {
        'schema': 'leanos-qotom-entry-integration-v1',
        'profile': 'qotom-copy-roots-v1', 'status': 0,
        'entries': 2, 'completed_returns': 1,
        'incoming_root': incoming_root, 'closed_root': closed_root,
        'active_root': active_root, 'frame_validated': True,
        'user_if': False,
        'saved_gprs': 15, 'close_readback': True, 'return_reload': True,
        'error_mask': 0, 'entry_contract': True,
        'cpl3_authority': False,
        'terminal_reason': 'qotom-exception-integration-pending',
    }
    return b''.join(lines[:-5]) + prior, metadata
