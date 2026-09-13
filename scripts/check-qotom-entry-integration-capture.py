#!/usr/bin/env python3
"""Validate the Qotom no-SMAP CPL3 entry/return checkpoint."""
import re

READY = b'LEANOS-LAB/1 QOTOM-ENTRY-READY '
PREFIX = b'LEANOS-LAB/1 QOTOM-ENTRY '
DEC = rb'(0|[1-9][0-9]{0,19})'


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
    if len(lines) < 3 or lines[-3] != ready or lines[-1] != final:
        raise ValueError('Qotom entry record order or terminal')
    if [i for i, line in enumerate(lines) if line.startswith(READY)] != [len(lines)-3]:
        raise ValueError('Qotom entry readiness multiplicity')
    if [i for i, line in enumerate(lines) if line.startswith(PREFIX)] != [len(lines)-2]:
        raise ValueError('Qotom entry result multiplicity')
    pattern = (PREFIX + rb'profile=qotom-copy-roots-v1 status=' + DEC +
        rb' entries=' + DEC + rb' returns=' + DEC +
        rb' incoming-root=' + DEC + rb' closed-root=' + DEC +
        rb' active-root=' + DEC + rb' frame=' + DEC + rb' gprs=' + DEC +
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
     frame, gprs, close_readback, return_reload, errors, contract, authority) = values
    roots_valid = (incoming_root != 0 and closed_root != 0 and
                   incoming_root != closed_root and active_root == closed_root and
                   incoming_root < 0x1000000 and closed_root < 0x1000000 and
                   incoming_root & 0xfff == 0 and closed_root & 0xfff == 0)
    if ((status, entries, returns, frame, gprs, close_readback,
         return_reload, errors, contract, authority) != (0, 2, 1, 1, 15, 1, 1, 0, 1, 0)
            or not roots_valid):
        raise ValueError('Qotom entry result')
    metadata = {
        'schema': 'leanos-qotom-entry-integration-v1',
        'profile': 'qotom-copy-roots-v1', 'status': 0,
        'entries': 2, 'completed_returns': 1,
        'incoming_root': incoming_root, 'closed_root': closed_root,
        'active_root': active_root, 'frame_validated': True,
        'saved_gprs': 15, 'close_readback': True, 'return_reload': True,
        'error_mask': 0, 'entry_contract': True,
        'cpl3_authority': False,
        'terminal_reason': 'qotom-exception-integration-pending',
    }
    return b''.join(lines[:-3]) + prior, metadata
