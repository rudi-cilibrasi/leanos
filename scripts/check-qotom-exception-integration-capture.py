#!/usr/bin/env python3
"""Validate the terminal Qotom CPL3 invalid-opcode checkpoint."""
from pathlib import Path
import re
import runpy

MARKER = b'!C6\n'
TERMINAL_MARKER = re.compile(rb'![CUE][268P0]\n')


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(MARKER):
        raise ValueError('Qotom exception capture bounds or terminal')
    markers = TERMINAL_MARKER.findall(raw)
    if markers != [MARKER]:
        raise ValueError('Qotom exception marker multiplicity or class')
    if protocol['FINAL'].encode() in raw:
        raise ValueError('Qotom exception capture has a structured terminal')

    entry = runpy.run_path(str(Path(__file__).with_name(
        'check-qotom-entry-integration-capture.py')))
    synthetic = (raw[:-len(MARKER)] + protocol['FINAL'].encode() +
                 b' status=FAIL reason=qotom-exception-integration-pending\n')
    projected, entry_metadata = entry['extract'](synthetic, protocol)
    metadata = {
        'schema': 'leanos-qotom-exception-integration-v1',
        'profile': 'qotom-copy-roots-v1',
        'status': 0,
        'ordinary_entries': 2,
        'completed_returns': 2,
        'terminal_vector': 6,
        'terminal_class': 'closed-root',
        'closed_root': entry_metadata['closed_root'],
        'active_root_before_terminal': entry_metadata['active_root'],
        'saved_gprs': 15,
        'user_return_value_validated': True,
        'close_readback': True,
        'cpl3_authority': False,
        'next_checkpoint': 'qotom-blocking-ipc-integration',
    }
    return projected, metadata, entry_metadata
