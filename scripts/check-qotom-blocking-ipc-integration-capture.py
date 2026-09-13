#!/usr/bin/env python3
"""Validate the exact physical Qotom blocking-IPC terminal transcript."""
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parent.parent
READY = (b'LEANOS-LAB/1 QOTOM-IPC-READY profile=qotom-blocking-ipc-v1 '
         b'subjects=2 interrupts=masked timer-gate=absent pic=masked '
         b'copy-in=readonly-root copy-out=writable-root cpl3-authority=1\n')
TEMPLATE = ROOT / 'scripts/expectations/blocking-ipc.transcript'


def semantic_expectation(protocol, template=TEMPLATE):
    rendered = []
    selected = False
    for source in Path(template).read_text().splitlines():
        if source.startswith('@10/IPC@ event=enter '):
            selected = True
        if not selected:
            continue
        match = re.fullmatch(r'@([0-9]+)/([A-Z][A-Z0-9-]*)@(.*)', source)
        if not match:
            raise ValueError('blocking-IPC expectation template tail is malformed')
        expected_prefix = f'LEANOS/{match.group(1)} {match.group(2)}'
        rendered.append(expected_prefix.encode() + match.group(3).encode() + b'\n')
    if not rendered or not rendered[-1].startswith(b'LEANOS/10 FINAL '):
        raise ValueError('blocking-IPC expectation template lacks its terminal')
    return READY + b''.join(rendered)


def extract(raw, protocol, template=TEMPLATE):
    expected = semantic_expectation(protocol, template)
    if len(raw) > 131072 or not raw.endswith(expected):
        raise ValueError('Qotom blocking-IPC bounds, order, or terminal')
    start = len(raw) - len(expected)
    if raw.count(READY) != 1 or raw.find(READY) != start:
        raise ValueError('Qotom blocking-IPC readiness multiplicity')
    if raw.count(b'LEANOS/10 FINAL ') != 1:
        raise ValueError('Qotom blocking-IPC terminal multiplicity')
    if (re.search(rb'![CUE][268P0]\n', raw) or
            re.search(rb'^LEANOS/[0-9]+ [^\n]* status=FAIL(?: |\n)',
                      raw, re.MULTILINE)):
        raise ValueError('Qotom blocking-IPC has an exception or failure terminal')

    entry = runpy.run_path(str(Path(__file__).with_name(
        'check-qotom-entry-integration-capture.py')))
    synthetic_terminal = (protocol['FINAL'].encode() +
        b' status=FAIL reason=qotom-exception-integration-pending\n')
    projected, entry_metadata = entry['extract'](
        raw[:start] + synthetic_terminal, protocol)
    metadata = {
        'schema': 'leanos-qotom-blocking-ipc-integration-v1',
        'profile': 'qotom-blocking-ipc-v1',
        'status': 'PASS',
        'subjects': 2,
        'semantic_syscalls': 8,
        'recoverable_page_faults': 1,
        'context_switches': 2,
        'copy_transfers': 2,
        'blocking_model_transitions': 4,
        'capability_model_transitions': 4,
        'blocks': 1,
        'wakes': 1,
        'deliveries': 1,
        'interrupts': 'masked',
        'timer_gate': 'absent',
        'pic': 'masked',
        'copy_in_root': 'readonly',
        'copy_out_root': 'writable',
        'cpl3_authority': True,
        'terminal_policy': 'halt-until-watchdog-reset',
        'expectation_template': str(TEMPLATE.relative_to(ROOT)),
    }
    return projected, metadata, entry_metadata
