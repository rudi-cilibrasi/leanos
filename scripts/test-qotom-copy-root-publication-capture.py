#!/usr/bin/env python3
"""Mutation checks for the Qotom copy-root capture decoder."""
import runpy
from pathlib import Path
from qotom_lab_protocol import record as protocol_record

decoder = runpy.run_path(str(Path(__file__).with_name(
    'check-qotom-copy-root-publication-capture.py')))
protocol = {'FINAL': protocol_record(3, 'FINAL').decode()}
prefix = protocol_record(10, 'BOOT') + b' sample\n'
record = (b'LEANOS-LAB/1 COPY-ROOTS profile=qotom-copy-roots-v1 status=0 '
    b'protected=5 removed-aliases=3 retained-present=4088 aliases=2 '
    b'closed-root=1712128 copy-root=1667072 closed-scan=1 copy-scan=1 '
    b'transferred=16 bytes-match=1 active-root=1712128 error-mask=0 '
    b'closed-root-published=1 copy-root-published=1 cpl3-authority=0\n')
terminal = protocol_record(3, 'FINAL') + b' status=FAIL reason=qotom-entry-integration-pending\n'
raw = prefix + record + terminal
projected, metadata = decoder['extract'](raw, protocol)
assert projected == (prefix + protocol_record(3, 'FINAL') +
                     b' status=FAIL reason=qotom-copy-roots-pending\n')
assert metadata['closed_root'] == metadata['active_root']

mutations = [
    raw.replace(b'protected=5', b'protected=4'),
    raw.replace(b'removed-aliases=3', b'removed-aliases=2'),
    raw.replace(b'bytes-match=1', b'bytes-match=0'),
    raw.replace(b'active-root=1712128', b'active-root=1667072'),
    raw.replace(b'copy-root-published=1', b'copy-root-published=0'),
    raw.replace(b'qotom-entry-integration-pending', b'qotom-copy-roots-pending'),
    prefix + record + record + terminal,
]
for index, mutation in enumerate(mutations):
    try:
        decoder['extract'](mutation, protocol)
    except ValueError:
        continue
    raise AssertionError(f'mutation {index} accepted')
print(f'Qotom copy-root capture decoder: {1 + len(mutations)} cases PASS')
