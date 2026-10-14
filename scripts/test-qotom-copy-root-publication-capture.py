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
# The DHCP-subject inventory (issue #556): A's text is two pages.
BASE_COUNTS = b'protected=5 removed-aliases=3 retained-present=4088'
DHCP_COUNTS = b'protected=6 removed-aliases=4 retained-present=4087'
dhcp_record = record.replace(BASE_COUNTS, DHCP_COUNTS)
terminal = protocol_record(3, 'FINAL') + b' status=FAIL reason=qotom-entry-integration-pending\n'
raw = prefix + record + terminal
dhcp_raw = prefix + dhcp_record + terminal
projected = (prefix + protocol_record(3, 'FINAL') +
             b' status=FAIL reason=qotom-copy-roots-pending\n')
cases = 0
for capture, inventory, protected in ((raw, None, 5), (raw, 'base', 5),
                                      (dhcp_raw, 'dhcp-subject', 6)):
    args = () if inventory is None else (inventory,)
    got, metadata = decoder['extract'](capture, protocol, *args)
    assert got == projected
    assert metadata['closed_root'] == metadata['active_root']
    assert metadata['protected_count'] == protected
    cases += 1

mutations = [
    (raw, 'base', b'protected=5', b'protected=4'),
    (raw, 'base', b'removed-aliases=3', b'removed-aliases=2'),
    (raw, 'base', b'bytes-match=1', b'bytes-match=0'),
    (raw, 'base', b'active-root=1712128', b'active-root=1667072'),
    (raw, 'base', b'copy-root-published=1', b'copy-root-published=0'),
    (raw, 'base', b'qotom-entry-integration-pending', b'qotom-copy-roots-pending'),
    # Each variant rejects the other's counts, whole or in part.
    (raw, 'base', BASE_COUNTS, DHCP_COUNTS),
    (raw, 'base', b'protected=5', b'protected=6'),
    (raw, 'base', b'retained-present=4088', b'retained-present=4087'),
    (dhcp_raw, 'dhcp-subject', DHCP_COUNTS, BASE_COUNTS),
    (dhcp_raw, 'dhcp-subject', b'protected=6', b'protected=5'),
    (dhcp_raw, 'dhcp-subject', b'removed-aliases=4', b'removed-aliases=3'),
    (dhcp_raw, 'dhcp-subject', b'retained-present=4087', b'retained-present=4088'),
    (dhcp_raw, 'dhcp-subject', b'aliases=2 ', b'aliases=3 '),
    (dhcp_raw, 'dhcp-subject', b'error-mask=0', b'error-mask=6'),
    # Only the two named variants exist.
    (raw, 'dhcp', b'', b''),
    (dhcp_raw, 'six-page', b'', b''),
]
for index, (capture, inventory, old, new) in enumerate(mutations):
    assert not old or old in capture, index
    mutation = capture.replace(old, new, 1) if old else capture
    try:
        decoder['extract'](mutation, protocol, inventory)
    except ValueError:
        cases += 1
        continue
    raise AssertionError(f'mutation {index} accepted')
try:
    decoder['extract'](prefix + record + record + terminal, protocol)
except ValueError:
    cases += 1
else:
    raise AssertionError('duplicate record accepted')
print(f'Qotom copy-root capture decoder: {cases} cases PASS')
