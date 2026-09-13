#!/usr/bin/env python3
"""Validate the Qotom closed/copy-root publication checkpoint."""
import re

PREFIX = b'LEANOS-LAB/1 COPY-ROOTS '
DEC = rb'(0|[1-9][0-9]{0,19})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('copy-root publication capture bounds')
    lines = raw.splitlines(keepends=True)
    positions = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    terminal = (protocol['FINAL'].encode() +
                b' status=FAIL reason=qotom-entry-integration-pending\n')
    prior = (protocol['FINAL'].encode() +
             b' status=FAIL reason=qotom-copy-roots-pending\n')
    if positions != [len(lines) - 2] or lines[-1] != terminal:
        raise ValueError('copy-root publication record order or terminal')
    pattern = (PREFIX + rb'profile=qotom-copy-roots-v1 status=' + DEC +
        rb' protected=' + DEC + rb' removed-aliases=' + DEC +
        rb' retained-present=' + DEC + rb' aliases=' + DEC +
        rb' closed-root=' + DEC + rb' copy-root=' + DEC +
        rb' closed-scan=' + DEC + rb' copy-scan=' + DEC +
        rb' transferred=' + DEC + rb' bytes-match=' + DEC +
        rb' active-root=' + DEC + rb' error-mask=' + DEC +
        rb' closed-root-published=' + DEC +
        rb' copy-root-published=' + DEC + rb' cpl3-authority=' + DEC + rb'\n')
    match = re.fullmatch(pattern, lines[-2])
    if not match:
        raise ValueError('copy-root publication framing')
    values = list(map(int, match.groups()))
    (status, protected, removed, retained, aliases, closed_root, copy_root,
     closed_scan, copy_scan, transferred, bytes_match, active_root, errors,
     closed_published, copy_published, cpl3) = values
    if any(value > 0xffffffffffffffff for value in values):
        raise ValueError('copy-root publication word width')
    roots_valid = (closed_root != 0 and copy_root != 0 and
                   closed_root != copy_root and
                   closed_root < 0x1000000 and copy_root < 0x1000000 and
                   closed_root & 0xfff == 0 and copy_root & 0xfff == 0 and
                   active_root == closed_root)
    if ((status, protected, removed, retained, aliases, closed_scan, copy_scan,
         transferred, bytes_match, errors, closed_published, copy_published,
         cpl3) != (0, 5, 3, 4088, 2, 1, 1, 16, 1, 0, 1, 1, 0)
            or not roots_valid):
        raise ValueError('copy-root publication result')
    metadata = {
        'schema': 'leanos-qotom-copy-root-publication-v1',
        'profile': 'qotom-copy-roots-v1', 'status': status,
        'protected_count': protected, 'removed_aliases': removed,
        'retained_present': retained, 'alias_count': aliases,
        'closed_root': closed_root, 'copy_root': copy_root,
        'closed_scan': True, 'copy_scan': True,
        'transferred': transferred, 'bytes_match': True,
        'active_root': active_root, 'error_mask': errors,
        'closed_root_published': True, 'copy_root_published': True,
        'cpl3_authority': False,
        'terminal_reason': 'qotom-entry-integration-pending'
    }
    return b''.join(lines[:-2]) + prior, metadata
