#!/usr/bin/env python3
"""Differential replay of consistent copy-policy/page-table snapshots."""
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def baseline():
    rows = [[i, 10+i, 1, 1, 1, 1, 4+i, 1, 10+i, 7, 7, 7,
             ((4+i) << 12) | 7 | (1 << 63)] for i in range(2)]
    return [0, 7, 4095, 2, 0, 7, 1, 0, 2], rows


def main():
    cc = os.environ.get('LEANOS_CC', 'gcc')
    out = ROOT / 'build/copy-roots' / ('binding-' + Path(cc).name)
    out.mkdir(parents=True, exist_ok=True)
    report = out / 'results.json'
    report.unlink(missing_ok=True)
    runner = out / 'replay'
    subprocess.run([cc, '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                    str(ROOT / 'experiments/copy-roots/binding-replay.c'), '-o', str(runner)], check=True)
    names, lines = [], []

    def add(name, header, rows):
        # The Lean table model has one shared ancestor path. All corpus rows
        # use the same ancestor words; malformed storage is tested directly.
        assert rows[0][9:12] == rows[1][9:12]
        names.append(name)
        lines.append(' '.join(map(str, header + rows[0] + rows[1])))

    for direction in range(2):
        for count in range(17):
            for start in (0, 4088, 4095, 8192):
                h, r = baseline()
                h[2:5] = start, count, direction
                add(f'range-{direction}-{count}-{start}', h, r)
    for name, index, value in [('too-long', 3, 17), ('wrong-space', 1, 8),
                               ('wrong-owner', 0, 1), ('absent-owner', 6, 0)]:
        h, r = baseline()
        h[index] = value
        add(name, h, r)
    for start, count in [((1 << 64)-1, 2), ((1 << 64)-1, 1),
                         ((1 << 47)-1, 2), ((1 << 47)-1, 1), ((1 << 64)-1, 0)]:
        h, r = baseline()
        h[2:4] = start, count
        add(f'arithmetic-{start}-{count}', h, r)
    for name, field, value in [('read-denied', 2, 0), ('wrong-kind', 4, 0),
                                ('retired', 5, 0), ('unallocated', 7, 0),
                                ('wrong-allocation-owner', 8, 12),
                                ('changed-frame', 12, (6 << 12) | 7),
                                ('absent-leaf', 12, 0), ('supervisor-leaf', 12, (5 << 12) | 3),
                                ('reserved-leaf', 12, (5 << 12) | 0x87)]:
        h, r = baseline()
        r[1][field] = value
        add(name, h, r)
    h, r = baseline()
    r[1][1], r[1][6], r[1][8] = 10, 4, 10
    add('cross-virtual-page-frame-alias', h, r)
    for index in range(3):
        for permission in (1, 2, 4):
            h, r = baseline()
            h[4] = 1
            for row in r:
                row[9+index] &= ~permission
            add(f'ancestor-{index}-missing-{permission}', h, r)
    h, r = baseline()
    h[4] = 1
    r[0][12] = 0
    r[1][3] = 0
    add('later-policy-before-earlier-hardware', h, r)
    rng = random.Random(329)
    for index in range(40):
        h, r = baseline()
        h[2], h[3], h[4] = rng.randrange(4080, 4112), rng.randrange(17), rng.randrange(2)
        frames = rng.sample(range(1 << 20), 2)
        for page, row in enumerate(r):
            row[6] = frames[page]
            row[12] = (frames[page] << 12) | 7 | (rng.randrange(2) << 63) | (rng.randrange(4) << 5)
        add(f'physical-frame-and-ad-{index}', h, r)
    payload = ('\n'.join(lines)+'\n').encode()
    expected = subprocess.check_output([str(ROOT / '.lake/build/bin/leanos-copy-binding-replay')], input=payload)
    actual = subprocess.check_output([str(runner)], input=payload)
    if len(expected.splitlines()) != len(lines) or len(actual.splitlines()) != len(lines):
        raise RuntimeError('binding replay row count mismatch')
    for name, a, b in zip(names, expected.splitlines(), actual.splitlines()):
        if a != b:
            raise RuntimeError(f'{name}: Lean {a!r}, C {b!r}')
    codes = sorted({int(line.split()[0]) for line in actual.splitlines()})
    if codes != list(range(13)):
        raise RuntimeError(f'incomplete binding rejection coverage: {codes}')
    report.write_text(json.dumps({'cases': names, 'result_codes': codes,
        'input_sha256': hashlib.sha256(payload).hexdigest(),
        'output_sha256': hashlib.sha256(actual).hexdigest(),
        'scope': 'consistent immutable two-page snapshots; no collector, lifetime or cached translation proof'}, indent=2)+'\n')
    print(f'copy binding Lean/C: {len(names)} cases, all 13 result codes PASS')


if __name__ == '__main__':
    main()
