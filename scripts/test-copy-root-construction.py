#!/usr/bin/env python3
"""Compare complete canonical leaf tables with the compiled Lean projection."""
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/copy-roots' / ('construction-' + Path(os.environ.get('LEANOS_CC', 'gcc')).name)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    report = OUT / 'results.json'
    report.unlink(missing_ok=True)
    cc = os.environ.get('LEANOS_CC', 'gcc')
    runner = OUT / 'replay'
    subprocess.run([cc, '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                    str(ROOT / 'experiments/copy-roots/construct-replay.c'), '-o', str(runner)], check=True)
    rows = []
    names = []

    def add(name, source, frames, required):
        # This comparison uses canonical present leaves or the zero absent word.
        # C-only tests cover A/D preservation, pointer overlap and storage bounds.
        assert all(word == 0 or word & 1 for word in source)
        assert all(word & 1 for _, word in required)
        words = [len(frames), len(required), *frames]
        for page, word in required:
            words.extend([page, word])
        rows.append(' '.join(map(str, words + source)))
        names.append(name)

    source = [(i << 12) | 3 for i in range(4096)]
    source[200] = (4 << 12) | (1 << 63) | 3
    source[4095] = (5 << 12) | 7
    source[99] = 0
    add('supervisor-and-user-aliases', source, [4, 5], [(8, source[8])])
    add('required-overlap', source, [4, 5, 8], [(8, source[8])])
    add('missing-required', source, [4], [(99, (99 << 12) | 3)])
    add('changed-required-frame', source, [4], [(8, (9 << 12) | 3)])
    add('changed-required-write', source, [4], [(8, source[8] ^ 2)])
    add('changed-required-user', source, [4], [(8, source[8] ^ 4)])
    add('changed-required-nx', source, [4], [(8, source[8] ^ (1 << 63))])
    add('duplicate-frames-and-requirements', source, [4, 4], [(8, source[8]), (8, source[8])])
    add('empty-inventories', source, [], [])
    rng = random.Random(329)
    for case in range(24):
        table = [0 if rng.randrange(8) == 0 else
                 (rng.randrange(4096) << 12) | 1 | (rng.randrange(4) << 1) |
                 (rng.randrange(2) << 63) for _ in range(4096)]
        required = [(p, table[p]) for p in (0, 127, 4095) if table[p]]
        used = {word >> 12 & ((1 << 40) - 1) for _, word in required}
        frames = [frame for frame in range(case, case + 16) if frame not in used]
        add(f'complete-table-{case}', table, frames, required)
    payload = ('\n'.join(rows) + '\n').encode()
    model = subprocess.check_output([str(ROOT / '.lake/build/bin/leanos-copy-root-construction')], input=payload)
    actual = subprocess.check_output([str(runner)], input=payload)
    expected_rows, actual_rows = model.splitlines(), actual.splitlines()
    if len(expected_rows) != len(rows) or len(actual_rows) != len(rows):
        raise RuntimeError('construction replay row count mismatch')
    for name, expected, observed in zip(names, expected_rows, actual_rows):
        if expected != observed:
            raise RuntimeError(f'construction differs from Lean model: {name}')
    accepted = sum(row.startswith(b'1 ') for row in expected_rows)
    if accepted != 27:
        raise RuntimeError(f'unexpected acceptance coverage: {accepted}')
    report.write_text(json.dumps({'cases': names, 'accepted': accepted, 'rejected': len(rows)-accepted,
        'leaf_entries_compared': accepted*4096, 'input_sha256': hashlib.sha256(payload).hexdigest(),
        'output_sha256': hashlib.sha256(actual).hexdigest(),
        'scope': 'canonical leaf-word differential replay; no final-binary refinement or production admission'}, indent=2)+'\n')
    print(f'closed-root Lean/C comparison: {len(rows)} cases, {accepted*4096} accepted leaves PASS')


if __name__ == '__main__':
    main()
