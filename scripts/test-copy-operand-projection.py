#!/usr/bin/env python3
"""Compare the prevalidated-location projection with the compiled Lean model."""
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def main():
    cc = os.environ.get('LEANOS_CC', 'gcc')
    out = ROOT / 'build/copy-roots' / ('operands-' + Path(cc).name)
    out.mkdir(parents=True, exist_ok=True)
    report = out / 'results.json'
    report.unlink(missing_ok=True)
    runner = out / 'replay'
    subprocess.run([cc, '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                    str(ROOT / 'experiments/copy-roots/operands-replay.c'), '-o', str(runner)], check=True)
    rows = []
    rng = random.Random(329)
    for direction in range(2):
        for count in range(17):
            for pattern in range(4):
                frames = [rng.randrange(1 << 40), rng.randrange(1 << 40)]
                locations = []
                for i in range(count):
                    slot = 0 if pattern == 0 else int(i >= 8) if pattern == 1 else i % 2
                    offset = (4088 + i) % 4096 if pattern < 2 else rng.randrange(4096)
                    locations.extend([frames[slot], offset])
                rows.append(' '.join(map(str, [count, direction, 0x700, 0x200000, *locations])))
    payload = ('\n'.join(rows) + '\n').encode()
    expected = subprocess.check_output([str(ROOT / '.lake/build/bin/leanos-copy-operand-projection')], input=payload)
    actual = subprocess.check_output([str(runner)], input=payload)
    if len(actual.splitlines()) != len(rows) or actual != expected:
        raise RuntimeError('operand projection differs from Lean model')
    report.write_text(json.dumps({'cases': len(rows),
        'input_sha256': hashlib.sha256(payload).hexdigest(),
        'output_sha256': hashlib.sha256(actual).hexdigest(),
        'scope': 'accepted prevalidated locations only; no pointer validation, lifetime or production admission'}, indent=2)+'\n')
    print(f'copy operand Lean/C projection: {len(rows)} cases PASS')


if __name__ == '__main__':
    main()
