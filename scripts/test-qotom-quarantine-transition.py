#!/usr/bin/env python3
"""Synthetic before/after binding checks using hash-verified captured PCI headers."""
import importlib.util
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/qotom-quarantine-transition/Replay.lean'


def main():
    spec = importlib.util.spec_from_file_location('trace', ROOT / 'scripts/test-qotom-quarantine-observation.py')
    trace = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(trace)
    source = trace.replay_source()  # revalidates raw capture hashes and selectors
    lines = [line for line in source.splitlines() if not line.startswith('example :')]
    lines[0] = 'import LeanOS.QotomPCIQuarantineTransition'
    lines.append('def initial : List RawHeader := [' + ', '.join(f'raw{i}' for i in range(15)) + ']')

    def check(before, after, expected):
        lines.append(f'example : (match LeanOS.QotomPCIQuarantineTransition.check ({before}) ({after}) with '
                     f'| .error e => {expected} | .ok _ => false) = true := by native_decide')

    def accepts(before, after):
        lines.append(f'example : (LeanOS.QotomPCIQuarantineTransition.check ({before}) ({after})).isOk = true := by native_decide')

    accepts('initial', 'trace')
    lines.append('example : (match LeanOS.QotomPCIQuarantineTransition.check initial trace with '
                 '| .ok w => w.initial.headers.map (·.raw) == initial && w.trace.steps.map (·.step) == trace '
                 '| .error _ => false) = true := by native_decide')
    check('initial.tail', 'trace', 'e == .initial .count')
    check('initial.set 0 ⟨raw0.bdf, raw0.words.set 0 0x12348086⟩', 'trace', 'e == .initial (.identity 0)')
    check('initial', 'trace.set 0 { step0 with value := 4 }', 'e == .trace (.write 0)')
    for i in range(15):
        changed = (f'trace.set {i} {{ step{i} with readback := ⟨step{i}.readback.bdf, '
                   f'step{i}.readback.words.set 8 ((step{i}.readback.words.getD 8 0) ^^^ 1)⟩ }}')
        check('initial', changed, f'e == .registers {i}')
    # Status is volatile; the before Command may be nonzero, while the trace
    # checker still requires its synthetic post-write Command to be zero.
    accepts('initial', 'trace.set 0 { step0 with readback := ⟨step0.readback.bdf, '
            'step0.readback.words.set 1 ((step0.readback.words.getD 1 0) ^^^ 0x10000)⟩ }')
    accepts('initial.set 0 ⟨raw0.bdf, raw0.words.set 1 0xffff⟩', 'trace')
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text('\n'.join(lines) + '\n')
    subprocess.run(['lake', 'env', 'lean', str(OUT)], cwd=ROOT, check=True)
    print(f'Qotom initial/trace binding passed ({sum(s.startswith("example :") for s in lines)} synthetic checks)')


if __name__ == '__main__':
    main()
