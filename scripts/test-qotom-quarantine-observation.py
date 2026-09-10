#!/usr/bin/env python3
"""Synthetic command-clear traces based on hashed PCI capture, not hardware writes."""
import importlib.util
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / 'build/qotom-quarantine-observation/Replay.lean'


def replay_source():
    spec = importlib.util.spec_from_file_location('capture', ROOT / 'scripts/test-pci-header-capture.py')
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    definitions = [line for line in capture.replay_source().splitlines() if line.startswith('def raw')]
    lines = ['import LeanOS.QotomPCIQuarantineObservation',
             'open LeanOS.PCIHeaderObservation LeanOS.QotomPCIQuarantineObservation', *definitions,
             'def cleared (r : RawHeader) : RawHeader :=',
             '  { r with words := r.words.set 1 (r.words.getD 1 0 &&& 0xffff0000) }']
    # Independent expected trace order: downstream endpoints, root endpoints, bridges.
    indices = [12, 13, 14, 0, 1, 2, 3, 4, 5, 10, 11, 6, 7, 8, 9]
    for i, raw in enumerate(indices):
        lines.append(f'def step{i} : Step := ⟨raw{raw}.bdf, 4, 2, 0, cleared raw{raw}⟩')
    lines.append('def trace : List Step := [' + ', '.join(f'step{i}' for i in range(15)) + ']')
    lines.append('example : (match check trace with | .ok w => w.steps.map (·.step) == trace'
                 ' | .error _ => false) = true := by native_decide')

    def rejects(value, error):
        lines.append(f'example : (match check ({value}) with | .error e => e == {error}'
                     ' | .ok _ => false) = true := by native_decide')

    rejects('trace.tail', '.count')
    rejects('trace ++ [step0]', '.count')
    rejects('trace.set 0 step1 |>.set 1 step0', '.inventory 0')
    for i in range(15):
        for change in ('offset := 5', 'width := 4', 'value := 4'):
            rejects(f'trace.set {i} {{ step{i} with {change} }}', f'.write {i}')
        rejects(f'trace.set {i} {{ step{i} with target := ⟨5, 0, 0⟩ }}', f'.target {i}')
        for word, value, error in [
            (1, f'(step{i}.readback.words.getD 1 0) ||| 4', f'.command {i}'),
            (0, '0x12348086', f'.inventory {i}'),
            (0, '0xffffffff', f'.header {i} .absent'),
            (15, '0x100000000', f'.header {i} .nonDword'),
        ]:
            rejects(f'trace.set {i} {{ step{i} with readback := ⟨step{i}.readback.bdf, '
                    f'step{i}.readback.words.set {word} ({value})⟩ }}', error)
    for i in range(11, 15):
        rejects(f'trace.set {i} {{ step{i} with readback := ⟨step{i}.readback.bdf, '
                f'step{i}.readback.words.set 6 0⟩ }}', f'.inventory {i}')
    return '\n'.join(lines) + '\n'


def main():
    source = replay_source()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(OUTPUT)], cwd=ROOT, check=True)
    print(f'Qotom quarantine observation fixtures passed ({source.count("example :")} synthetic checks)')


if __name__ == '__main__':
    main()
