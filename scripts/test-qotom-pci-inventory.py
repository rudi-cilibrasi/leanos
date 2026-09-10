#!/usr/bin/env python3
"""Replay the hashed AHCI capture and reject whole-inventory mutations."""
import importlib.util
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / 'build/qotom-pci-inventory/Replay.lean'


def replay_source():
    spec = importlib.util.spec_from_file_location('header_capture', ROOT / 'scripts/test-pci-header-capture.py')
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    # The existing collector replay verifies every retained raw digest and the
    # exact before/after selector inventory before any Lean fixture is emitted.
    checked = capture.replay_source()
    definitions = [line for line in checked.splitlines() if line.startswith('def raw')]
    lines = ['import LeanOS.QotomPCIInventory',
             'open LeanOS.PCIHeaderObservation LeanOS.QotomPCIInventory', *definitions,
             'def captured : List RawHeader := [' + ', '.join(f'raw{i}' for i in range(len(definitions))) + ']']
    lines.append('example : (match check captured with | .ok w => '
                 '(w.headers.map (·.raw)) == captured | .error _ => false) = true := by native_decide')

    def rejects(raws, error):
        lines.append(f'example : (match check ({raws}) with | .error e => e == {error}'
                     ' | .ok _ => false) = true := by native_decide')

    rejects('captured.tail', '.count')
    rejects('captured ++ [raw0]', '.count')
    rejects('captured.set 14 raw13', '.address 14')
    rejects('captured.set 0 raw1 |>.set 1 raw0', '.address 0')
    for i in range(len(definitions)):
        rejects(f'captured.set {i} ⟨raw{i}.bdf, raw{i}.words.set 0 0x12348086⟩', f'.identity {i}')
        rejects(f'captured.set {i} ⟨⟨5, 0, 0⟩, raw{i}.words⟩', f'.address {i}')
    # Older IDE profile, and q35 host identity, must not mix into this candidate.
    rejects('captured.set 2 ⟨raw2.bdf, (raw2.words.set 0 0x0f218086).set 2 0x01018a0e⟩', '.identity 2')
    rejects('captured.set 0 ⟨raw0.bdf, raw0.words.set 0 0x29c08086⟩', '.identity 0')
    rejects('captured.set 6 ⟨raw6.bdf, raw6.words.set 3 0x00010000⟩', '.multifunction 6')
    rejects('captured.set 6 ⟨raw6.bdf, raw6.words.set 3 0x00800000⟩', '.routing 6')
    for i in range(6, 10):
        for mask in (1, 0x100, 0x10000):
            rejects(f'captured.set {i} ⟨raw{i}.bdf, raw{i}.words.set 6 ((raw{i}.words.getD 6 0) ^^^ {mask})⟩', f'.routing {i}')
        rejects(f'captured.set {i} ⟨raw{i}.bdf, raw{i}.words.set 15 0⟩', f'.routing {i}')
    rejects('captured.set 14 ⟨raw14.bdf, raw14.words.tail⟩', '.header 14 .wrongWordCount')
    rejects('captured.set 14 ⟨raw14.bdf, raw14.words.set 0 0xffffffff⟩', '.header 14 .absent')
    # Observation matching deliberately retains unsafe command/window values.
    # These are inputs to the next quarantine stage, never DMA-safety evidence.
    lines.extend([
        'def changed : List RawHeader := captured.set 6 ⟨raw6.bdf, (raw6.words.set 1 0xffff).set 8 0xffffffff⟩',
        'example : (match check changed with | .ok w => (w.headers.map (·.raw)) == changed'
        ' | .error _ => false) = true := by native_decide',
    ])
    return '\n'.join(lines) + '\n'


def main():
    source = replay_source()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(OUTPUT)], cwd=ROOT, check=True)
    print(f'Qotom PCI inventory replay passed ({source.count("example :")} checks)')


if __name__ == '__main__':
    main()
