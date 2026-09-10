#!/usr/bin/env python3
"""Replay retained PCI headers into the typed decoder; no hardware admission."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
CAPTURE = ROOT / 'hardware/lab/observations/qotom-pci-20260910'
OUTPUT = ROOT / 'build/pci-header-capture/Replay.lean'


def replay_source():
    inventory = json.loads((CAPTURE / 'inventory.json').read_text())
    spec = importlib.util.spec_from_file_location('pci_collector', ROOT / 'hardware/lab/capture-pci.py')
    collector = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(collector)
    before = (CAPTURE / 'listing-before.txt').read_text()
    if before != (CAPTURE / 'listing-after.txt').read_text():
        raise ValueError('PCI listing changed during retained capture')
    selectors = collector.selectors(before)
    if selectors != [function['selector'] for function in inventory['functions']]:
        raise ValueError('capture projection omits, reorders, or adds a PCI function')
    expected_files = {'listing-before.txt', 'listing-after.txt'} | {
        selector.replace(':', '-') + '.txt' for selector in selectors}
    if expected_files != {command['file'] for command in inventory['commands']}:
        raise ValueError('capture digest inventory does not cover the raw observations')
    for command in inventory['commands']:
        data = (CAPTURE / command['file']).read_bytes()
        if hashlib.sha256(data).hexdigest() != command['sha256']:
            raise ValueError(f"capture digest mismatch: {command['file']}")
    lines = ['import LeanOS.PCIHeaderObservation',
             'open LeanOS.PCIHeaderObservation', '']
    for index, function in enumerate(inventory['functions']):
        selector = function['selector']
        domain, bus, device, slot = map(int, selector.removeprefix('pci').split(':'))
        if domain != 0:
            raise ValueError('capture contains a nonzero PCI domain')
        words = [int(word, 16) for word in
                 (CAPTURE / (selector.replace(':', '-') + '.txt')).read_text().split()]
        if words != function['words']:
            raise ValueError(f'capture projection differs from raw words: {selector}')
        raw = f'⟨⟨{bus}, {device}, {slot}⟩, [{", ".join(map(str, words))}]⟩'
        lines.append(f'def raw{index} : RawHeader := {raw}')
        checks = [f'h.raw == raw{index}']
        for projected, stored in [('identity.vendor', 'vendor'), ('identity.device', 'device'),
                                  ('identity.classCode', 'class_code'), ('command', 'command'),
                                  ('status', 'status'), ('revision', 'revision')]:
            checks.append(f'h.{projected} == {function[stored]}')
        checks.append(f'h.multifunction == {str(function["multifunction"]).lower()}')
        lines.append(f'example : (match decode raw{index} with | .ok h => '
                     + ' && '.join(checks) + ' | .error _ => false) = true := by native_decide')
        if 'bridge' in function:
            checks = [f'r.{key} == {function["bridge"][key]}'
                      for key in ('primary', 'secondary', 'subordinate', 'control')]
            expression = '(match h.layout with | .bridge r => ' + ' && '.join(checks) + ' | _ => false)'
        else:
            expression = 'h.layout == .endpoint'
        lines.append(f'example : (match decode raw{index} with | .ok h => {expression}'
                     + ' | .error _ => false) = true := by native_decide')
    # Distinct sentinel values independently exercise each bridge field's offset
    # and mask. This is a synthetic transport fixture, not a board observation.
    lines.extend([
        'def windows : RawHeader := ⟨⟨0, 28, 0⟩,',
        '  [0x0f488086, 0x00100407, 0x0604000e, 0x00810000, 0, 0,',
        '   0x99030201, 0xabcd1234, 0x23456789, 0x3456789a,',
        '   0x456789ab, 0x56789abc, 0x6789abcd, 0, 0, 0xbeef0102]⟩',
        'example : (match decode windows with',
        '  | .ok h => match h.layout with',
        '    | .bridge r => r == ⟨1, 2, 3, 0xbeef, 0x1234, 0xabcd,',
        '        0x23456789, 0x3456789a, 0x456789ab, 0x56789abc, 0x6789abcd⟩',
        '    | _ => false',
        '  | .error _ => false) = true := by native_decide',
    ])
    for raw, error in [
        ('⟨⟨256, 0, 0⟩, raw0.words⟩', 'invalidBDF'),
        ('⟨⟨0, 32, 0⟩, raw0.words⟩', 'invalidBDF'),
        ('⟨⟨0, 0, 8⟩, raw0.words⟩', 'invalidBDF'),
        ('⟨raw0.bdf, raw0.words.tail⟩', 'wrongWordCount'),
        ('⟨raw0.bdf, raw0.words ++ [0]⟩', 'wrongWordCount'),
        ('⟨raw0.bdf, raw0.words.set 0 0x100000000⟩', 'nonDword'),
        ('⟨raw0.bdf, raw0.words.set 15 0x100000000⟩', 'nonDword'),
        ('⟨raw0.bdf, raw0.words.set 0 0xffffffff⟩', 'absent'),
        ('⟨raw0.bdf, raw0.words.set 3 0x20000⟩', 'unsupportedLayout'),
    ]:
        lines.append(f'example : (match decode {raw} with | .error e => e == .{error}'
                     + ' | .ok _ => false) = true := by native_decide')
    return '\n'.join(lines) + '\n'


def main():
    source = replay_source()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(OUTPUT)], cwd=ROOT, check=True)
    print(f'PCI header capture replay and transport fixtures passed ({source.count("example :")} checks)')


if __name__ == '__main__':
    main()
