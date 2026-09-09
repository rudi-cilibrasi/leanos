#!/usr/bin/env python3
"""Replay measured J1900 CPUID words and rejection mutations through Lean."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
corpus = root / 'hardware/cpu-corpus/qotom-j1900-20260909'
fields = ('basic', 'features', 'structured', 'extended', 'extendedFeatures')
leaves = (0, 1, 7, 0x80000000, 0x80000001)
manifest = json.loads((corpus / 'provenance.json').read_text())
captures = []
for name, digest in sorted(manifest['files'].items()):
    raw = (corpus / name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest, name
    lines = raw.decode().splitlines()
    assert lines[0] == 'leaf\tsubleaf\teax\tebx\tecx\tedx', name
    rows = [tuple(int(word, 16) for word in line.split('\t')) for line in lines[1:]]
    assert len(rows) == 5 and all(len(row) == 6 for row in rows), name
    assert [row[:2] for row in rows] == [(leaf, 0) for leaf in leaves], name
    assert all(0 <= word <= 0xffffffff for row in rows for word in row), name
    captures.append({field: list(row[2:]) for field, row in zip(fields, rows)})
assert len(captures) == 4


def literal(snapshot, version=1, present=31):
    members = [f'version := {version}', f'present := {present}']
    for field in fields:
        values = ', '.join(f'{reg} := 0x{word:x}' for reg, word in zip(('eax', 'ebx', 'ecx', 'edx'), snapshot[field]))
        members.append(field + ' := { ' + values + ' }')
    return '{ ' + ', '.join(members) + ' }'


checks = ['import LeanOS.J1900CpuProfile', 'import LeanOS.PrivilegeEntryControl',
          'open LeanOS.J1900CpuProfile']
count = 0


def check(snapshot, reason=None, **kwargs):
    global count
    expected = '.ok selected' if reason is None else '.error .' + reason
    checks.append(f'example : select ({literal(snapshot, **kwargs)} : Snapshot) = {expected} := by rfl')
    count += 1


for snapshot in captures:
    check(snapshot)
base = captures[0]
check(base, 'version', version=2)
for bit in range(5):
    check(base, 'presence', present=31 ^ (1 << bit))
check(base, 'presence', present=63)
for field, word, value, reason in (
        ('basic', 0, 6, 'basicRange'), ('extended', 0, 0x80000000, 'extendedRange'),
        ('basic', 1, 0x68747541, 'vendor'), ('features', 0, 0x30679, 'signature'),
        ('features', 0, 0x40678, 'signature')):
    changed = copy.deepcopy(base)
    changed[field][word] = value
    check(changed, reason)
for field, word, bits, reason in (
        ('features', 3, (0, 3, 5, 6, 11, 23, 24, 25, 26), 'requiredLegacy'),
        ('extendedFeatures', 3, (11, 20, 29), 'requiredExtended'),
        ('structured', 1, (7,), 'smep')):
    for bit in bits:
        changed = copy.deepcopy(base)
        changed[field][word] &= ~(1 << bit)
        check(changed, reason)
for field, word, bits, reason in (
        ('features', 2, (26, 27, 28), 'unexpectedExtendedState'),
        ('structured', 1, (20,), 'smap')):
    for bit in bits:
        changed = copy.deepcopy(base)
        changed[field][word] |= 1 << bit
        check(changed, reason)

# Exercise the vendor/mode distinction and selector boundary independently of
# CPU admission. In particular, an Intel long-mode non-null target is enabled,
# while RPL-only and upper-register bits must not make a null selector valid.
entry_count = 0
for vendor in ('intel', 'amd', 'unsupported'):
    for mode in ('protected32', 'long64', 'compatibility'):
        for exposed in (False, True):
            for selector in (0, 1, 2, 3, 4, 8, 0x10000, 0x10003, 0x10008):
                expected = (exposed and (vendor == 'intel' or
                            (vendor == 'amd' and mode != 'long64')) and
                            (selector & 0xfffc) != 0)
                control = ('{ acceptedControl with '
                           'cpu := { selectedCpu with '
                           f'vendor := .{vendor}, mode := .{mode}, '
                           f'sysenterExposed := {str(exposed).lower()} }}, '
                           f'msrs := {{ deniedMsrs with sysenterCs := {selector} }} }}')
                checks.append('open LeanOS.PrivilegeEntryControl in\n'
                              f'example : enabled ({control}) .sysenter = '
                              f'{str(expected).lower()} := by rfl')
                entry_count += 1

output = root / 'build/j1900'
output.mkdir(parents=True, exist_ok=True)
path = output / 'Checks.lean'
path.write_text('\n'.join(checks) + '\n')
subprocess.run(['lake', 'build', 'LeanOS.J1900CpuProfile',
                'LeanOS.PrivilegeEntryControl'], cwd=root, check=True)
subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root, check=True)
print(f'J1900 CPU profile: {len(captures)} captures, {count} Lean selection/rejection checks passed')
print(f'Fast entry: {entry_count} vendor/mode/exposure/selector checks passed')
