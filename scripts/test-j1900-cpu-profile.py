#!/usr/bin/env python3
"""Replay measured J1900 CPUID words and rejection mutations through Lean."""
import copy
import hashlib
import json
import os
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
          'import LeanOS.J1900EntryControl',
          'import LeanOS.J1900CpuControlPolicy',
          'open LeanOS.J1900CpuProfile']
count = 0
raw_count = 0
raw_cases = []
control_count = 0
reasons = ('version', 'presence', 'basicRange', 'extendedRange', 'vendor',
           'signature', 'requiredLegacy', 'requiredExtended', 'smep',
           'unexpectedExtendedState', 'smap')


def raw_words(snapshot, version=1, present=31):
    return [version, present] + [word for field in fields for word in snapshot[field]]


def check_raw(words, expected):
    global raw_count
    args = ' '.join(str(word) for word in words)
    checks.append(f'example : selectRaw {args} = {expected} := by rfl')
    raw_cases.append((list(words), expected))
    raw_count += 1


def check(snapshot, reason=None, **kwargs):
    global count, control_count
    expected = '.ok selected' if reason is None else '.error .' + reason
    checks.append(f'example : select ({literal(snapshot, **kwargs)} : Snapshot) = {expected} := by rfl')
    check_raw(raw_words(snapshot, **kwargs),
              0x10000 if reason is None else reasons.index(reason) + 1)
    checks.append('example : LeanOS.J1900EntryControl.validate '
                  f'({literal(snapshot, **kwargs)} : Snapshot) '
                  'LeanOS.J1900EntryControl.deniedControl = '
                  f'{str(reason is None).lower()} := by rfl')
    control_count += 1
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

# A high bit in any slot must reject before UInt32 conversion, including
# unused registers and the version/presence words.
for index in range(22):
    words = raw_words(base)
    words[index] |= 1 << 32
    check_raw(words, 12)

control_changes = [
    'cpu := LeanOS.PrivilegeEntryControl.selectedCpu',
    'cpu := { LeanOS.J1900EntryControl.cpu with mode := .compatibility }',
    'boot := { writesComplete := false, readbackMatches := true }',
    'boot := { writesComplete := true, readbackMatches := false }',
    'int80ManifestPresent := false',
    'extendedFeatures := LeanOS.PrivilegeEntryControl.reviewedExtendedFeatures',
    'extendedControls := { LeanOS.ExtendedState.deniedControls with cr0Ts := false }',
]
for field, value in (('eferLme', 'false'), ('eferLma', 'false'),
                     ('eferNxe', 'false'), ('eferSce', 'true')):
    control_changes.append('msrs := { LeanOS.PrivilegeEntryControl.deniedMsrs with '
                           f'{field} := {value} }}')
for field in ('star', 'lstar', 'cstar', 'sfmask', 'sysenterCs', 'sysenterEsp', 'sysenterEip'):
    control_changes.append('msrs := { LeanOS.PrivilegeEntryControl.deniedMsrs with '
                           f'{field} := 1 }}')
for change in control_changes:
    checks.append('example : LeanOS.J1900EntryControl.validate '
                  f'({literal(base)} : Snapshot) '
                  '{ LeanOS.J1900EntryControl.deniedControl with ' + change +
                  ' } = false := by rfl')
    control_count += 1
for mechanism, vector in (('syscall', 6), ('sysenter', 13)):
    checks.append('example : LeanOS.PrivilegeEntryControl.expectedVector '
                  f'LeanOS.J1900EntryControl.cpu .{mechanism} = {vector} := by rfl')

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

# Exact full-width MSR readback: every bit differs from the denied tuple
# in one mutation. This covers reserved EFER bits and upper target bits.
msr_denied = [0xd00, 0, 0, 0, 0, 0, 0, 0]
msr_cases = [(msr_denied, 1)]
for slot in range(8):
    for bit in range(64):
        changed = list(msr_denied)
        changed[slot] ^= 1 << bit
        msr_cases.append((changed, 0))
for words, expected in msr_cases:
    args = ' '.join(str(word) for word in words)
    checks.append(f'example : LeanOS.J1900MsrReadback.checkRaw {args} = {expected} := by rfl')

policy_cpu = raw_words(base)
policy_args = ' '.join(map(str, policy_cpu + msr_denied))
checks += [
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 0 = 1 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 1 = 1 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 2 = 0 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 3 = 1 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 4 = 0x10000 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 5 = 1 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 6 = 1 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {policy_args} 7 = 0 := by rfl',
]
wrong_vendor = list(policy_cpu); wrong_vendor[3] ^= 1
bad_cpu_args = ' '.join(map(str, wrong_vendor + msr_denied))
bad_msr = list(msr_denied); bad_msr[0] ^= 1
bad_msr_args = ' '.join(map(str, policy_cpu + bad_msr))
checks += [
    f'example : LeanOS.J1900CpuControlPolicy.query {bad_cpu_args} 1 = 2 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {bad_cpu_args} 2 = 5 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {bad_msr_args} 1 = 2 := by rfl',
    f'example : LeanOS.J1900CpuControlPolicy.query {bad_msr_args} 2 = 13 := by rfl',
]

output = root / 'build/j1900'
output.mkdir(parents=True, exist_ok=True)
path = output / 'Checks.lean'
path.write_text('\n'.join(checks) + '\n')
subprocess.run(['lake', 'build', 'LeanOS.J1900CpuProfile',
                'LeanOS.PrivilegeEntryControl', 'LeanOS.J1900EntryControl',
                'LeanOS.J1900CpuControlPolicy'], cwd=root, check=True)
subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root, check=True)
print(f'J1900 CPU profile: {len(captures)} captures, {count} Lean selection/rejection checks passed')
print(f'Fast entry: {entry_count} vendor/mode/exposure/selector checks passed')
print(f'Raw CPU boundary: {raw_count} selection/rejection/width checks passed')
print(f'J1900 control binding: {control_count} snapshot/readback checks and two vector checks passed')

# Include the freshly generated translation unit so the compiler itself checks
# the exported signature; do not transcribe a second prototype into this test.
host = output / 'raw-host.c'
lines = ['#include <stdio.h>',
         '#include "../../.lake/build/ir/LeanOS/J1900CpuProfile.c"',
         'extern void lean_initialize(void);',
         'int main(void) {', '  lean_initialize();',
         '  lean_object *init = initialize_leanos_LeanOS_J1900CpuProfile(1);',
         '  if (lean_io_result_is_error(init)) return 2;',
         '  lean_dec_ref(init);', '  lean_io_mark_end_initialization();']
for index, (words, expected) in enumerate(raw_cases):
    args = ', '.join(f'UINT64_C({word})' for word in words)
    lines.append(f'  if (leanos_j1900_cpu_select({args}) != UINT64_C({expected})) {{')
    lines.append(f'    fprintf(stderr, "raw CPU case {index} failed\\n"); return 1; }}')
lines.extend([f'  puts("Generated-C CPU boundary: {raw_count} cases passed");',
              '  return 0;', '}'])
host.write_text('\n'.join(lines) + '\n')
rows = ['{' + ', '.join(f'UINT64_C({word})' for word in words + [expected]) + '}'
        for words, expected in raw_cases]
(output / 'raw-cases.h').write_text(
    'static const uint64_t cpu_cases[][23] = {\n' + ',\n'.join(rows) + '\n};\n')
executable = output / 'raw-host'
prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                 cwd=root, text=True).strip()
host_object = output / 'raw-host.o'
subprocess.run([os.environ.get('LEANOS_HOST_CC', 'gcc'), '-O1',
                '-I' + str(Path(prefix) / 'include'), '-c', str(host),
                '-o', str(host_object)], cwd=root, check=True)
subprocess.run(['lake', 'env', 'leanc', str(host_object), '-o', str(executable)],
               cwd=root, check=True)
subprocess.run([str(executable)], cwd=root, check=True)

# The early boot consumer has no Lean runtime or allocator. Retain only the
# exported function and its transitive machine-code dependencies, then require
# a closed object. This also catches accidental lazy initialization helpers.
# Match the image builder's Clang handling: general-registers-only changes
# FLT_EVAL_METHOD unless source-width evaluation is explicitly selected. Lean's
# header rejects the resulting semantics even for these integer-only exports.
compiler = os.environ.get('LEANOS_CC', 'gcc')
freestanding_flags = ['-O2', '-ffreestanding', '-fno-stack-protector',
                      '-mno-red-zone', '-mgeneral-regs-only',
                      '-fno-asynchronous-unwind-tables', '-fno-unwind-tables',
                      '-ffunction-sections', '-fdata-sections']
compiler_version = subprocess.check_output([compiler, '--version'], text=True)
if 'clang' in compiler_version.splitlines()[0].lower():
    freestanding_flags += ['-ffp-eval-method=source', '-Wno-error=pragmas',
                           '-fno-jump-tables']
generated_object = output / 'cpu-generated.o'
closed_object = output / 'cpu-freestanding.elf'
subprocess.run([compiler, *freestanding_flags,
                '-I' + str(Path(prefix) / 'include'), '-c',
                str(root / '.lake/build/ir/LeanOS/J1900CpuProfile.c'),
                '-o', str(generated_object)], cwd=root, check=True)
subprocess.run(['ld', '--gc-sections', '-e', 'leanos_j1900_cpu_select',
                str(generated_object), '-o', str(closed_object)], cwd=root, check=True)
undefined = subprocess.check_output(['nm', '-u', str(closed_object)], text=True)
if undefined.strip():
    raise RuntimeError('CPU boundary needs runtime symbols:\n' + undefined)
print('Freestanding CPU boundary: no unresolved runtime dependencies')

# Replay the same full-width corpus through the separately generated MSR C
# translation unit and prove its retained entry point links without runtime.
msr_rows = ['{' + ', '.join(f'UINT64_C({word})' for word in words + [expected]) + '}'
            for words, expected in msr_cases]
(output / 'msr-cases.h').write_text(
    'static const uint64_t msr_cases[][9] = {\n' + ',\n'.join(msr_rows) + '\n};\n')
msr_host = output / 'msr-host.c'
msr_host.write_text('''#include <stdio.h>
#include "../../.lake/build/ir/LeanOS/J1900MsrReadback.c"
#include "msr-cases.h"
extern void lean_initialize(void);
int main(void) {
  lean_initialize();
  lean_object *init = initialize_leanos_LeanOS_J1900MsrReadback(1);
  if (lean_io_result_is_error(init)) return 2;
  lean_dec_ref(init);
  lean_io_mark_end_initialization();
  for (size_t i = 0; i < sizeof(msr_cases) / sizeof(msr_cases[0]); ++i) {
    const uint64_t *w = msr_cases[i];
    if (leanos_j1900_msr_readback(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]) != w[8]) {
      fprintf(stderr, "MSR case %zu failed\\n", i);
      return 1;
    }
  }
  puts("Generated-C MSR boundary: 513 cases passed");
  return 0;
}
''')
msr_object = output / 'msr-host.o'
msr_executable = output / 'msr-host'
subprocess.run([os.environ.get('LEANOS_HOST_CC', 'gcc'), '-O1',
                '-I' + str(Path(prefix) / 'include'), '-c', str(msr_host),
                '-o', str(msr_object)], cwd=root, check=True)
subprocess.run(['lake', 'env', 'leanc', str(msr_object), '-o', str(msr_executable)],
               cwd=root, check=True)
subprocess.run([str(msr_executable)], cwd=root, check=True)
msr_generated = output / 'msr-generated.o'
msr_closed = output / 'msr-freestanding.elf'
subprocess.run([compiler, *freestanding_flags,
                '-I' + str(Path(prefix) / 'include'), '-c',
                str(root / '.lake/build/ir/LeanOS/J1900MsrReadback.c'),
                '-o', str(msr_generated)], cwd=root, check=True)
subprocess.run(['ld', '--gc-sections', '-e', 'leanos_j1900_msr_readback',
                str(msr_generated), '-o', str(msr_closed)], cwd=root, check=True)
undefined = subprocess.check_output(['nm', '-u', str(msr_closed)], text=True)
if undefined.strip():
    raise RuntimeError('MSR boundary needs runtime symbols:\n' + undefined)
print('Freestanding MSR boundary: no unresolved runtime dependencies')

# The composed production checkpoint retains only the two reviewed scalar
# dependencies and publishes no CPL3 authority.
policy_generated = output / 'cpu-control-policy-generated.o'
policy_closed = output / 'cpu-control-policy-freestanding.elf'
subprocess.run([compiler, *freestanding_flags,
                '-I' + str(Path(prefix) / 'include'), '-c',
                str(root / '.lake/build/ir/LeanOS/J1900CpuControlPolicy.c'),
                '-o', str(policy_generated)], cwd=root, check=True)
subprocess.run(['ld', '--gc-sections', '-e',
                'leanos_j1900_cpu_control_policy_query',
                str(policy_generated), str(generated_object), str(msr_generated),
                '-o', str(policy_closed)], cwd=root, check=True)
undefined = subprocess.check_output(['nm', '-u', str(policy_closed)], text=True)
if undefined.strip():
    raise RuntimeError('CPU/control policy boundary needs runtime symbols:\n' + undefined)
print('Freestanding CPU/control policy: no unresolved runtime dependencies')
