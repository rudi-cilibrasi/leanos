#!/usr/bin/env python3
"""Replay actual MADT entry bytes and inventory mutations through scalar Lean."""
import hashlib
import json
import itertools
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / 'hardware/lab/observations/qotom-bootstrap-20260911'
manifest = json.loads((CAPTURE / 'manifest.json').read_text())
name = 'cycle-1/acpi/00000000b97a6ae0.bin'
raw = (CAPTURE / name).read_bytes()
assert hashlib.sha256(raw).hexdigest() == manifest['files'][name]
records = []
offset = 44
while offset < len(raw):
    size = raw[offset + 1]
    assert size >= 2 and offset + size <= len(raw)
    records.append(raw[offset:offset + size])
    offset += size
cpu_indices = [i for i, record in enumerate(records) if record[0] == 0]
assert len(cpu_indices) == 4

def changed(index, byte, value):
    result = list(records)
    record = bytearray(result[index]); record[byte] = value
    result[index] = bytes(record)
    return result

cases = [('native', records, 0, 0), ('wrong-executing', records, 2, 76)]
for position, index in enumerate(cpu_indices):
    cases.append((f'disabled-{position}', changed(index, 4, 0), 0, 77))
    cases.append((f'online-{position}', changed(index, 4, 3), 0, 73))
    cases.append((f'wrong-id-{position}', changed(index, 3, 7), 0, 77))
swapped = list(records)
a, b = cpu_indices[:2]; swapped[a], swapped[b] = swapped[b], swapped[a]
cases += [('swapped', swapped, 0, 77),
          ('missing-last', [r for i, r in enumerate(records) if i != cpu_indices[-1]], 0, 75),
          ('duplicate', records + [records[cpu_indices[0]]], 0, 74),
          ('extra', records + [bytes([0, 8, 5, 8, 1, 0, 0, 0])], 0, 77),
          ('unsupported', records + [bytes([9, 2])], 0, 70),
          ('wrong-width', records + [bytes([0, 7])], 0, 71),
          ('truncated', records + [bytes([0])], 0, 72)]

# Every permutation has the same ID bitset/count; only the baseline order passes.
for order in itertools.permutations(range(4)):
    permuted = list(records)
    for position, source_index in enumerate(order):
        permuted[cpu_indices[position]] = records[cpu_indices[source_index]]
    cases.append(('order-' + ''.join(map(str, order)), permuted, 0,
                  0 if order == (0, 1, 2, 3) else 77))
# Reserved flag bits and firmware processor UIDs are not part of Processor.
# Preserve the reference decoder's semantics rather than silently tightening them.
cases += [('reserved-flags', changed(cpu_indices[0], 7, 128), 0, 0),
          ('firmware-uid', changed(cpu_indices[0], 2, 255), 0, 0)]

# The test driver allocates lists; byteStepQuery itself has only scalar inputs.
source = (ROOT / 'LeanOS/QotomMadtStream.lean').read_text()
source += '''
def streamTest (bytes : List UInt64) (length executing : UInt64)
    (state : List UInt64 := [44,0,0,0,0,0,0,256,0,0,0,0]) : UInt64 × UInt64 :=
  match bytes with
  | [] => (0, 999)
  | byte :: rest =>
    let q := fun word => LeanOS.QotomMadtStream.byteStepQuery
      state[0]! state[1]! state[2]! state[3]! state[4]! state[5]!
      state[6]! state[7]! state[8]! state[9]! state[10]! state[11]!
      length executing state[0]! byte word
    if q 1 == 2 then (q 1, q 2)
    else if rest.isEmpty then (q 1, q 2)
    else streamTest rest length executing ((List.range 12).map fun i => q (UInt64.ofNat (i+3)))
'''
source += """
def fullTableTest (bytes : List UInt8) (executing : UInt32) : Bool :=
  match LeanOS.BootTopology.decodeCompleteMadtSnapshot bytes executing executing with
  | .error _ => false
  | .ok snapshot =>
    match LeanOS.QotomBspTopology.check snapshot with
    | .error _ => false
    | .ok _ => true
"""
for label, recs, executing, error in cases:
    data = b''.join(recs)
    words = ','.join(map(str, data))
    source += f'#eval streamTest [{words}] {44+len(data)} {executing}\n'
    # Repair only the outer SDT envelope of each named entry mutation so that
    # the reference reaches the same entry bytes as the scalar stream.
    table = bytearray(raw[:44] + data)
    table[4:8] = len(table).to_bytes(4, 'little')
    table[9] = 0; table[9] = (-sum(table)) & 255
    source += f'#eval fullTableTest [{",".join(map(str, table))}] {executing}\n'
# Probe invalid scalar inputs directly, independent of table traversal.
initial = [44,0,0,0,0,0,0,256,0,0,0,0,132,0,44,0]
probes = []
for label, field, value in [
    ('offset-mismatch',0,45), ('record-offset',1,12), ('record-kind',2,256),
    ('record-length',3,13), ('apic-width',4,256), ('flags-width',5,2**32),
    ('processor-count',6,5), ('admitted-width',7,257),
    ('table-overflow',12,2**64-1), ('table-too-short',12,43),
    ('executing-width',13,256), ('byte-offset',14,43), ('byte-width',15,256),
]:
    args = list(initial); args[field] = value
    probes.append((label, args, 69))
args = list(initial); args[12] = 45
probes.append(('terminal-incomplete-record', args, 72))
for _, args, error in probes:
    query = 'LeanOS.QotomMadtStream.byteStepQuery ' + ' '.join(map(str,args))
    source += f'#eval (List.range 18).map (fun w => {query} (UInt64.ofNat w))\n'

with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp) / 'Replay.lean'; path.write_text(source)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    actual = result.stdout.splitlines()
    expected = [value for _, _, _, error in cases
                for value in (f'({2 if error else 3}, {error})', 'false' if error else 'true')]
    expected += ['[1, 2, ' + str(error) + ', ' + ', '.join(['0']*15) + ']'
                 for _, _, error in probes]
    if actual != expected:
        for index, (want, got) in enumerate(zip(expected, actual)):
            if want != got: print(index, 'expected', want, 'got', got)
        raise SystemExit('scalar MADT replay mismatch: ' + result.stdout)
print(f'PASS {len(cases)} native MADT scalar/full-table cases')
# The independent C runner consumes these same named cases and expectations.
out = ROOT / 'build/qotom-madt-stream'
out.mkdir(parents=True, exist_ok=True)
header = '#include <stddef.h>\n#include <stdint.h>\n'
for i, (_, recs, _, _) in enumerate(cases):
    header += f'static const uint8_t input_{i}[] = {{{",".join(map(str, b"".join(recs)))}}};\n'
header += 'static const struct { const char *name; const uint8_t *bytes; size_t length; uint64_t executing, error; } cases[] = {\n'
for i, (label, _, executing, error) in enumerate(cases):
    header += f'{{"{label}",input_{i},sizeof(input_{i}),{executing},{error}}},\n'
header += '};\n'
header += 'static const struct { const char *name; uint64_t args[16], error; } probes[] = {\n'
for label, args, error in probes:
    header += '{"' + label + '",{' + ','.join(str(x)+'ULL' for x in args) + '},' + str(error) + '},\n'
header += '};\n'
(out / 'cases.h').write_text(header)
print(f'PASS {len(probes)} malformed scalar probes, all 18 projection words')
