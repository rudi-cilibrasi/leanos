#!/usr/bin/env python3
"""Check synthetic terminal shapes and synthetic/captured BSP observations."""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
base = [3,0,132,0,0,0,0,0,4,0,85,0,0,0,132,0,0x220,1,0xfee00900,0]
cases = [('baseline', base, [1,1,0,4,0xfee00900,0])]
for field in range(16):
    values = list(base); values[field] += 1
    cases.append((f'terminal-{field}', values, [1,2,78,0,0,0]))
for label, field, value, status, error in [
    ('cpuid-width',16,2**32,2,306), ('available-width',17,2,2,307),
    ('sample-width',19,2**32,2,308), ('unavailable',17,0,5,1),
    ('features',16,0,5,2), ('sample-id',19,2,5,3),
    ('not-bsp',18,0xfee00800,5,4), ('disabled-apic',18,0xfee00100,5,5),
    ('x2apic',18,0xfee00d00,5,5), ('reserved',18,0xfee00901,5,5),
]:
    values = list(base); values[field] = value
    cases.append((label,values,[1,status,error,0,0,0]))
capture = ROOT/'hardware/lab/observations/qotom-bootstrap-20260911'
manifest = json.loads((capture/'manifest.json').read_text())
def pinned_json(name):
    raw = (capture/name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == manifest['files'][name]
    return json.loads(raw)
observed = pinned_json('cycle-1/bootstrap.json')
handoff = pinned_json('cycle-1/handoff.json')
native = list(base)
native[15] = handoff['apic']
native[16:] = [observed['cpuid_edx'], int(observed['available']),
               observed['ia32_apic_base'], handoff['apic']]
cases.append(('captured-bsp', native, [1,1,0,4,0xfee00900,0]))
source = (ROOT/'LeanOS/QotomMadtStream.lean').read_text()
source += """
def finishReference (edx : UInt32) (available : Bool) (apicBase : UInt64)
    (sample : UInt32) : List UInt64 :=
  let topology : LeanOS.QotomBspTopology.Witness :=
    ⟨LeanOS.QotomBspTopology.baseline, rfl⟩
  match LeanOS.QotomBspTopology.bindBootstrap topology ⟨edx, available, apicBase, sample⟩ with
  | .ok _ => [1,1,0,4,apicBase,0]
  | .error reason =>
    let code : UInt64 := match reason with
      | .unavailable => 1
      | .missingFeatures => 2
      | .executingIdMismatch => 3
      | .notBootstrapProcessor => 4
      | .unsupportedApicState => 5
    [1,5,code,0,0,0]
"""
reference_expected = []
for _, args, _ in cases:
    query = 'LeanOS.QotomMadtStream.finishQuery ' + ' '.join(map(str,args))
    source += f'#eval (List.range 6).map (fun w => {query} (UInt64.ofNat w))\n'
# Only well-formed terminal states and representable typed inputs enter the
# typed policy; malformed scalar cases retain their separate ABI expectations.
for _, args, words in cases:
    if args[:16] == base[:16] and args[16] < 2**32 and args[17] < 2 and args[19] < 2**32:
        edx, available, apic_base, sample = args[16:]
        source += f'#eval finishReference {edx} {str(bool(available)).lower()} {apic_base} {sample}\n'
        reference_expected.append(str(words))
with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp)/'Finish.lean'; path.write_text(source)
    run = subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,text=True,capture_output=True)
    expected = [str(words) for _,_,words in cases] + reference_expected
    if run.returncode or run.stdout.splitlines() != expected:
        raise SystemExit(run.stdout + run.stderr)
print(f'PASS {len(cases)} terminal/BSP scalar cases; {len(reference_expected)} typed-policy comparisons')
header = 'static const struct { const char *name; uint64_t args[20], words[6]; } finish_cases[] = {\n'
for label, args, words in cases:
    header += '{"'+label+'",{'+','.join(str(x)+'ULL' for x in args)+'},{'+','.join(str(x)+'ULL' for x in words)+'}},\n'
header += '};\n'
out = ROOT/'build/qotom-madt-stream'
out.mkdir(parents=True,exist_ok=True)
(out/'finish-cases.h').write_text(header)
