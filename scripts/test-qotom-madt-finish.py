#!/usr/bin/env python3
"""Check terminal shape and BSP binding; terminal inputs here are synthetic."""
from pathlib import Path
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
source = (ROOT/'LeanOS/QotomMadtStream.lean').read_text()
for _, args, _ in cases:
    query = 'LeanOS.QotomMadtStream.finishQuery ' + ' '.join(map(str,args))
    source += f'#eval (List.range 6).map (fun w => {query} (UInt64.ofNat w))\n'
with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp)/'Finish.lean'; path.write_text(source)
    run = subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,text=True,capture_output=True)
    expected = [str(words) for _,_,words in cases]
    if run.returncode or run.stdout.splitlines() != expected:
        raise SystemExit(run.stdout + run.stderr)
print(f'PASS {len(cases)} terminal/BSP scalar cases')
