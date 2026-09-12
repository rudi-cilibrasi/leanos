#!/usr/bin/env python3
import runpy
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
T=runpy.run_path(str(Path(__file__).with_name('test-qotom-txe-bme-capture.py')))
D=runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-final-capture.py')))
P=T['P'];FINAL=T['FINAL'];STATE=T['STATE'].replace(FINAL,T['record']()+FINAL)
COMMANDS=','.join(map(str,D['COMMANDS'])).encode()
record=(b'LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=6 index=16 count=16 '
    b'commands-accepted=1 assumption-mask=3 admitted=0 commands='+COMMANDS+
    b' vtd=not-applicable platform-admitted=0\n')
terminal=FINAL.replace(b'qotom-platform-pending',b'qotom-pci-assumptions')
raw=STATE.replace(FINAL,record+terminal)
projection,result=D['extract'](raw,P)
assert projection==STATE
assert result['fresh_complete_rescan_observed'] and not result['platform_admitted']
assert result['fixed_infrastructure_noninitiating_assumed']
assert not result['posted_writes_drained'] and not result['txe_private_dma_quiescent']
def changed(old,new):return raw.replace(record,record.replace(old,new,1),1)
mutations=(changed(b'status=6',b'status=0'),
    changed(b'index=16',b'index=15'),changed(b'count=16',b'count=15'),
    changed(b'commands-accepted=1',b'commands-accepted=0'),
    changed(b'assumption-mask=3',b'assumption-mask=31'),
    changed(b'admitted=0',b'admitted=1'),changed(b'commands=7,',b'commands=6,'),
    changed(b'vtd=not-applicable',b'vtd=present'),
    changed(b'platform-admitted=0',b'platform-admitted=1'),
    raw.replace(b'qotom-pci-assumptions',b'qotom-platform-pending',1),
    raw.replace(T['record'](),b'',1),raw.replace(record,record+record,1))
for number,bad in enumerate(mutations):
    try:D['extract'](bad,P)
    except ValueError:pass
    else:raise AssertionError(f'accepted mutated PCI final capture {number}')
print('PASS Qotom PCI final decoder: exact rescan, commands and unmet assumptions')
