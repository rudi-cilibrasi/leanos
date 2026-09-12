#!/usr/bin/env python3
import hashlib
import json
import runpy
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
T=runpy.run_path(str(Path(__file__).with_name('test-qotom-txe-bme-capture.py')))
D=runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-final-capture.py')))
R=runpy.run_path(str(Path(__file__).with_name('run-qotom-recovery-lab.py')))
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
trust_record=(b'LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=0 index=16 count=16 '
    b'commands-accepted=1 assumption-mask=31 admitted=1 '
    b'contract=qotom-j1900-pci-trust-v1 contract-accepted=1 commands='+COMMANDS+
    b' vtd=not-applicable platform-admitted=1\n')
trust_terminal=FINAL.replace(b'qotom-platform-pending',b'qotom-nosmap-pending')
trust_raw=STATE.replace(FINAL,trust_record+trust_terminal)
trust_projection,trust=D['extract'](trust_raw,P,trust_contract=True)
assert trust_projection==STATE
assert trust['platform_admitted'] and trust['trust_contract_accepted']
assert trust['dma_quarantine_admitted_under_contract']
assert trust['posted_writes_drained_assumed'] and not trust['posted_writes_drained']
assert trust['txe_private_dma_quiescent_assumed'] and not trust['txe_private_dma_quiescent']
assert trust['firmware_and_smm_noninterference_assumed']
for bad,mode in ((trust_raw,False),(raw,True)):
    try:D['extract'](bad,P,trust_contract=mode)
    except ValueError:pass
    else:raise AssertionError('accepted PCI final capture under wrong policy mode')
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
trust_mutations=(trust_raw.replace(b'contract-accepted=1',b'contract-accepted=0',1),
    trust_raw.replace(b'assumption-mask=31',b'assumption-mask=3',1),
    trust_raw.replace(b'qotom-j1900-pci-trust-v1',b'qotom-j1900-pci-trust-v2',1),
    trust_raw.replace(b'qotom-nosmap-pending',b'qotom-pci-assumptions',1))
for number,bad in enumerate(trust_mutations):
    try:D['extract'](bad,P,trust_contract=True)
    except ValueError:pass
    else:raise AssertionError(f'accepted mutated PCI trust-contract capture {number}')
evidence=ROOT/'hardware/lab/observations/qotom-native-pci-final-20260912'
if evidence.exists():
    physical_protocol=R['cpu_replay_module'](True).load_protocol(
        evidence/'diagnostic-protocol.tsv')
    serial=(evidence/'cycle-1/serial.raw').read_bytes()
    start=serial.index(physical_protocol['BOOT'].encode()+b' target=qotom-j1900-candidate')
    physical_terminal=(physical_protocol['FINAL'].encode()+
        b' status=FAIL reason=qotom-pci-assumptions\n')
    end=serial.index(physical_terminal,start)+len(physical_terminal)
    _,retained=D['extract'](serial[start:end],physical_protocol)
    assert retained==json.loads((evidence/'cycle-1/pci-final.json').read_text())
    manifest=json.loads((evidence/'manifest.json').read_text())
    assert manifest['raw_serial_sha256']==hashlib.sha256(
        (evidence/'cycle-1/serial.raw').read_bytes()).hexdigest()
    for name,digest in manifest['files'].items():
        assert hashlib.sha256((evidence/name).read_bytes()).hexdigest()==digest,name
trust_evidence=ROOT/'hardware/lab/observations/qotom-native-pci-trust-20260912'
if trust_evidence.exists():
    physical_protocol=R['cpu_replay_module'](True).load_protocol(
        trust_evidence/'diagnostic-protocol.tsv')
    serial=(trust_evidence/'cycle-1/serial.raw').read_bytes()
    start=serial.index(physical_protocol['BOOT'].encode()+b' target=qotom-j1900-candidate')
    physical_terminal=(physical_protocol['FINAL'].encode()+
        b' status=FAIL reason=qotom-nosmap-pending\n')
    end=serial.index(physical_terminal,start)+len(physical_terminal)
    _,retained=D['extract'](serial[start:end],physical_protocol,trust_contract=True)
    assert retained==json.loads((trust_evidence/'cycle-1/pci-final.json').read_text())
    manifest=json.loads((trust_evidence/'manifest.json').read_text())
    assert manifest['trust_contract']=='qotom-j1900-pci-trust-v1'
    assert manifest['raw_serial_sha256']==hashlib.sha256(
        (trust_evidence/'cycle-1/serial.raw').read_bytes()).hexdigest()
    for name,digest in manifest['files'].items():
        assert hashlib.sha256((trust_evidence/name).read_bytes()).hexdigest()==digest,name
print('PASS Qotom PCI final decoder: exact rescan, rejection and named trust contract')
