#!/usr/bin/env python3
"""Check the proved Qotom inherited-masked LVT policy image and decoder."""
import importlib.util
import hashlib
import json
import runpy
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ELF = ROOT / 'build/qotom-bsp-lvt-policy-lab/leanos-qotom-lab.elf'
spec = importlib.util.spec_from_file_location(
    'qotom_ap_start_audit', ROOT / 'scripts/audit-qotom-ap-start.py')
audit_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit_module)
audit = audit_module.audit(ELF)
assert audit['leanos_ap_start_path_excluded']
assert not audit['x2apic_icr_msr_write']
assert all(not plan['local_apic_aliases'] for plan in audit['plans'].values())

symbols = subprocess.check_output(['nm','-n',str(ELF)], text=True)
for name in ('lab_enforce_qotom_apic_lvt','lab_sample_qotom_apic_lvt',
             'lab_qotom_lvt_native_load32','lab_qotom_lvt_native_invalidate',
             'leanos_qotom_inherited_lvt_policy_query'):
    assert name in symbols
load = subprocess.check_output([
    'objdump','-d','--no-show-raw-insn',
    '--disassemble=lab_qotom_lvt_native_load32',str(ELF)], text=True)
assert load.count('mov    (%rsi),%eax') == 1
assert 'mov    %eax,(%rsi)' not in load
sample = subprocess.check_output([
    'objdump','-d','--no-show-raw-insn',
    '--disassemble=lab_sample_qotom_apic_lvt',str(ELF)], text=True)
assert sample.count('<lab_qotom_lvt_native_load32>') == 4
assert sample.count('<lab_qotom_lvt_native_invalidate>') == 2
enforce = subprocess.check_output([
    'objdump','-d','--no-show-raw-insn',
    '--disassemble=lab_enforce_qotom_apic_lvt',str(ELF)], text=True)
assert enforce.count('<leanos_qotom_inherited_lvt_policy_query>') == 1

runner = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
protocol = runner['cpu_replay_module'](True).load_protocol(
    ROOT / 'build/boot/serial-protocol.tsv')
digest = audit['elf_sha256']
lvt = (b'LEANOS-LAB/1 APIC-LVT profile=qotom-lvt-v1 status=0 '
       b'apic-base=4276095232 executing=0 lint0-first=65536 lint1-first=65536 '
       b'lint0-second=65536 lint1-second=65536 stable=1 '
       b'routing-authority=0 writes=0 map-restored=1 platform-admitted=0\n')
policy = (b'LEANOS-LAB/1 APIC-LVT-POLICY profile=qotom-lvt-v1 status=0 '
          b'detail=0 lint0=65536 lint1=65536 policy=masked-inherited '
          b'routing-authority=0 writes=0 map-restored=1 platform-admitted=0\n')
kernel = (
    b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
    b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
    + b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD sha256=' + digest.encode() + b'\n'
    b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
    + protocol['BOOT'].encode() + b' target=x86_64-qotom schedule=bsp-production\n'
    + lvt + policy +
    b'LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published '
    b'topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0\n'
    + protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n')
recovery = b'LEANOS-LAB/1 DEFAULT request=none\nLEANOS-LAB/1 CHAIN freebsd disk=hd1\n'
events = [{'elapsed':0,'hex':kernel.hex()},{'elapsed':35,'hex':recovery.hex()}]
result = runner['classify_bsp_production'](events,digest,lvt_policy=True)
assert result['inherited_lvt_observed']
assert result['inherited_lvt_policy_enforced']
assert result['local_apic_lvt_policy']['policy'] == 'masked-inherited'

mutations = (
    policy.replace(b'status=0',b'status=1'),
    policy.replace(b'detail=0',b'detail=90'),
    policy.replace(b'lint0=65536',b'lint0=65537'),
    policy.replace(b'lint1=65536',b'lint1=65537'),
    policy.replace(b'policy=masked-inherited',b'policy=rejected'),
    policy.replace(b'routing-authority=0',b'routing-authority=1'),
    policy.replace(b'writes=0',b'writes=1'),
    policy.replace(b'map-restored=1',b'map-restored=0'),
    policy.replace(b'platform-admitted=0',b'platform-admitted=1'),
    policy.replace(b'status=0',b'status=00'),
    policy + policy,
)
for changed in mutations:
    altered = kernel.replace(policy,changed)
    try:
        runner['classify_bsp_production'](
            [{'elapsed':0,'hex':altered.hex()},{'elapsed':35,'hex':recovery.hex()}],
            digest,lvt_policy=True)
    except ValueError:
        pass
    else:
        raise AssertionError('changed Qotom LVT policy was accepted')
try:
    runner['classify_bsp_production'](events,digest,lvt_observation=True)
except ValueError:
    pass
else:
    raise AssertionError('policy record accepted as observation-only capture')

capture = ROOT / 'hardware/lab/observations/qotom-apic-lvt-policy-20260912'
manifest = json.loads((capture/'manifest.json').read_text())
for name,expected_digest in manifest['files'].items():
    assert hashlib.sha256((capture/name).read_bytes()).hexdigest() == expected_digest,name
physical_events = [json.loads(line) for line in
                   (capture/'cycle-1/events.jsonl').read_text().splitlines()]
assert b''.join(bytes.fromhex(event['hex']) for event in physical_events) == \
       (capture/'cycle-1/serial.raw').read_bytes()
saved = json.loads((capture/'cycle-1/result.json').read_text())
physical = runner['classify_bsp_production'](
    physical_events,manifest['elf_sha256'],lvt_policy=True)
for key,value in physical.items():
    assert saved[key] == value,key
assert saved['inherited_lvt_policy_enforced']
assert saved['local_apic_lvt_policy']['policy'] == 'masked-inherited'
assert saved['local_apic_lvt_policy']['lint0_raw'] == 65536
assert saved['local_apic_lvt_policy']['lint1_raw'] == 65536
assert saved['request_consumed'] and saved['recovery'] == 'freebsd-ssh-restored'
assert saved['freebsd_boot_after'] > saved['freebsd_boot_before']
print('PASS Qotom inherited-masked APIC LVT policy image and decoder negatives')
