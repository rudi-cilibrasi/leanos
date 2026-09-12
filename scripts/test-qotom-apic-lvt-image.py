#!/usr/bin/env python3
"""Check the read-only Qotom local-APIC LINT observation image and decoder."""
import importlib.util
import hashlib
import json
import runpy
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ELF = ROOT / 'build/qotom-bsp-lvt-lab/leanos-qotom-lab.elf'
spec = importlib.util.spec_from_file_location(
    'qotom_ap_start_audit', ROOT / 'scripts/audit-qotom-ap-start.py')
audit_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit_module)
audit = audit_module.audit(ELF)
assert audit['leanos_ap_start_path_excluded']
assert not audit['x2apic_icr_msr_write']
assert all(not plan['local_apic_aliases'] for plan in audit['plans'].values())

symbols = subprocess.check_output(['nm','-n',str(ELF)], text=True)
for name in ('lab_observe_qotom_apic_lvt','lab_qotom_lvt_native_load32',
             'lab_qotom_lvt_native_invalidate'):
    assert name in symbols
load_disassembly = subprocess.check_output([
    'objdump','-d','--no-show-raw-insn',
    '--disassemble=lab_qotom_lvt_native_load32',str(ELF)], text=True)
assert load_disassembly.count('mov    (%rsi),%eax') == 1
assert 'mov    %eax,(%rsi)' not in load_disassembly
invalidate_disassembly = subprocess.check_output([
    'objdump','-d','--no-show-raw-insn',
    '--disassemble=lab_qotom_lvt_native_invalidate',str(ELF)], text=True)
assert invalidate_disassembly.count('invlpg (%rsi)') == 1
observer_disassembly = subprocess.check_output([
    'objdump','-d','--no-show-raw-insn',
    '--disassemble=lab_observe_qotom_apic_lvt',str(ELF)], text=True)
assert observer_disassembly.count('<lab_qotom_lvt_native_load32>') == 4
assert observer_disassembly.count('<lab_qotom_lvt_native_invalidate>') == 2
assert '$0xfee00000' in observer_disassembly and '$0xfee00900' in observer_disassembly

runner = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
protocol = runner['cpu_replay_module'](True).load_protocol(
    ROOT / 'build/boot/serial-protocol.tsv')
digest = audit['elf_sha256']
lvt = (b'LEANOS-LAB/1 APIC-LVT profile=qotom-lvt-v1 status=0 '
       b'apic-base=4276095232 executing=0 lint0-first=67328 lint1-first=66560 '
       b'lint0-second=67328 lint1-second=66560 stable=1 '
       b'routing-authority=0 writes=0 map-restored=1 platform-admitted=0\n')
kernel = (
    b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
    b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
    + b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD sha256=' + digest.encode() + b'\n'
    b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
    + protocol['BOOT'].encode() + b' target=x86_64-qotom schedule=bsp-production\n'
    + lvt +
    b'LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published '
    b'topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0\n'
    + protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n')
recovery = b'LEANOS-LAB/1 DEFAULT request=none\nLEANOS-LAB/1 CHAIN freebsd disk=hd1\n'
events = [{'elapsed':0,'hex':kernel.hex()},{'elapsed':35,'hex':recovery.hex()}]
result = runner['classify_bsp_production'](events,digest,lvt_observation=True)
assert result['inherited_lvt_observed'] and result['local_apic_lvt']['stable']
assert result['local_apic_lvt']['lint0_first']['raw'] == 67328
assert result['local_apic_lvt']['lint1_first']['masked']

mutations = (
    lvt.replace(b'status=0',b'status=1'),
    lvt.replace(b'apic-base=4276095232',b'apic-base=4276092928'),
    lvt.replace(b'executing=0',b'executing=2'),
    lvt.replace(b'lint0-first=67328',b'lint0-first=4294967296'),
    lvt.replace(b'stable=1',b'stable=0'),
    lvt.replace(b'routing-authority=0',b'routing-authority=1'),
    lvt.replace(b'writes=0',b'writes=1'),
    lvt.replace(b'map-restored=1',b'map-restored=0'),
    lvt.replace(b'platform-admitted=0',b'platform-admitted=1'),
    lvt.replace(b'status=0',b'status=00'),
    lvt + lvt,
)
for changed in mutations:
    altered = kernel.replace(lvt,changed)
    try:
        runner['classify_bsp_production'](
            [{'elapsed':0,'hex':altered.hex()},{'elapsed':35,'hex':recovery.hex()}],
            digest,lvt_observation=True)
    except ValueError:
        pass
    else:
        raise AssertionError('changed Qotom LVT observation was accepted')
try:
    runner['classify_bsp_production'](events,digest)
except ValueError:
    pass
else:
    raise AssertionError('unexpected LVT record was accepted by production-only decoder')

capture = ROOT / 'hardware/lab/observations/qotom-apic-lvt-20260912'
manifest = json.loads((capture/'manifest.json').read_text())
for name,expected_digest in manifest['files'].items():
    assert hashlib.sha256((capture/name).read_bytes()).hexdigest() == expected_digest,name
physical_events = [json.loads(line) for line in
                   (capture/'cycle-1/events.jsonl').read_text().splitlines()]
assert b''.join(bytes.fromhex(event['hex']) for event in physical_events) == \
       (capture/'cycle-1/serial.raw').read_bytes()
saved = json.loads((capture/'cycle-1/result.json').read_text())
physical = runner['classify_bsp_production'](
    physical_events,manifest['elf_sha256'],lvt_observation=True)
for key,value in physical.items():
    assert saved[key] == value,key
observed = saved['local_apic_lvt']
assert saved['inherited_lvt_observed'] and observed['stable']
assert observed['lint0_first'] == observed['lint0_second']
assert observed['lint1_first'] == observed['lint1_second']
for sample in (observed['lint0_first'],observed['lint1_first']):
    assert sample == {'raw':65536,'vector':0,'delivery_mode':0,
                      'delivery_status':0,'polarity':0,'remote_irr':0,
                      'trigger_mode':0,'masked':True}
assert not observed['routing_authority'] and observed['write_count'] == 0
assert observed['mapping_restored'] and not observed['platform_admitted']
assert saved['request_consumed'] and saved['recovery'] == 'freebsd-ssh-restored'
assert saved['freebsd_boot_after'] > saved['freebsd_boot_before']
print('PASS Qotom inherited APIC LVT read-only image and decoder negatives')
