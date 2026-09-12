#!/usr/bin/env python3
"""Exercise the final Qotom BSP production image and AP-start audit."""
import importlib.util
from pathlib import Path
import hashlib
import json
import shutil
import struct
import tempfile
import runpy

ROOT = Path(__file__).resolve().parents[1]
ELF = ROOT / 'build/qotom-bsp-production-lab/leanos-qotom-lab.elf'
spec = importlib.util.spec_from_file_location(
    'qotom_ap_start_audit',ROOT / 'scripts/audit-qotom-ap-start.py')
audit_module = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit_module)

result = audit_module.audit(ELF)
assert result['leanos_ap_start_path_excluded']
assert not result['x2apic_icr_msr_write']
assert result['firmware_ap_dormancy_assumed'] and not result['ap_dormancy_established']
assert all(not plan['local_apic_aliases'] for plan in result['plans'].values())

lab_graph = (ROOT/'build/qotom-bsp-production-lab/objects.mk').read_text()
assert str(ROOT/'build/boot') not in lab_graph
assert str(ROOT/'build/qotom-bsp-production-lab/boot') in lab_graph

runner = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
protocol = runner['cpu_replay_module'](True).load_protocol(
    ROOT / 'build/boot/serial-protocol.tsv')
digest = result['elf_sha256']
kernel = (
    b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
    b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
    + b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD sha256=' + digest.encode() + b'\n'
    b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
    + protocol['BOOT'].encode() + b' target=x86_64-qotom schedule=bsp-production\n'
    b'LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0\n'
    + protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n')
recovery = b'LEANOS-LAB/1 DEFAULT request=none\nLEANOS-LAB/1 CHAIN freebsd disk=hd1\n'
events = [{'elapsed':0,'hex':kernel.hex()},{'elapsed':35,'hex':recovery.hex()}]
classified = runner['classify_bsp_production'](events,digest)
assert classified['memory_published'] and classified['topology_published']
assert not classified['platform_admitted'] and classified['quiet_seconds'] == 35
for changed in (
        kernel.replace(b'processor',b'processor',1) + protocol['FINAL'].encode() +
            b' status=FAIL reason=qotom-platform-pending\n',
        kernel.replace(b'topology=published',b'topology=rejected'),
        kernel.replace(digest.encode(),b'0'*64)):
    try:
        runner['classify_bsp_production'](
            [{'elapsed':0,'hex':changed.hex()},{'elapsed':35,'hex':recovery.hex()}],digest)
    except ValueError:
        pass
    else:
        raise AssertionError('changed production capture was accepted')

capture = ROOT / 'hardware/lab/observations/qotom-bsp-production-20260912'
manifest = json.loads((capture/'manifest.json').read_text())
for name,digest in manifest['files'].items():
    assert hashlib.sha256((capture/name).read_bytes()).hexdigest() == digest,name
physical_events = [json.loads(line) for line in
                   (capture/'cycle-1/events.jsonl').read_text().splitlines()]
assert b''.join(bytes.fromhex(event['hex']) for event in physical_events) == \
       (capture/'cycle-1/serial.raw').read_bytes()
saved = json.loads((capture/'cycle-1/result.json').read_text())
physical_data = b''.join(bytes.fromhex(event['hex']) for event in physical_events)
legacy_marker = (b'LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 '
                 b'memory=published topology=published interrupts=masked '
                 b'platform-admitted=0\n')
assert physical_data.count(legacy_marker) == 1
assert b'nmi-routing=quarantined' not in physical_data
assert saved['memory_published'] and saved['topology_published']
assert saved['interrupts_masked'] and not saved['platform_admitted']
assert saved['request_consumed'] and saved['recovery'] == 'freebsd-ssh-restored'
assert saved['freebsd_boot_after'] > saved['freebsd_boot_before']

capture = ROOT / 'hardware/lab/observations/qotom-madt-nmi-policy-20260912'
manifest = json.loads((capture/'manifest.json').read_text())
for name,expected_digest in manifest['files'].items():
    assert hashlib.sha256((capture/name).read_bytes()).hexdigest() == expected_digest,name
physical_events = [json.loads(line) for line in
                   (capture/'cycle-1/events.jsonl').read_text().splitlines()]
assert b''.join(bytes.fromhex(event['hex']) for event in physical_events) == \
       (capture/'cycle-1/serial.raw').read_bytes()
saved = json.loads((capture/'cycle-1/result.json').read_text())
physical = runner['classify_bsp_production'](physical_events,manifest['elf_sha256'])
for key,value in physical.items():
    assert saved[key] == value,key
assert saved['nmi_routing_quarantined']
assert saved['request_consumed'] and saved['recovery'] == 'freebsd-ssh-restored'
assert saved['freebsd_boot_after'] > saved['freebsd_boot_before']

with tempfile.TemporaryDirectory(prefix='qotom-bsp-production-negative-') as directory:
    mapped = Path(directory) / 'mapped-apic.elf'
    shutil.copy2(ELF,mapped)
    offset,_ = audit_module.symbol_location(mapped,'leanos_boot_plan_a',4096*8)
    raw = bytearray(mapped.read_bytes())
    struct.pack_into('<Q',raw,offset+4095*8,0x80000000FEE00003)
    mapped.write_bytes(raw)
    try:
        audit_module.audit(mapped)
    except ValueError as error:
        assert str(error) == 'generated CPU page plan maps the local APIC page'
    else:
        raise AssertionError('local APIC mapping mutation was accepted')

    extra_wrmsr = Path(directory) / 'extra-wrmsr.elf'
    shutil.copy2(ELF,extra_wrmsr)
    raw = bytearray(extra_wrmsr.read_bytes())
    normalization = audit_module.symbols(extra_wrmsr)['normalize_fast_entry_msrs'][0]
    executable = [(address,start,length) for address,start,length,flags
                  in audit_module.sections(raw) if flags & 4]
    changed = False
    for address,start,length in executable:
        for index in range(length-1):
            virtual = address + index
            if not normalization <= virtual < normalization + 70 and raw[start+index:start+index+2] == b'\x00\x00':
                raw[start+index:start+index+2] = b'\x0f\x30'; changed = True; break
        if changed: break
    assert changed
    extra_wrmsr.write_bytes(raw)
    try:
        audit_module.audit(extra_wrmsr)
    except ValueError as error:
        assert str(error) == 'WRMSR sites outside the reviewed normalization block'
    else:
        raise AssertionError('extra WRMSR mutation was accepted')

print('PASS Qotom BSP production ELF, local-APIC mapping and x2APIC-WRMSR negatives')
