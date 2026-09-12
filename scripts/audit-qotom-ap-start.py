#!/usr/bin/env python3
"""Audit the Qotom BSP image mechanisms that exclude a LeanOS AP start."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import struct
import subprocess

LOCAL_APIC_PAGE = 0xFEE00000
PTE_ADDRESS = 0x000FFFFFFFFFF000
PLAN_WORDS = 4096


def sections(raw):
    if raw[:7] != b'\x7fELF\x02\x01\x01' or len(raw) < 64:
        raise ValueError('requires little-endian ELF64')
    if struct.unpack_from('<HH',raw,16) != (2,62):
        raise ValueError('requires linked x86-64 executable')
    offset = struct.unpack_from('<Q',raw,40)[0]
    size,count = struct.unpack_from('<HH',raw,58)
    if size != 64 or not 1 <= count <= 4096 or offset + size*count > len(raw):
        raise ValueError('invalid or extended section table')
    result = []
    for index in range(count):
        _,kind,flags,address,start,length,_,_,_,_ = struct.unpack_from(
            '<IIQQQQIIQQ',raw,offset+index*size)
        if flags & 2 and kind != 8:
            if start + length > len(raw): raise ValueError('invalid section extent')
            result.append((address,start,length,flags))
    return result


def symbols(path):
    result = {}
    output = subprocess.check_output(
        ['nm','-S','--defined-only',str(path)],text=True)
    for line in output.splitlines():
        fields = line.split()
        if len(fields) == 4:
            address,size,kind,name = fields
        elif len(fields) == 3:
            address,kind,name = fields
            size = '0'
        else:
            continue
        if name in result: raise ValueError('ambiguous symbol: ' + name)
        result[name] = (int(address,16),int(size,16),kind)
    return result


def symbol_location(path, name, expected_size):
    raw = Path(path).read_bytes()
    table = symbols(path)
    if name not in table: raise ValueError('missing symbol: ' + name)
    address,size,_ = table[name]
    if size != expected_size: raise ValueError('wrong symbol size: ' + name)
    matches = [(start + address-base,size) for base,start,length,_ in sections(raw)
               if base <= address and address+size <= base+length]
    if len(matches) != 1: raise ValueError('symbol is not in one backed section: ' + name)
    return matches[0]


def audit(path):
    path = Path(path)
    raw = path.read_bytes()
    table = symbols(path)
    required = {'kernel_main','leanos_qotom_machine_topology_admission_result_query'}
    if not required <= table.keys():
        raise ValueError('not a linked Qotom BSP production image')
    marker = (b'LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 '
              b'memory=published topology=published interrupts=masked '
              b'nmi-routing=quarantined platform-admitted=0')
    if raw.count(marker) != 1 or raw.count(b'qotom-platform-pending') != 1:
        raise ValueError('Qotom BSP terminal contract is absent or ambiguous')
    plans = {}
    aliases = []
    for name in ('leanos_boot_plan_a','leanos_boot_plan_b'):
        offset,size = symbol_location(path,name,PLAN_WORDS*8)
        data = raw[offset:offset+size]
        words = struct.unpack('<4096Q',data)
        mapped = [index for index,value in enumerate(words)
                  if value & 1 and value & PTE_ADDRESS == LOCAL_APIC_PAGE]
        aliases.extend((name,index) for index in mapped)
        plans[name] = {'sha256':hashlib.sha256(data).hexdigest(),
                       'present_entries':sum(bool(value & 1) for value in words),
                       'local_apic_aliases':mapped}
    if aliases:
        raise ValueError('generated CPU page plan maps the local APIC page')
    spec = importlib.util.spec_from_file_location(
        'qotom_msr_audit',Path(__file__).with_name('audit-qotom-msr-writes.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    msr = module.audit(path)
    forbidden = re.compile(r'(^|_)(ap_start|startup_ap|secondary_cpu|sipi|ap_trampoline)(_|$)',re.I)
    names = sorted(name for name in table if forbidden.search(name))
    if names: raise ValueError('AP-start symbol retained: ' + ','.join(names))
    return {
        'schema':'leanos-qotom-ap-start-exclusion-v1',
        'elf_sha256':hashlib.sha256(raw).hexdigest(),
        'local_apic_page':LOCAL_APIC_PAGE,
        'plans':plans,
        'wrmsr_sites':len(msr['sites']),
        'wrmsr_selectors':[site['selector_on_normal_entry'] for site in msr['sites']],
        'x2apic_icr_msr_write':False,
        'ap_start_symbol':False,
        'leanos_ap_start_path_excluded':True,
        'firmware_ap_dormancy_assumed':True,
        'ap_dormancy_established':False,
        'platform_admitted':False,
    }


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf',type=Path)
    args=parser.parse_args()
    print(json.dumps(audit(args.elf),indent=2))
