#!/usr/bin/env python3
"""Check the lab ELF's WRMSR byte sites, not whole-machine AP-start exclusion."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import subprocess

# The bootstrap normalization block has no relocations or branches. These are
# its reviewed IA32_EFER, STAR/LSTAR/CSTAR/SFMASK and SYSENTER selectors.
SELECTORS = (0xc0000080,0xc0000081,0xc0000082,0xc0000083,0xc0000084,0x174,0x175,0x176)
BLOCK = bytes.fromhex('b9800000c00f3283e0fe0d000900000f3031c031d2') + b''.join(
    b'\xb9'+struct.pack('<I',msr)+b'\x0f\x30' for msr in SELECTORS[1:])


def audit(path):
    raw = Path(path).read_bytes()
    if raw[:7] != b'\x7fELF\x02\x01\x01' or len(raw) < 64:
        raise ValueError('requires little-endian ELF64')
    if struct.unpack_from('<HH',raw,16) != (2,62):
        raise ValueError('requires linked x86-64 executable')
    offset = struct.unpack_from('<Q',raw,40)[0]
    size,count = struct.unpack_from('<HH',raw,58)
    if size != 64 or not 1 <= count <= 4096 or offset + size*count > len(raw):
        raise ValueError('invalid or extended section table')
    sections = []
    sites = []
    for index in range(count):
        _,kind,flags,address,start,length,_,_,_,_ = struct.unpack_from('<IIQQQQIIQQ',raw,offset+index*size)
        if not flags & 4: continue
        if kind != 1 or flags & 3 != 2 or start+length > len(raw):
            raise ValueError('executable section must be backed, allocated and nonwritable')
        data = raw[start:start+length]
        sections.append((address,data))
        # Conservative raw-pair scan also catches possible unaligned WRMSR
        # encodings; it does not depend on objdump's mode or instruction starts.
        sites.extend(address+i for i in range(len(data)-1) if data[i:i+2] == b'\x0f\x30')
    symbols = {}
    for line in subprocess.check_output(['nm','--defined-only',str(path)],text=True).splitlines():
        parts = line.split()
        if len(parts) == 3:
            if parts[2] in symbols: raise ValueError('ambiguous symbol')
            symbols[parts[2]] = int(parts[0],16)
    begin = symbols['normalize_fast_entry_msrs']
    end = symbols['normalize_extended_state_cr0']
    candidates = [data[begin-address:end-address] for address,data in sections
                  if address <= begin < end <= address+len(data)]
    if candidates != [BLOCK]:
        raise ValueError('normalization block differs from reviewed bytes')
    expected = [begin+i for i in range(len(BLOCK)-1) if BLOCK[i:i+2] == b'\x0f\x30']
    if sorted(sites) != expected:
        raise ValueError('WRMSR sites outside the reviewed normalization block')
    return {'schema':'leanos-qotom-msr-write-sites-v1',
            'elf_sha256':hashlib.sha256(raw).hexdigest(),
            'normalization_address':begin,'normalization_length':len(BLOCK),
            'executable_sections':len(sections),
            'sites':[{'address':a,'selector_on_normal_entry':msr} for a,msr in zip(expected,SELECTORS)],
            'control_flow_integrity_established':False,
            'mmio_write_exclusion_established':False,
            'ap_dormancy_established':False,'platform_admitted':False}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf',type=Path)
    args=parser.parse_args()
    print(json.dumps(audit(args.elf),indent=2))
