#!/usr/bin/env python3
"""Audit the linked Qotom no-SMAP checkpoint's complete instruction body."""
import json
import re
import subprocess
import sys

SYMBOL='lab_capture_nosmap_control'

def audit(text):
    body=[]
    for line in text.splitlines():
        match=re.match(r'^\s*[0-9a-f]+:\s+(?:[0-9a-f]{2}\s+)+\s*(\S+)(?:\s+(.*))?$',line)
        if match:body.append((match.group(1),match.group(2) or ''))
    if not body:raise ValueError('missing no-SMAP control instructions')
    smap=[]
    for op,args in body:
        immediate=re.search(r'\$0x([0-9a-f]+)',args)
        if ((op=='bts' and ('$0x15' in args or '$21' in args)) or
                (op in {'or','xor','add'} and immediate and
                 int(immediate.group(1),16)&0x200000)):
            smap.append((op,args))
    forbidden=[(op,args) for op,args in body if op in {'stac','clac'}]
    writes=[(op,args) for op,args in body if '%cr4' in args and args.rstrip().endswith('%cr4')]
    smep=[(op,args) for op,args in body if op=='or' and '$0x100000' in args]
    if forbidden:raise ValueError('unsupported no-SMAP instruction')
    if smap:raise ValueError('SMAP-setting instruction in no-SMAP checkpoint')
    if len(writes)!=1:raise ValueError('no-SMAP checkpoint must contain one CR4 write')
    if len(smep)!=1:raise ValueError('no-SMAP checkpoint must contain one SMEP-only mask')
    return {'schema':'leanos-qotom-nosmap-control-audit-v1','symbol':SYMBOL,
            'instruction_count':len(body),'cr4_writes':len(writes),
            'smep_masks':len(smep),'stac_clac':len(forbidden),
            'smap_set_instructions':len(smap)}

def selftest():
    good='  1: 48 0d 00 00 10 00 or $0x100000,%rax\n  7: 0f 22 e0 mov %rax,%cr4\n'
    audit(good)
    for bad in (good+'  a: 0f 01 cb stac\n',good+'  a: 48 0d 00 00 20 00 or $0x200000,%rax\n',
                good+'  a: 48 0f ba e8 15 bts $0x15,%rax\n',
                good.replace('$0x100000','$0x200000'),
                good+'  a: 0f 22 e1 mov %rcx,%cr4\n'):
        try:audit(bad)
        except ValueError:continue
        raise SystemExit('audit self-test accepted a mutation')

if __name__=='__main__':
    if len(sys.argv)==2 and sys.argv[1]=='--self-test':
        selftest();print('Qotom no-SMAP control audit mutations rejected')
    elif len(sys.argv)==2:
        text=subprocess.check_output(['objdump','-d','--disassemble='+SYMBOL,sys.argv[1]],text=True)
        print(json.dumps(audit(text),sort_keys=True))
    else:
        raise SystemExit('usage: audit-qotom-nosmap-control.py ELF | --self-test')
