#!/usr/bin/env python3
"""Audit the linked Qotom no-SMAP checkpoint's complete instruction body."""
import json
import re
import subprocess
import sys

SYMBOL='lab_capture_nosmap_control'

CALLEE_SAVED={'rbx','rbp','r12','r13','r14','r15'}

def register(value):
    match=re.fullmatch(r'%((?:r(?:[abcd]x|[sb]p|[sd]i|[89]|1[0-5]))|(?:e[abcd]x))',value)
    if not match:return None
    name=match.group(1)
    aliases={'eax':'rax','ebx':'rbx','ecx':'rcx','edx':'rdx'}
    return aliases.get(name,name)

def operands(args):
    return [value.strip() for value in args.split(',')]

def writes_register(op,args,wanted):
    values=operands(args)
    if not values:return False
    # AT&T syntax puts the destination last. These are the only operations
    # admitted in the provenance slice between the CR4 snapshot and its copy.
    writers={'mov','movabs','lea','pop','add','sub','or','xor','and','bts','btc','btr',
             'shl','shr','sar','inc','dec','not','neg'}
    return op in writers and register(values[-1])==wanted

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
    writes=[i for i,(op,args) in enumerate(body)
            if op=='mov' and len(operands(args))==2 and operands(args)[1]=='%cr4']
    if forbidden:raise ValueError('unsupported no-SMAP instruction')
    if smap:raise ValueError('SMAP-setting instruction in no-SMAP checkpoint')
    if len(writes)!=1:raise ValueError('no-SMAP checkpoint must contain one CR4 write')
    write=writes[0]
    if write<2:raise ValueError('CR4 write lacks exact SMEP provenance')
    write_values=operands(body[write][1])
    destination=register(write_values[0])
    copy_op,copy_args=body[write-2]
    smep_op,smep_args=body[write-1]
    copy_values=operands(copy_args)
    if (destination is None or copy_op!='mov' or len(copy_values)!=2 or
            register(copy_values[1])!=destination or smep_op!='or' or
            operands(smep_args)!=['$0x100000','%'+destination]):
        raise ValueError('CR4 write lacks exact SMEP provenance')
    source=register(copy_values[0])
    if source not in CALLEE_SAVED:
        raise ValueError('CR4 snapshot is not held in a callee-saved register')
    reads=[i for i,(op,args) in enumerate(body[:write-2])
           if op=='mov' and operands(args)==['%cr4','%'+source]]
    if len(reads)!=1 or any(writes_register(op,args,source)
                            for op,args in body[reads[0]+1:write-2]):
        raise ValueError('CR4 snapshot provenance changed before write')
    return {'schema':'leanos-qotom-nosmap-control-audit-v1','symbol':SYMBOL,
            'instruction_count':len(body),'cr4_writes':len(writes),
            'smep_masks':1,'stac_clac':len(forbidden),
            'cr4_write_provenance':'snapshot-or-smep-only',
            'smap_set_instructions':len(smap)}

def selftest():
    good=('  1: 0f 20 e5 mov %cr4,%rbp\n'
          '  4: 48 89 e8 mov %rbp,%rax\n'
          '  7: 48 0d 00 00 10 00 or $0x100000,%rax\n'
          '  d: 0f 22 e0 mov %rax,%cr4\n')
    audit(good)
    for bad in (good+'  a: 0f 01 cb stac\n',good+'  a: 48 0d 00 00 20 00 or $0x200000,%rax\n',
                good+'  a: 48 0f ba e8 15 bts $0x15,%rax\n',
                good.replace('$0x100000','$0x200000'),
                good+'  a: 0f 22 e1 mov %rcx,%cr4\n',
                good.replace('  7: 48 0d 00 00 10 00 or $0x100000,%rax\n',
                    '  5: b9 00 00 20 00 mov $0x200000,%ecx\n'
                    '  6: 48 09 c8 or %rcx,%rax\n'
                    '  7: 48 0d 00 00 10 00 or $0x100000,%rax\n'),
                good.replace('  4: 48 89 e8 mov %rbp,%rax\n',
                    '  2: 48 81 cd 00 00 20 00 or $0x200000,%rbp\n'
                    '  4: 48 89 e8 mov %rbp,%rax\n')):
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
