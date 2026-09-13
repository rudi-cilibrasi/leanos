#!/usr/bin/env python3
"""Validate the Qotom no-SMAP live-control transition checkpoint."""
import re

PREFIX=b'LEANOS-LAB/1 NO-SMAP-CONTROL '
DEC=rb'(0|[1-9][0-9]{0,19})'

def extract(raw,protocol):
    if len(raw)>131072 or not raw.endswith(b'\n'):
        raise ValueError('no-SMAP control capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    terminal=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-copy-roots-pending\n'
    prior=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-nosmap-pending\n'
    if positions!=[len(lines)-2] or lines[-1]!=terminal:
        raise ValueError('no-SMAP control record order or terminal')
    pattern=(PREFIX+rb'profile=qotom-copy-roots-v1 status='+DEC+
        rb' cr0='+DEC+rb' cr4-before='+DEC+rb' cr4-after='+DEC+
        rb' efer='+DEC+rb' rflags='+DEC+rb' error-mask='+DEC+
        rb' strategy=qotom-copy-roots-v1 max-bytes='+DEC+
        rb' max-aliases='+DEC+rb' reload=mandatory cpl3-authority='+DEC+
        rb' closed-root-published='+DEC+rb' copy-root-published='+DEC+rb'\n')
    match=re.fullmatch(pattern,lines[-2])
    if not match:
        raise ValueError('no-SMAP control framing')
    (status,cr0,before,after,efer,rflags,errors,max_bytes,max_aliases,
     cpl3,closed,copy)=map(int,match.groups())
    if any(word>0xffffffffffffffff for word in (cr0,before,after,efer,rflags)):
        raise ValueError('no-SMAP control word width')
    if (status!=0 or errors!=0 or cr0&0x10000==0 or efer&0x800==0 or
        before&(0x200000|0x20000|0x80)!=0 or rflags&0x200!=0 or
        after!=before|0x100000 or after&0x100000==0 or
        after&(0x200000|0x20000|0x80)!=0 or
        (max_bytes,max_aliases,cpl3,closed,copy)!=(16,2,0,0,0)):
        raise ValueError('no-SMAP control result')
    metadata={'schema':'leanos-qotom-nosmap-control-v1','profile':'qotom-copy-roots-v1',
        'status':status,'cr0':cr0,'cr4_before':before,'cr4_after':after,
        'efer':efer,'rflags':rflags,'error_mask':errors,'wp':True,'nxe':True,
        'smep':True,'smap':False,'pcid':False,'pge':False,
        'interrupts_enabled':False,'max_bytes':max_bytes,
        'max_aliases':max_aliases,'reload':'mandatory','cpl3_authority':False,
        'closed_root_published':False,'copy_root_published':False,
        'terminal_reason':'qotom-copy-roots-pending'}
    return b''.join(lines[:-2])+prior,metadata
