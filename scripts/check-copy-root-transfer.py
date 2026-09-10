#!/usr/bin/env python3
"""Audit the linked transfer/reload/terminal helpers, not production entries."""
import argparse
import importlib.util
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def check(elf):
    spec = importlib.util.spec_from_file_location('reload_audit', ROOT / 'scripts/check-copy-root-reload.py')
    reload_audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reload_audit)
    reload_audit.check(elf, within_bundle=True)
    symbols = {}
    for line in subprocess.check_output(['nm', '-S', str(elf)], text=True).splitlines():
        f = line.split()
        if len(f) in (3, 4):
            symbols[f[-1]] = (int(f[0], 16), int(f[1], 16) if len(f) == 4 else 0)
    start, size = symbols['leanos_copy_root_transfer']
    if not size:
        raise ValueError('transfer has no sized body')
    output = subprocess.check_output(['objdump', '-d', '--no-show-raw-insn',
        f'--start-address={start}', f'--stop-address={start+size}', str(elf)], text=True)
    rows = []
    for line in output.splitlines():
        m = re.fullmatch(r'\s*([0-9a-f]+):\s+([a-z0-9]+)\s*(.*?)\s*', line)
        if m:
            rows.append((int(m[1], 16), m[2], m[3]))
        elif re.match(r'\s*[0-9a-f]+:', line):
            raise ValueError('undecodable transfer instruction')
    expected = [
        ('push', '%rbx'), ('push', '%r12'), ('push', '%r13'), ('push', '%r14'), ('push', '%r15'),
        ('mov', '%rdi,%r12'), ('mov', '%rsi,%r13'), ('mov', '%rdx,%r14'), ('mov', '%rcx,%r15'),
        ('call', 'reload'), ('cmp', '$0x10,%r15'), ('ja', 'terminal'),
        ('xor', '%ebx,%ebx'), ('test', '%r15,%r15'), ('je', 'return'),
        ('mov', '%r13,%rdi'), ('call', 'reload'),
        ('mov', '(%r14),%r10'), ('mov', '0x8(%r14),%r11'),
        ('mov', '(%r10),%al'), ('mov', '%al,(%r11)'), ('inc', '%rbx'),
        ('add', '$0x10,%r14'), ('cmp', '%r15,%rbx'), ('jb', 'byte'),
        ('mov', '%r12,%rdi'), ('call', 'reload'), ('mov', '%rbx,%rax'),
        ('pop', '%r15'), ('pop', '%r14'), ('pop', '%r13'), ('pop', '%r12'), ('pop', '%rbx'), ('ret', '')]
    if len(rows) != len(expected):
        raise ValueError('transfer instruction count differs')
    targets = {symbols['leanos_copy_root_reload'][0]: 'reload',
               symbols['leanos_copy_root_terminal'][0]: 'terminal',
               rows[27][0]: 'return', rows[17][0]: 'byte'}
    normalized = []
    for address, mnemonic, operands in rows:
        if mnemonic in ('call', 'ja', 'je', 'jb'):
            target = re.fullmatch(r'([0-9a-f]+) <[^>]+>', operands)
            if not target or int(target[1], 16) not in targets:
                raise ValueError('unexpected transfer branch target')
            operands = targets[int(target[1], 16)]
        normalized.append((mnemonic, operands))
    if normalized != expected or rows[0][0] != start:
        raise ValueError('transfer instruction contract differs')
    if symbols['leanos_copy_transfer_load'][0] != rows[19][0] or symbols['leanos_copy_transfer_store'][0] != rows[20][0]:
        raise ValueError('transfer fault checkpoints differ')


def self_test():
    source = (ROOT / 'experiments/copy-roots/transfer.S').read_text()
    mutations = {
        'missing-cleanup-reload': ('    mov %r12, %rdi\n    call leanos_copy_root_reload', '    mov %r12, %rdi\n    nop'),
        'missing-copy-reload': ('    mov %r13, %rdi\n    call leanos_copy_root_reload', '    mov %r13, %rdi\n    nop'),
        'length-bound': ('$16, %r15', '$17, %r15'),
        'signed-bound': ('    ja leanos_copy_root_terminal', '    jg leanos_copy_root_terminal'),
        'cleanup-operand': ('    mov %r12, %rdi', '    mov %r13, %rdi'),
        'oversized-load': ('    movb (%r10), %al', '    movq (%r10), %rax'),
        'oversized-store': ('    movb %al, (%r11)', '    movq %rax, (%r11)'),
        'skip-byte': ('    add $16, %r14', '    add $32, %r14'),
        'extra-byte': ('    jb .Ltransfer_byte', '    jbe .Ltransfer_byte'),
        'zero-opens-window': ('    jz .Ltransfer_return', '    nop'),
        'unsupported-clac': ('    xor %ebx, %ebx', '    clac\n    xor %ebx, %ebx'),
        'early-return': ('    mov %r12, %rdi', '    ret\n    mov %r12, %rdi'),
    }
    with tempfile.TemporaryDirectory(prefix='leanos-transfer-audit-') as tmp:
        directory = Path(tmp)
        cc = os.environ.get('LEANOS_CC', 'gcc')
        reload_obj = directory / 'reload.o'
        subprocess.run([cc, '-m64', '-c', str(ROOT/'experiments/copy-roots/reload.S'), '-o', str(reload_obj)], check=True)
        def build(name, text):
            asm, obj, elf = [directory/(name+suffix) for suffix in ('.S','.o','.elf')]
            asm.write_text(text)
            subprocess.run([cc, '-m64', '-c', str(asm), '-o', str(obj)], check=True)
            subprocess.run(['ld','-nostdlib','--build-id=none','-e','leanos_copy_root_transfer',
                            '-Ttext','0x100000','-o',str(elf),str(obj),str(reload_obj)],check=True)
            return elf
        check(build('baseline', source))
        for name,(old,new) in mutations.items():
            if source.count(old)!=1:
                raise ValueError(f'mutation no longer unique: {name}')
            try:
                check(build(name,source.replace(old,new)))
            except ValueError:
                continue
            raise ValueError(f'unsafe mutation accepted: {name}')
    print(f'Copy transfer linked baseline passed; {len(mutations)} mutations rejected')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf',nargs='?',type=Path)
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    if args.self_test: self_test()
    elif args.elf: check(args.elf); print('Copy transfer linked instruction contract passed')
    else: parser.error('provide an ELF or --self-test')
