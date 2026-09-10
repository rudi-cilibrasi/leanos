#!/usr/bin/env python3
"""Check the isolated reload prototype's linked instructions and rejection mutations."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def check(elf):
    output = subprocess.check_output(
        ['objdump', '-d', '--no-show-raw-insn', str(elf)], text=True)
    if 'file format elf64-x86-64' not in output:
        raise ValueError('expected x86-64 ELF')
    symbols, instructions = {}, []
    for line in output.splitlines():
        symbol = re.fullmatch(r'([0-9a-f]+) <([^>]+)>:', line)
        if symbol:
            symbols[symbol[2]] = int(symbol[1], 16)
        instruction = re.fullmatch(r'\s*([0-9a-f]+):\s+([a-z0-9]+)\s*(.*?)\s*', line)
        if instruction:
            instructions.append((int(instruction[1], 16), instruction[2], instruction[3]))
        elif re.match(r"\s*[0-9a-f]+:", line):
            raise ValueError("undecodable instruction bytes")
    if set(symbols) != {'leanos_copy_root_reload', 'leanos_copy_root_terminal'}:
        raise ValueError('unexpected or missing code symbols')
    terminal = symbols['leanos_copy_root_terminal']
    normalized = []
    for address, mnemonic, operands in instructions:
        if mnemonic in {'jne', 'je', 'jae', 'jmp'}:
            target = re.fullmatch(r'([0-9a-f]+) <[^>]+>', operands)
            if not target:
                raise ValueError('unresolved branch')
            target_address = int(target[1], 16)
            if mnemonic == 'jmp':
                if target_address != terminal + 1:
                    raise ValueError('terminal loop must target HLT')
                operands = 'halt'
            else:
                if target_address != terminal:
                    raise ValueError('all guards must target terminal')
                operands = 'terminal'
        normalized.append((mnemonic, operands))
    expected = [
        ('pushf', ''), ('pop', '%rdx'), ('test', '$0x200,%edx'), ('jne', 'terminal'),
        ('mov', '%cr4,%rcx'), ('test', '$0x20080,%ecx'), ('jne', 'terminal'),
        ('test', '%rdi,%rdi'), ('je', 'terminal'),
        ('test', '$0xfff,%edi'), ('jne', 'terminal'),
        ('cmp', '$0x1000000,%rdi'), ('jae', 'terminal'),
        ('mov', '%rdi,%cr3'), ('mov', '%cr3,%rax'), ('cmp', '%rdi,%rax'),
        ('jne', 'terminal'), ('mov', '$0x1,%eax'), ('ret', ''),
        ('cli', ''), ('hlt', ''), ('jmp', 'halt')]
    if normalized != expected:
        raise ValueError('reload instruction contract differs')
    if instructions[0][0] != symbols['leanos_copy_root_reload'] or instructions[19][0] != terminal:
        raise ValueError('entry/terminal boundaries differ')
    if subprocess.check_output(['nm', '-u', str(elf)], text=True).strip():
        raise ValueError('unexpected external dependencies')


def self_test():
    source = (ROOT / 'experiments/copy-roots/reload.S').read_text()
    mutations = {
        'missing-reload': ('    mov %rdi, %cr3', '    nop'),
        'missing-pcid-guard': ('$0x20080', '$0x80'),
        'missing-pge-guard': ('$0x20080', '$0x20000'),
        'missing-if-guard': ('$0x200, %edx', '$0, %edx'),
        'missing-alignment': ('$0xfff', '$0'),
        'wrong-arena-bound': ('$0x1000000', '$0x2000000'),
        'early-return': ('    mov %rdi, %cr3', '    ret\n    mov %rdi, %cr3'),
        'missing-readback': ('    mov %cr3, %rax', '    mov %rdi, %rax'),
        'unsupported-stac': ('    mov %rdi, %cr3', '    stac\n    mov %rdi, %cr3'),
        'terminal-return': ('1:  hlt', '1:  ret'),
        'undecodable-tail': ('    jmp 1b', '    jmp 1b\n    .byte 0x0f'),
    }
    with tempfile.TemporaryDirectory(prefix='leanos-copy-root-') as directory:
        path = Path(directory)

        def build(name, text):
            asm, obj, elf = (path / (name + suffix) for suffix in ('.S', '.o', '.elf'))
            asm.write_text(text)
            subprocess.run([os.environ.get('LEANOS_CC', 'gcc'), '-m64', '-c', str(asm), '-o', str(obj)], check=True)
            subprocess.run(['ld', '-nostdlib', '--build-id=none', '-e', 'leanos_copy_root_reload',
                            '-Ttext', '0x100000', '-o', str(elf), str(obj)], check=True)
            return elf

        check(build('baseline', source))
        for name, (old, new) in mutations.items():
            if source.count(old) != 1:
                raise ValueError(f'mutation no longer applies uniquely: {name}')
            elf = build(name, source.replace(old, new))
            try:
                check(elf)
            except ValueError:
                continue
            raise ValueError(f'unsafe mutation accepted: {name}')
    print(f'copy-root reload: linked baseline PASS; {len(mutations)} mutations rejected')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf', nargs='?', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.elf:
        check(args.elf)
        print('copy-root reload instruction contract PASS')
    else:
        parser.error('provide an ELF or --self-test')
