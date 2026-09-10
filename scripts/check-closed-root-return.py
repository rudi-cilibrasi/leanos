#!/usr/bin/env python3
"""Check the isolated return primitive's linked instructions and rejection mutations."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def check(elf, *, within_bundle=False):
    selectors = ['leanos_closed_root_return', 'leanos_closed_root_return_terminal'] if within_bundle else [None]
    output = ''.join(subprocess.check_output(
        ['objdump', '-d', '--no-show-raw-insn'] +
        ([f'--disassemble={symbol}'] if symbol else []) + [str(elf)], text=True)
        for symbol in selectors)
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
    if within_bundle:
        # The caller audits other reachable helpers separately. Retain the
        # entire declared bodies of these two callees, including any tail.
        selected = {'leanos_closed_root_return', 'leanos_closed_root_return_terminal'}
        ranges = []
        for line in subprocess.check_output(['nm', '-S', str(elf)], text=True).splitlines():
            fields = line.split()
            if len(fields) == 4 and fields[-1] in selected:
                start, size = int(fields[0], 16), int(fields[1], 16)
                ranges.append((start, start + size))
        if len(ranges) != 2:
            raise ValueError('missing sized reload/terminal symbols')
        instructions = [row for row in instructions if any(a <= row[0] < b for a, b in ranges)]
        symbols = {name: address for name, address in symbols.items() if name in selected}
    if set(symbols) != {'leanos_closed_root_return', 'leanos_closed_root_return_terminal'}:
        raise ValueError('unexpected or missing code symbols')
    terminal = symbols['leanos_closed_root_return_terminal']
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
        ('mov', '%cr3,%rax'), ('cmp', '%rsi,%rax'), ('jne', 'terminal'),
        ('test', '%rdi,%rdi'), ('je', 'terminal'),
        ('test', '$0xfff,%edi'), ('jne', 'terminal'),
        ('cmp', '$0x1000000,%rdi'), ('jae', 'terminal'),
        ('cmp', '%rsi,%rdi'), ('je', 'terminal'),
        ('mov', '%rdi,%cr3'), ('mov', '%cr3,%rax'), ('cmp', '%rdi,%rax'),
        ('jne', 'terminal')]
    expected += [('pop', '%' + reg) for reg in
                 ['r15', 'r14', 'r13', 'r12', 'r11', 'r10', 'r9', 'r8',
                  'rdi', 'rsi', 'rbp', 'rdx', 'rcx', 'rbx', 'rax']]
    expected += [('iretq', ''), ('cli', ''), ('hlt', ''), ('jmp', 'halt')]
    if normalized != expected:
        raise ValueError('return instruction contract differs')
    if instructions[0][0] != symbols['leanos_closed_root_return'] or instructions[38][0] != terminal:
        raise ValueError('entry/terminal boundaries differ')
    if subprocess.check_output(['nm', '-u', str(elf)], text=True).strip():
        raise ValueError('unexpected external dependencies')


def self_test():
    source = (ROOT / 'experiments/copy-roots/return.S').read_text()
    mutations = {
        'missing-reload': ('    mov %rdi, %cr3', '    nop'),
        'missing-pcid-guard': ('$0x20080', '$0x80'),
        'missing-pge-guard': ('$0x20080', '$0x20000'),
        'missing-if-guard': ('$0x200, %edx', '$0, %edx'),
        'missing-alignment': ('$0xfff', '$0'),
        'wrong-arena-bound': ('$0x1000000', '$0x2000000'),
        'early-return': ('    mov %rdi, %cr3', '    ret\n    mov %rdi, %cr3'),
        'missing-readback': ('    mov %cr3, %rax\n    cmp %rdi', '    mov %rdi, %rax\n    cmp %rdi'),
        'wrong-closed-root': ('    cmp %rsi, %rax', '    cmp %rax, %rax'),
        'same-root-allowed': ('    cmp %rsi, %rdi', '    cmp $0, %rdi'),
        'wrong-register': ('    pop %r15', '    pop %r14'),
        'post-restore-clobber': ('    iretq', '    xor %eax, %eax\n    iretq'),
        'frame-write': ('    pop %r15', '    movq $0, (%rsp)\n    pop %r15'),
        'wrong-iret': ('    iretq', '    ret'),
        'unsupported-stac': ('    mov %rdi, %cr3', '    stac\n    mov %rdi, %cr3'),
        'terminal-return': ('1:  hlt', '1:  ret'),
        'post-reload-call': ('    pop %r15', '    call leanos_closed_root_return_terminal\n    pop %r15'),
        'undecodable-tail': ('    jmp 1b', '    jmp 1b\n    .byte 0x0f'),
    }
    with tempfile.TemporaryDirectory(prefix='leanos-copy-root-') as directory:
        path = Path(directory)

        def build(name, text):
            asm, obj, elf = (path / (name + suffix) for suffix in ('.S', '.o', '.elf'))
            asm.write_text(text)
            subprocess.run([os.environ.get('LEANOS_CC', 'gcc'), '-m64', '-c', str(asm), '-o', str(obj)], check=True)
            subprocess.run(['ld', '-nostdlib', '--build-id=none', '-e', 'leanos_closed_root_return',
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
    print(f'closed-root return: linked baseline PASS; {len(mutations)} mutations rejected')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf', nargs='?', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.elf:
        check(args.elf)
        print('closed-root return instruction contract PASS')
    else:
        parser.error('provide an ELF or --self-test')
