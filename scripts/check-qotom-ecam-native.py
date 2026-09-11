#!/usr/bin/env python3
"""Check exact native ECAM primitive instructions and their C ABI."""
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    'lab_ecam_native_load32': [('mov', '(%rsi),%eax'), ('mov', '%eax,(%rdx)'),
                              ('mov', '$0x1,%eax'), ('ret', '')],
    'lab_ecam_native_invalidate': [('invlpg', '(%rsi)'), ('ret', '')],
    'lab_ecam_native_controls': [
        ('push', '%rbx'), ('mov', '%rsi,%r8'), ('pushf', ''), ('pop', '%r9'),
        ('mov', '$0x1,%eax'), ('xor', '%ecx,%ecx'), ('cpuid', ''),
        ('and', '$0x10020,%edx'), ('cmp', '$0x10020,%edx'), ('jne', '@32'),
        ('mov', '$0x277,%ecx'), ('rdmsr', ''), ('mov', '%eax,%eax'),
        ('shl', '$0x20,%rdx'), ('or', '%rdx,%rax'), ('mov', '%rax,(%r8)'),
        ('mov', '%cr0,%rax'), ('mov', '%rax,0x8(%r8)'), ('mov', '%cr3,%rax'),
        ('mov', '%rax,0x10(%r8)'), ('mov', '%cr4,%rax'), ('mov', '%rax,0x18(%r8)'),
        ('mov', '$0xc0000080,%ecx'), ('rdmsr', ''), ('mov', '%eax,%eax'),
        ('shl', '$0x20,%rdx'), ('or', '%rdx,%rax'), ('mov', '%rax,0x20(%r8)'),
        ('mov', '%r9,0x28(%r8)'), ('mov', '$0x1,%eax'), ('pop', '%rbx'), ('ret', ''),
        ('xor', '%eax,%eax'), ('pop', '%rbx'), ('ret', '')],
}


def check(path):
    text = subprocess.check_output(['objdump', '-d', '--no-show-raw-insn', str(path)], text=True)
    groups = {}
    current = None
    for line in text.splitlines():
        symbol = re.fullmatch(r'[0-9a-f]+ <([^>]+)>:', line)
        if symbol:
            current = symbol[1]; groups[current] = []
        instruction = re.fullmatch(r'\s*([0-9a-f]+):\s+([a-z0-9]+)\s*(.*?)\s*', line)
        if instruction:
            if current is None: raise ValueError('instruction outside primitive')
            groups[current].append((int(instruction[1], 16), instruction[2], instruction[3]))
        elif re.match(r'\s*[0-9a-f]+:', line):
            raise ValueError('undecodable instruction')
    normalized = {}
    for name, instructions in groups.items():
        addresses = {address: index for index, (address, _, _) in enumerate(instructions)}
        result = []
        for _, op, operand in instructions:
            if op.startswith('j'):
                try: operand = '@' + str(addresses[int(operand.split()[0], 16)])
                except (ValueError, KeyError): raise ValueError('branch leaves primitive') from None
            result.append((op, operand))
        normalized[name] = result
    if normalized != EXPECTED:
        raise ValueError('native ECAM instruction contract')
    if subprocess.check_output(['nm', '-u', str(path)], text=True).strip():
        raise ValueError('native ECAM unresolved dependency')


def main():
    cc = os.environ.get('CC', 'gcc')
    source = (ROOT / 'hardware/lab/qotom-ecam-native.S').read_text()
    mutations = {
        'short-load': ('mov (%rsi), %eax', 'mov (%rsi), %ax'),
        'wide-load': ('mov (%rsi), %eax', 'mov (%rsi), %rax'),
        'mmio-write': ('mov %eax, (%rdx)', 'mov %eax, (%rsi)'),
        'duplicate-load': ('mov (%rsi), %eax', 'mov (%rsi), %eax\n    mov (%rsi), %eax'),
        'no-invalidation': ('invlpg (%rsi)', 'nop'),
        'wrong-invalidation': ('invlpg (%rsi)', 'invlpg (%rdi)'),
        'gate-bypass': ('jne .Lecam_unavailable', 'nop'),
        'missing-pat-gate': ('and $0x10020, %edx', 'and $0x20, %edx'),
        'wrong-msr': ('mov $0x277, %ecx', 'mov $0x278, %ecx'),
        'msr-write': ('    rdmsr', '    wrmsr'),
        'root-write': ('mov %cr3, %rax', 'mov %rax, %cr3'),
        'lost-callee-save': ('push %rbx', 'push %rcx'),
    }
    with tempfile.TemporaryDirectory(prefix='ecam-native-') as tmp:
        directory = Path(tmp)
        for name, change in [('baseline', None), *mutations.items()]:
            asm, obj = directory / (name + '.S'), directory / (name + '.o')
            asm.write_text(source if change is None else source.replace(*change, 1))
            subprocess.run([cc, '-m64', '-c', str(asm), '-o', str(obj)], check=True)
            try: check(obj)
            except ValueError:
                if change is None: raise
            else:
                if change is not None: raise AssertionError('accepted mutation: ' + name)
        abi = directory / 'abi.c'
        abi.write_text('#include "qotom-ecam-native.h"\n#include "qotom-ecam-window.h"\n'
                       'struct lab_ecam_window binding = {.controls=lab_ecam_native_controls,'
                       '.invalidate=lab_ecam_native_invalidate,.load32=lab_ecam_native_load32};\n')
        subprocess.run([cc, '-m64', '-std=c11', '-Wall', '-Wextra', '-Werror', '-ffreestanding',
                        '-I', str(ROOT / 'hardware/lab'), '-c', str(abi), '-o', str(directory / 'abi.o')], check=True)
        subprocess.run(['ld', '-r', str(directory / 'abi.o'), str(directory / 'baseline.o'),
                        '-o', str(directory / 'linked.o')], check=True)
        if subprocess.check_output(['nm', '-u', str(directory / 'linked.o')]).strip():
            raise AssertionError('unresolved native C ABI')
        subprocess.run([cc, '-m64', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
            '-I', str(ROOT / 'hardware/lab'), str(ROOT / 'tests/qotom-ecam-native.c'),
            str(directory / 'baseline.o'), '-o', str(directory / 'load-test')], check=True)
        subprocess.run([str(directory / 'load-test')], check=True)
    print('ECAM native primitives: ABI, exact instruction sequence and 12 mutations PASS')


if __name__ == '__main__': main()
