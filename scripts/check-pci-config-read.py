#!/usr/bin/env python3
"""Check mechanism-1 adapter encoding and exact privileged I/O sequence."""
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def check(path):
    disassembly = subprocess.check_output(
        ['objdump', '-d', '--no-show-raw-insn', str(path)], text=True)
    instructions = []
    for line in disassembly.splitlines():
        match = re.fullmatch(r'\s*[0-9a-f]+:\s+([a-z0-9]+)\s*(.*?)\s*', line)
        if match:
            instructions.append((match[1], match[2]))
        elif re.match(r'\s*[0-9a-f]+:', line):
            raise ValueError('undecodable instruction')
    expected = [('pushf', ''), ('cli', ''), ('mov', '%edi,%eax'),
                ('mov', '$0xcf8,%edx'), ('out', '%eax,(%dx)'),
                ('mov', '$0xcfc,%edx'), ('in', '(%dx),%eax'),
                ('popf', ''), ('ret', '')]
    if instructions != expected:
        raise ValueError('configuration-read instruction contract')
    if subprocess.check_output(['nm', '-u', str(path)], text=True).strip():
        raise ValueError('unresolved dependency')


def main():
    cc = os.environ.get('LEANOS_CC', 'gcc')
    source = (ROOT / 'boot/pci-config-read.S').read_text()
    mutations = {
        'missing-cli': ('    cli', '    nop'),
        'lost-flags': ('    popfq', '    add $8, %rsp'),
        'unconditional-sti': ('    popfq', '    popfq\n    sti'),
        'wrong-address-port': ('$0xcf8', '$0xcfc'),
        'wrong-data-port': ('$0xcfc', '$0xcf8'),
        'data-write': ('    in %dx, %eax', '    out %eax, %dx'),
        'short-read': ('    in %dx, %eax', '    in %dx, %ax'),
        'wrong-argument': ('    mov %edi, %eax', '    mov %esi, %eax'),
        'call': ('    ret', '    call unexpected\n    ret'),
    }
    with tempfile.TemporaryDirectory(prefix='leanos-pci-read-') as tmp:
        directory = Path(tmp)
        for name, change in [('baseline', None), *mutations.items()]:
            asm, obj = directory / (name + '.S'), directory / (name + '.o')
            if change:
                old, new = change
                assert source.count(old) == 1, name
                asm.write_text(source.replace(old, new))
            else:
                asm.write_text(source)
            subprocess.run([cc, '-m64', '-c', str(asm), '-o', str(obj)], check=True)
            try:
                check(obj)
            except ValueError:
                if not change:
                    raise
            else:
                if change:
                    raise RuntimeError('accepted mutation: ' + name)
        binary = directory / 'host'
        subprocess.run([cc, '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                        '-Iboot', 'tests/pci-config-read.c', '-o', str(binary)],
                       cwd=ROOT, check=True)
        subprocess.run([str(binary)], check=True)
    print('PCI configuration read: native instruction audit and nine mutations PASS')


if __name__ == '__main__':
    main()
