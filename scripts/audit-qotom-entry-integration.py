#!/usr/bin/env python3
"""Audit the linked Qotom CPL3 entry checkpoint and rejection mutations."""
import argparse
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def linked(elf):
    symbols = {}
    for line in subprocess.check_output(['nm', '-S', '--defined-only', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) == 4:
            symbols[fields[3]] = (int(fields[0], 16), int(fields[1], 16))
    for line in subprocess.check_output(['nm', '-n', '--defined-only', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) == 3 and fields[2] not in symbols:
            symbols[fields[2]] = (int(fields[0], 16), 0)
    rows = []
    code = ('qotom_entry_start', 'qotom_entry_isr80', 'qotom_entry_isr2',
            'qotom_entry_isr6', 'qotom_entry_isr8', 'qotom_entry_isr13',
            'qotom_entry_isr14', 'qotom_entry_exception_closed',
            'qotom_entry_exception_unclosed', 'qotom_entry_exception_frame',
            'qotom_entry_entry_terminal',
            'qotom_entry_emit_and_halt',
            'qotom_entry_user')
    output = ''.join(subprocess.check_output(
        ['objdump', '-d', '--no-show-raw-insn', f'--disassemble={name}', str(elf)], text=True)
        for name in code)
    if 'file format elf64-x86-64' not in output:
        raise ValueError('expected x86-64 ELF')
    for line in output.splitlines():
        match = re.fullmatch(r'\s*([0-9a-f]+):\s+([a-z0-9]+)\s*(.*?)\s*', line)
        if match:
            rows.append((int(match[1], 16), match[2], match[3]))
        elif re.match(r'\s*[0-9a-f]+:', line):
            raise ValueError('undecodable instruction bytes')
    return symbols, rows


def check(elf, exception_integration=False):
    symbols, rows = linked(elf)
    required = {
        'qotom_entry_start', 'qotom_entry_isr80', 'qotom_entry_isr2',
        'qotom_entry_isr6', 'qotom_entry_isr8', 'qotom_entry_isr13',
            'qotom_entry_isr14', 'qotom_entry_exception_closed',
            'qotom_entry_exception_unclosed', 'qotom_entry_exception_frame',
            'qotom_entry_entry_terminal',
            'qotom_entry_emit_and_halt',
        'qotom_entry_user', 'qotom_entry_user_after_first',
        'qotom_entry_user_after_second', 'qotom_entry_user_failure',
        'leanos_closed_root_return',
        'qotom_entry_dispatch', 'qotom_entry_closed_root',
        'qotom_entry_gp_dispatch',
        'qotom_entry_subject_root', 'qotom_entry_observed_root',
    }
    if not required <= symbols.keys():
        raise ValueError('missing entry integration symbols')
    if exception_integration and 'qotom_entry_user_exception' not in symbols:
        raise ValueError('missing terminal user exception symbol')

    def body(name):
        start, size = symbols[name]
        result = [row for row in rows if start <= row[0] < start + size]
        if not result or result[0][0] != start:
            raise ValueError(f'missing linked body: {name}')
        return result

    def mnemonics(name):
        return [row[1] for row in body(name)]

    def target(row, expected):
        match = re.match(r'([0-9a-f]+)\s+<', row[2])
        if not match or int(match[1], 16) != symbols[expected][0]:
            raise ValueError(f'{row[1]} does not target {expected}')

    def rip_target(row, expected):
        match = re.search(r'#\s+([0-9a-f]+)\s+<', row[2])
        if not match or int(match[1], 16) != symbols[expected][0]:
            raise ValueError(f'{row[1]} does not address {expected}')

    forbidden = {'stac', 'clac', 'ret', 'retq', 'iret', 'iretq'}
    start = body('qotom_entry_start')
    if [row[1] for row in start] != (
            ['cli', 'cld', 'mov', 'mov'] + ['push'] * 5 +
            ['xor'] + ['push'] * 15 + ['mov', 'mov', 'jmp']):
        raise ValueError('initial CPL3 return frame differs')
    if [row[2] for row in start[4:9]] != [
            '$0x1b', '%rcx', '$0x2', '$0x23', '%rdx']:
        raise ValueError('initial CPL3 return-frame operands differ')
    if any(row[1] in forbidden for row in start):
        raise ValueError('unsafe initial return instruction')
    target(start[-1], 'leanos_closed_root_return')

    ordinary = body('qotom_entry_isr80')
    expected = (['cld'] + ['push'] * 15 +
        ['mov', 'mov', 'mov', 'test', 'je', 'test', 'jne', 'mov', 'mov',
         'cmp', 'jne', 'mov', 'call', 'mov', 'mov', 'jmp'])
    if [row[1] for row in ordinary] != expected:
        raise ValueError('ordinary entry instruction sequence differs')
    registers = ['%rax', '%rbx', '%rcx', '%rdx', '%rbp', '%rsi', '%rdi',
                 '%r8', '%r9', '%r10', '%r11', '%r12', '%r13', '%r14', '%r15']
    if [row[2] for row in ordinary[1:16]] != registers:
        raise ValueError('ordinary entry does not save the complete GPR bank first')
    if ordinary[16][2] != '%cr3,%rax' or 'qotom_entry_observed_root' not in ordinary[17][2]:
        raise ValueError('incoming root observation differs')
    if '%r10,%cr3' != ordinary[23][2] or ordinary[24][2] != '%cr3,%r11':
        raise ValueError('closed-root reload/readback differs')
    if ordinary[27][2] != '%rsp,%rdi':
        raise ValueError('dispatcher frame argument differs')
    target(ordinary[28], 'qotom_entry_dispatch')
    target(ordinary[-1], 'leanos_closed_root_return')
    if any(row[1] in forbidden for row in ordinary) or sum(row[1] == 'call' for row in ordinary) != 1:
        raise ValueError('ordinary entry has an unsafe transfer')

    exception_shape = ['mov', 'cli', 'cld', 'mov', 'test', 'je', 'test', 'jne',
                       'mov', 'mov', 'cmp', 'jne', 'jmp']
    exception_stubs = ['qotom_entry_isr2', 'qotom_entry_isr8',
                       'qotom_entry_isr14']
    if not exception_integration:
        exception_stubs.append('qotom_entry_isr6')
    for name in exception_stubs:
        rows_for_stub = body(name)
        if [row[1] for row in rows_for_stub] != exception_shape:
            raise ValueError(f'terminal exception shape differs: {name}')
        if rows_for_stub[8][2] != '%r10,%cr3' or rows_for_stub[9][2] != '%cr3,%r11':
            raise ValueError(f'exception does not close and read back root: {name}')
        target(rows_for_stub[-1], 'qotom_entry_exception_closed')
        if any(row[1] in forbidden or row[1] == 'call' for row in rows_for_stub):
            raise ValueError(f'exception can call or return: {name}')
    if exception_integration:
        invalid = body('qotom_entry_isr6')
        invalid_shape = [
            'mov', 'cli', 'cld', 'mov', 'mov', 'test', 'je', 'test', 'jne',
            'mov', 'mov', 'cmp', 'jne', 'mov', 'cmp', 'jne', 'lea', 'cmp',
            'jne', 'cmpq', 'jne', 'lea', 'cmp', 'jne', 'cmpq', 'jne', 'mov',
            'test', 'jne', 'test', 'je', 'test', 'je', 'jmp']
        if [row[1] for row in invalid] != invalid_shape:
            raise ValueError('invalid-opcode frame validation shape differs')
        if (invalid[3][2] != '%cr3,%r9' or invalid[9][2] != '%r10,%cr3' or
                invalid[10][2] != '%cr3,%r11'):
            raise ValueError('invalid-opcode entry does not close and read back root')
        rip_target(invalid[13], 'qotom_entry_subject_root')
        rip_target(invalid[16], 'qotom_entry_user_exception')
        rip_target(invalid[21], 'user_a_stack_top')
        if (invalid[14][2] != '%r10,%r9' or
                invalid[17][2] != '%r10,(%rsp)' or invalid[19][2] != '$0x23,0x8(%rsp)' or
                invalid[22][2] != '%r10,0x18(%rsp)' or
                invalid[24][2] != '$0x1b,0x20(%rsp)' or
                invalid[26][2] != '0x10(%rsp),%r10' or
                invalid[27][2] != '$0x3e7700,%r10' or
                invalid[29][2] != '$0x10000,%r10' or
                invalid[31][2] != '$0x2,%r10'):
            raise ValueError('invalid-opcode frame operands differ')
        target(invalid[-1], 'qotom_entry_exception_closed')
        if any(row[1] in forbidden or row[1] == 'call' for row in invalid):
            raise ValueError('invalid-opcode entry can call or return')
    gp = body('qotom_entry_isr13')
    if [row[1] for row in gp] != ['cli', 'cld', 'mov', 'test', 'je', 'test',
            'jne', 'mov', 'mov', 'cmp', 'jne', 'mov', 'call', 'ud2']:
        raise ValueError('general-protection diagnostic shape differs')
    if gp[7][2] != '%r10,%cr3' or gp[8][2] != '%cr3,%r11' or gp[11][2] != '%rsp,%rdi':
        raise ValueError('general-protection diagnostic does not close root first')
    target(gp[12], 'qotom_entry_gp_dispatch')
    if any(row[1] in forbidden for row in gp) or sum(row[1] == 'call' for row in gp) != 1:
        raise ValueError('general-protection diagnostic can return')

    for name, shape in (('qotom_entry_exception_closed', ['mov', 'jmp']),
                        ('qotom_entry_exception_unclosed', ['mov', 'jmp']),
                        ('qotom_entry_exception_frame', ['mov', 'jmp']),
                        ('qotom_entry_entry_terminal', ['mov', 'mov', 'jmp'])):
        terminal = body(name)
        if [row[1] for row in terminal] != shape:
            raise ValueError(f'terminal marker differs: {name}')
        target(terminal[-1], 'qotom_entry_emit_and_halt')
    emitter = body('qotom_entry_emit_and_halt')
    if (sum(row[1] == 'out' for row in emitter) != 4 or
            sum(row[1] == 'hlt' for row in emitter) != 1 or
            any(row[1] in forbidden or row[1] == 'call' for row in emitter)):
        raise ValueError('terminal serial marker can call or return')
    halt = next(row[0] for row in emitter if row[1] == 'hlt')
    if emitter[-1][1] != 'jmp' or emitter[-1][2].split()[0] != format(halt, 'x'):
        raise ValueError('terminal marker halt loop differs')

    user = body('qotom_entry_user')
    ints = [row for row in user if row[1] == 'int']
    expected_ints = 3 if exception_integration else 2
    if len(ints) != expected_ints or any(row[2] != '$0x80' for row in ints):
        raise ValueError('user checkpoint INT 0x80 paths differ')
    expected_jne = 16 if exception_integration else 15
    expected_ud2 = 2 if exception_integration else 1
    if ([row[1] for row in user].count('jne') != expected_jne or
            [row[1] for row in user].count('ud2') != expected_ud2):
        raise ValueError('user GPR validation or terminal trap differs')
    expected_compares = ['$0x51525354,%rax', '$0x2222,%rbx', '$0x3333,%rcx',
        '$0x4444,%rdx', '$0x5555,%rbp', '$0x6666,%rsi', '$0x7777,%rdi',
        '$0x8888,%r8', '$0x9999,%r9', '$0xaaaa,%r10', '$0xbbbb,%r11',
        '%rax,%r12', '%rax,%r13', '$0xeeee,%r14', '$0xffff,%r15']
    if exception_integration:
        expected_compares.append('%rdi,%rax')
    if [row[2] for row in user if row[1] == 'cmp'] != expected_compares:
        raise ValueError('user GPR comparison bank differs')
    failure = symbols['qotom_entry_user_failure'][0]
    for row in user:
        if row[1] == 'jne':
            match = re.match(r'([0-9a-f]+)\s+<', row[2])
            if not match or int(match[1], 16) != failure:
                raise ValueError('user validation does not fail closed')
    if user[-1][1] != 'ud2' or any(row[1] in {'call', 'ret', 'retq', 'iret', 'iretq', 'stac', 'clac'} for row in user):
        raise ValueError('user checkpoint has an unsafe transfer')
    if exception_integration:
        after_second = symbols['qotom_entry_user_after_second'][0]
        suffix = [row for row in user if row[0] >= after_second]
        if ([row[1] for row in suffix] != ['movabs', 'cmp', 'jne', 'ud2', 'mov', 'int', 'ud2'] or
                suffix[0][2] != '$0x6162636465666768,%rdi' or
                suffix[1][2] != '%rdi,%rax' or suffix[5][2] != '$0x80'):
            raise ValueError('terminal #UD return validation differs')

    runpy.run_path(str(ROOT / 'scripts/check-closed-root-return.py'))['check'](
        elf, within_bundle=True)
    result = {
        'schema': 'leanos-qotom-entry-integration-audit-v1',
        'ordinary_saved_gprs': 15,
        'ordinary_calls_after_close': 1,
        'terminal_exception_vectors': [2, 6, 8, 13, 14],
        'user_entries': 2,
        'user_validated_gprs': 15,
        'closed_root_return_audited': True,
        'stac_clac_reachable': False,
    }
    if exception_integration:
        result.update(terminal_user_exception=6,
                      completed_returns_before_terminal=2)
    return result


def self_test():
    source = (ROOT / 'experiments/copy-roots/entry.S').read_text()
    mutations = {
        'missing-final-save': ('push %r13; push %r14; push %r15', 'push %r13; push %r14; nop'),
        'fake-incoming-root': ('    mov %cr3, %rax\n    mov %rax, qotom_entry_observed_root', '    xor %eax, %eax\n    mov %rax, qotom_entry_observed_root'),
        'missing-close-readback': ('    mov %cr3, %r11', '    mov %r10, %r11'),
        'ordinary-return': ('    jmp leanos_closed_root_return\n.size qotom_entry_isr80', '    ret\n.size qotom_entry_isr80'),
        'ordinary-stac': ('qotom_entry_isr80:\n    cld', 'qotom_entry_isr80:\n    stac\n    cld'),
        'one-user-entry': ('    mov $0x52, %rax\n    int $0x80', '    mov $0x52, %rax\n    nop'),
        'missing-gpr-check': ('    cmp $0xffff, %r15', '    cmp %r15, %r15'),
        'exception-return': ('    jmp qotom_entry_exception_closed\n    .size \\name, .-\\name',
                             '    ret\n    .size \\name, .-\\name'),
        'terminal-return': ('5:  hlt\n    jmp 5b', '5:  hlt\n    ret'),
        'user-interrupts-enabled': ('    pushq $0x2\n    pushq $0x23',
                                    '    pushq $0x202\n    pushq $0x23'),
    }
    exception_mutations = {
        'exception-fake-incoming-root': ('    mov %cr3, %r9', '    xor %r9, %r9'),
        'exception-fake-rip': ('    cmp %r10, 0(%rsp)', '    cmp %r10, %r10'),
        'exception-wrong-cs': ('    cmpq $0x23, 8(%rsp)', '    cmpq $0x8, 8(%rsp)'),
        'exception-fake-rsp': ('    cmp %r10, 24(%rsp)', '    cmp %r10, %r10'),
        'exception-wrong-ss': ('    cmpq $0x1b, 32(%rsp)', '    cmpq $0x23, 32(%rsp)'),
        'exception-flags-mask': ('    test $0x3e7700, %r10', '    test $0, %r10'),
        'exception-missing-rf': ('    test $0x10000, %r10', '    test $2, %r10'),
        'exception-missing-trap': ('qotom_entry_user_exception:\n    ud2',
                                   'qotom_entry_user_exception:\n    nop'),
    }
    fixture = '''
.data
.globl qotom_entry_closed_root, qotom_entry_subject_root, qotom_entry_observed_root
qotom_entry_closed_root: .quad 0
qotom_entry_subject_root: .quad 0
qotom_entry_observed_root: .quad 0
.globl user_a_stack_top
user_a_stack_top: .quad 0
.text
.globl qotom_entry_dispatch
.type qotom_entry_dispatch,@function
qotom_entry_dispatch: xor %eax,%eax; ret
.size qotom_entry_dispatch,.-qotom_entry_dispatch
.globl qotom_entry_gp_dispatch
.type qotom_entry_gp_dispatch,@function
qotom_entry_gp_dispatch: ud2
.size qotom_entry_gp_dispatch,.-qotom_entry_gp_dispatch
.section .note.GNU-stack,"",@progbits
'''
    with tempfile.TemporaryDirectory(prefix='leanos-entry-audit-') as directory:
        directory = Path(directory)

        def build(name, text, exception_integration=False):
            asm = directory / f'{name}.S'; obj = directory / f'{name}.o'
            ret_obj = directory / f'{name}-return.o'; fixture_asm = directory / 'fixture.S'
            fixture_obj = directory / 'fixture.o'; elf = directory / f'{name}.elf'
            asm.write_text(text); fixture_asm.write_text(fixture)
            cc = os.environ.get('LEANOS_CC', 'gcc')
            command = [cc, '-m64']
            if exception_integration:
                command.append('-DLEANOS_QOTOM_EXCEPTION_INTEGRATION=1')
            subprocess.run(command + ['-c', str(asm), '-o', str(obj)], check=True)
            subprocess.run([cc, '-m64', '-c', str(ROOT / 'experiments/copy-roots/return.S'), '-o', str(ret_obj)], check=True)
            subprocess.run([cc, '-m64', '-c', str(fixture_asm), '-o', str(fixture_obj)], check=True)
            subprocess.run(['ld', '-nostdlib', '--build-id=none', '-e', 'qotom_entry_start',
                            '-Ttext', '0x100000', '-o', str(elf), str(obj), str(ret_obj), str(fixture_obj)], check=True)
            return elf

        check(build('baseline', source))
        check(build('exception-baseline', source, True), True)
        for name, (old, new) in mutations.items():
            if source.count(old) != 1:
                raise ValueError(f'mutation no longer applies uniquely: {name}')
            try:
                check(build(name, source.replace(old, new)))
            except ValueError:
                continue
            raise ValueError(f'unsafe mutation accepted: {name}')
        for name, (old, new) in exception_mutations.items():
            if source.count(old) != 1:
                raise ValueError(f'mutation no longer applies uniquely: {name}')
            try:
                check(build(name, source.replace(old, new), True), True)
            except ValueError:
                continue
            raise ValueError(f'unsafe mutation accepted: {name}')
    total = len(mutations) + len(exception_mutations)
    print(f'Qotom entry integration: linked baselines PASS; {total} mutations rejected')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf', nargs='?', type=Path)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--exception-integration', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.elf:
        import json
        print(json.dumps(check(args.elf, args.exception_integration), indent=2, sort_keys=True))
    else:
        parser.error('provide an ELF or --self-test')
