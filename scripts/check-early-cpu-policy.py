#!/usr/bin/env python3
"""Check the actual 32-bit CPU guard and bounded rejection in the linked ELF."""
import importlib.util
from pathlib import Path
import sys

spec = importlib.util.spec_from_file_location('early_idt', Path(__file__).with_name('check-early-idt-policy.py'))
idt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(idt)
elf = Path(sys.argv[1])
symbols = idt.read_symbols(elf)
sections = idt.read_sections(elf)


def match_region(first, past, plan, external):
    instructions = idt.disassemble_i386(elf, sections, symbols[first], symbols[past])
    expected = []
    labels = dict(external)
    for line in plan.strip().splitlines():
        line = line.strip()
        if line.endswith(':'):
            labels[line[:-1]] = len(expected)
        else:
            expected.append(line.split(' ', 1))
    if len(instructions) != len(expected):
        idt.fail(f'early CPU instruction inventory drifted: {first}')
    for index, ((address, mnemonic, operands), row) in enumerate(zip(instructions, expected)):
        op = row[0]
        arg = row[1] if len(row) == 2 else ''
        if mnemonic != op:
            idt.fail(f'early CPU opcode drifted: {first} instruction={index}')
        if arg.startswith('@'):
            target = labels[arg[1:]]
            if arg[1:] not in external:
                target = instructions[target][0]
            valid = idt.operand_address(operands) == target
        else:
            valid = operands.replace(' ', '') == arg
        if not valid:
            idt.fail(f'early CPU operand/branch drifted: {first} instruction={index}')
    return instructions


required = ('boot_cpu_gate_begin', 'boot_cpu_gate_end', 'boot_cpu_rejected',
            'boot_cpu_rejected_end', 'boot_cpu_rejected_record',
            'boot_cpu_rejected_record_end', 'normalize_extended_state_cr4')
for name in required:
    if name not in symbols:
        idt.fail(f'early CPU symbol missing: {name}')
if not (symbols['boot_idt32_published'] < symbols['boot_cpu_gate_begin'] <
        symbols['boot_cpu_gate_end'] <= symbols['normalize_extended_state_cr4']):
    idt.fail('early CPU gate is not between IDT ownership and control writes')

# The only successful path from IDT publication must fall through the guard.
# The existing bootstrap32 fault probe may deliberately terminate first.
before = idt.disassemble_i386(elf, sections, symbols['boot_idt32_published'],
                              symbols['boot_cpu_gate_begin'])
if before and before[0][1] == 'ud2':
    before = before[1:]
expected_handoff = [('mov', f'%eax,0x{symbols["multiboot_magic"]:x}'),
                    ('mov', f'%ebx,0x{symbols["multiboot_info"]:x}')]
if [(op, args.replace(' ', '')) for _, op, args in before] != expected_handoff:
    idt.fail('early CPU gate can be bypassed or handoff preservation drifted')

entry = idt.disassemble_i386(elf, sections, symbols['multiboot_entry'],
                             symbols['long_mode_entry'])
for address, op, args in entry:
    if (op in ('rdmsr', 'wrmsr') or '%cr' in args) and address < symbols['boot_cpu_gate_end']:
        idt.fail('control/MSR access precedes early CPU authorization')

match_region('boot_cpu_gate_begin', 'boot_cpu_gate_end', '''
xor %eax,%eax
xor %ecx,%ecx
cpuid
cmp $0x1,%eax
jb @rejected
cmp $0x756e6547,%ebx
jne @amd
cmp $0x49656e69,%edx
jne @rejected
cmp $0x6c65746e,%ecx
jne @rejected
jmp @common
amd:
cmp $0x68747541,%ebx
jne @rejected
cmp $0x69746e65,%edx
jne @rejected
cmp $0x444d4163,%ecx
jne @rejected
common:
mov $0x1,%eax
xor %ecx,%ecx
cpuid
and $0x7800869,%edx
cmp $0x7800869,%edx
jne @rejected
mov $0x80000000,%eax
xor %ecx,%ecx
cpuid
cmp $0x80000001,%eax
jb @rejected
mov $0x80000001,%eax
xor %ecx,%ecx
cpuid
and $0x20100800,%edx
cmp $0x20100800,%edx
jne @rejected
''', {'rejected': symbols['boot_cpu_rejected']})

record = b'LEANOS/3 FINAL status=FAIL reason=early-cpu-capability\n'
start = symbols['boot_cpu_rejected_record']
if symbols['boot_cpu_rejected_record_end'] - start != len(record) or idt.read_virtual(elf, sections, start, len(record)) != record:
    idt.fail('early CPU rejection record drifted')
terminal = match_region('boot_cpu_rejected', 'boot_cpu_rejected_end', f'''
cli
mov $0x{start:x},%esi
mov $0x{len(record):x},%ecx
next:
mov $0x10000,%edi
mov $0x3fd,%dx
poll:
in (%dx),%al
test $0x20,%al
jne @ready
sub $0x1,%edi
jne @poll
jmp @halt
ready:
mov (%esi),%al
mov $0x3f8,%dx
out %al,(%dx)
add $0x1,%esi
sub $0x1,%ecx
jne @next
halt:
hlt
jmp @halt
''', {})
idt.check_terminal_stub('boot_cpu_rejected', terminal,
                        symbols['boot_cpu_rejected'], symbols['boot_cpu_rejected_end'])
print('Early CPU guard and bounded UART rejection match the linked instruction contract')
