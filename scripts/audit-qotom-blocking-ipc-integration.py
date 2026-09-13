#!/usr/bin/env python3
"""Audit the linked Qotom blocking-IPC profile and rejection guards."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def load(elf):
    symbols = {}
    for line in subprocess.check_output(
            ['nm', '-S', '--defined-only', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) == 4:
            symbols[fields[3]] = (int(fields[0], 16), int(fields[1], 16))
    for line in subprocess.check_output(
            ['nm', '-n', '--defined-only', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) == 3 and fields[2] not in symbols:
            symbols[fields[2]] = (int(fields[0], 16), 0)
    output = subprocess.check_output(
        ['objdump', '-d', '--no-show-raw-insn', str(elf)], text=True)
    if 'file format elf64-x86-64' not in output:
        raise ValueError('expected x86-64 ELF')
    rows = []
    for line in output.splitlines():
        match = re.fullmatch(r'\s*([0-9a-f]+):\s+(\S+)\s*(.*?)\s*', line)
        if match:
            rows.append((int(match[1], 16), match[2], match[3]))
        elif re.match(r'\s*[0-9a-f]+:', line):
            raise ValueError('undecodable instruction bytes')
    return symbols, rows


def body(symbols, rows, name):
    matches = [key for key in symbols if key == name or key.startswith(name + '.')]
    if len(matches) != 1:
        raise ValueError(f'missing or ambiguous linked body: {name}')
    start, size = symbols[matches[0]]
    result = [row for row in rows if start <= row[0] < start + size]
    if not result or result[0][0] != start:
        raise ValueError(f'missing linked instructions: {name}')
    return result


def calls(rows, target):
    return sum(row[1] == 'call' and re.search(rf'<{re.escape(target)}(?:>|\+)', row[2])
               is not None for row in rows)


def syscall_numbers(rows):
    result = []
    for index, row in enumerate(rows):
        if row[1] != 'int':
            continue
        if row[2] != '$0x80':
            raise ValueError('user code contains a non-INT-0x80 software interrupt')
        for prior in reversed(rows[:index]):
            match = re.fullmatch(r'\$(0x[0-9a-f]+),%rax', prior[2])
            if match:
                result.append(int(match.group(1), 16))
                break
        else:
            raise ValueError('INT 0x80 has no constant syscall-number load')
    return result


def facts(elf):
    symbols, rows = load(elf)
    required_sizes = {
        'qotom_saved_a': 20 * 8,
        'qotom_saved_b': 20 * 8,
        'qotom_copy_root': 0xb000,
        'qotom_copy_out_root': 0xb000,
        'qotom_entry_closed_root': 8,
    }
    if any(symbols.get(name, (0, 0))[1] != size
           for name, size in required_sizes.items()):
        raise ValueError('blocking context bank or root storage differs')
    required = {
        'qotom_blocking_user_a', 'qotom_blocking_user_b',
        'qotom_blocking_user_a_fault_instruction',
        'qotom_blocking_user_a_fault_recovered',
        'qotom_blocking_page_fault_dispatch', 'qotom_entry_dispatch',
        'leanos_blocking_ipc_demo', 'leanos_capability_reuse_demo',
        'leanos_copy_root_transfer',
        'leanos_qotom_blocking_ipc_integration_query', 'qotom_entry_start',
    }
    if not required <= symbols.keys():
        raise ValueError('missing blocking-IPC integration symbols')

    user_a = body(symbols, rows, 'qotom_blocking_user_a')
    user_b = body(symbols, rows, 'qotom_blocking_user_b')
    forbidden_user = {'cli', 'sti', 'hlt', 'stac', 'clac', 'in', 'out',
                      'ins', 'outs', 'wrmsr', 'rdmsr', 'syscall', 'sysenter'}
    if any(row[1] in forbidden_user or '%cr' in row[2]
           for row in user_a + user_b):
        raise ValueError('blocking user code retains a privileged operation')
    a_syscalls = syscall_numbers(user_a)
    b_syscalls = syscall_numbers(user_b)

    dispatch = body(symbols, rows, 'qotom_entry_dispatch')
    page_fault = body(symbols, rows, 'qotom_blocking_page_fault_dispatch')
    setup = body(symbols, rows, 'lab_run_qotom_blocking_ipc')
    privilege = body(symbols, rows, 'privilege_init')
    selected = dispatch + page_fault + setup
    if any(row[1] in {'sti', 'stac', 'clac', 'wrmsr', 'rdmsr', 'out'}
           for row in selected):
        raise ValueError('blocking profile enables interrupts or performs direct I/O')

    hlt_indices = [i for i, row in enumerate(dispatch) if row[1] == 'hlt']
    terminal_loop = False
    if len(hlt_indices) == 1:
        i = hlt_indices[0]
        terminal_loop = (i > 0 and i + 1 < len(dispatch) and
            dispatch[i - 1][1] == 'cli' and dispatch[i + 1][1] == 'jmp' and
            dispatch[i + 1][2].split()[0] == format(dispatch[i - 1][0], 'x'))

    fault_address = symbols['qotom_blocking_user_a_fault_instruction'][0]
    recovered = symbols['qotom_blocking_user_a_fault_recovered'][0]
    fault_operands = {row[2] for row in page_fault}
    zero_offsets = {'(%rdi)'} | {f'0x{offset:x}(%rdi)' for offset in range(8, 0x60, 8)}
    exact_fault_frame = (
        all(f'$0x0,{operand}' in fault_operands for operand in zero_offsets) and
        '$0x4,0x60(%rdi)' in fault_operands and
        '$0x1,0x70(%rdi)' in fault_operands and
        '$0x0,0x78(%rdi)' in fault_operands and
        '$0x5,0x80(%rdi)' in fault_operands and
        f'$0x{fault_address:x},0x88(%rdi)' in fault_operands and
        '$0x23,0x90(%rdi)' in fault_operands and
        '$0x10002,%rcx' in fault_operands and
        '$0x1b,0xa8(%rdi)' in fault_operands and
        f'$0x{recovered:x},0x88(%rdi)' in fault_operands)

    out8_sites = [i for i, row in enumerate(privilege)
                  if row[1] == 'call' and '<out8>' in row[2]]
    pic_mask_pairs = []
    for i in out8_sites:
        if i >= 2:
            pic_mask_pairs.append((privilege[i - 2][2], privilege[i - 1][2]))
    direct_ports = []
    for i, row in enumerate(setup):
        if row[1] != 'call' or '<in8>' not in row[2]:
            continue
        candidates = [re.fullmatch(r'\$(0x[0-9a-f]+),%edi', prior[2])
                      for prior in setup[max(0, i - 3):i] if prior[1] == 'mov']
        candidates = [match for match in candidates if match]
        if len(candidates) != 1:
            raise ValueError('PIC mask read port is not an immediate argument')
        direct_ports.append(int(candidates[0].group(1), 16))

    return {
        'a_syscalls': a_syscalls,
        'b_syscalls': b_syscalls,
        'blocking_model_calls': calls(dispatch, 'leanos_blocking_ipc_demo'),
        'capability_model_calls': calls(dispatch, 'leanos_capability_reuse_demo'),
        'copy_transfer_calls': calls(dispatch, 'leanos_copy_root_transfer'),
        'admission_query_calls': calls(setup, 'leanos_qotom_blocking_ipc_integration_query'),
        'entry_start_calls': calls(setup, 'qotom_entry_start'),
        'gate_check_calls': calls(setup, 'qotom_blocking_gate_exact'),
        'port_read_calls': calls(setup, 'in8'),
        'direct_ports': direct_ports,
        'pic_mask_pairs': pic_mask_pairs,
        'exact_fault_frame': exact_fault_frame,
        'terminal_loop': terminal_loop,
        'context_banks': 2,
        'copy_roots': 2,
    }


EXPECTED = {
    'a_syscalls': [4, 4, 8, 3],
    'b_syscalls': [10, 11, 12, 7, 9, 3],
    'blocking_model_calls': 4,
    'capability_model_calls': 4,
    'copy_transfer_calls': 2,
    'admission_query_calls': 3,
    'entry_start_calls': 1,
    'gate_check_calls': 2,
    'port_read_calls': 2,
    'direct_ports': [0x21, 0xa1],
    'pic_mask_pairs': [('$0xff,%esi', '$0x21,%edi'),
                       ('$0xff,%esi', '$0xa1,%edi')],
    'exact_fault_frame': True,
    'terminal_loop': True,
    'context_banks': 2,
    'copy_roots': 2,
}


def validate(observed):
    for key, expected in EXPECTED.items():
        if observed.get(key) != expected:
            raise ValueError(f'blocking-IPC linked contract differs: {key}')
    if any(port in {0x40, 0x41, 0x42, 0x43} for port in observed['direct_ports']):
        raise ValueError('blocking profile retains PIT programming')


def check(elf):
    runpy.run_path(str(ROOT / 'scripts/audit-qotom-entry-integration.py'))['check'](
        elf, exception_integration=True, blocking_ipc_integration=True)
    observed = facts(elf)
    validate(observed)
    raw = Path(elf).read_bytes()
    return {
        'schema': 'leanos-qotom-blocking-ipc-integration-audit-v1',
        'elf_sha256': hashlib.sha256(raw).hexdigest(),
        'cpl3_syscalls_including_failure_sentinels': 10,
        'semantic_syscalls': 8,
        'recoverable_page_faults': 1,
        'context_switches': 2,
        'copy_transfers': observed['copy_transfer_calls'],
        'blocking_model_transitions': observed['blocking_model_calls'],
        'capability_model_transitions': observed['capability_model_calls'],
        'pic_masks': [0xff, 0xff],
        'timer_gate_present': False,
        'pit_programmed': False,
        'terminal_policy': 'cli-hlt',
        'entry_audit_passed': True,
    }


def self_test():
    baseline = {key: (value.copy() if isinstance(value, list) else value)
                for key, value in EXPECTED.items()}
    validate(baseline)
    rejected = 0
    mutations = {
        'missing-copy': ('copy_transfer_calls', 1),
        'extra-model-transition': ('blocking_model_calls', 5),
        'missing-capability-transition': ('capability_model_calls', 3),
        'altered-user-interrupt': ('a_syscalls', [4, 4, 3]),
        'altered-capability-order': ('b_syscalls', [10, 12, 11, 7, 9, 3]),
        'missing-admission-query': ('admission_query_calls', 2),
        'missing-gate-check': ('gate_check_calls', 1),
        'timer-port': ('direct_ports', [0x21, 0x43, 0xa1]),
        'unmasked-pic': ('pic_mask_pairs', [('$0xfe,%esi', '$0x21,%edi'),
                                            ('$0xff,%esi', '$0xa1,%edi')]),
        'partial-fault-frame': ('exact_fault_frame', False),
        'returning-terminal': ('terminal_loop', False),
        'one-context-bank': ('context_banks', 1),
        'one-copy-root': ('copy_roots', 1),
    }
    for name, (key, value) in mutations.items():
        candidate = dict(baseline); candidate[key] = value
        try:
            validate(candidate)
        except ValueError:
            rejected += 1
            continue
        raise ValueError(f'unsafe mutation accepted: {name}')
    print(f'Qotom blocking IPC: baseline PASS; {rejected} mutations rejected')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf', nargs='?', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.elf:
        print(json.dumps(check(args.elf), indent=2, sort_keys=True))
    else:
        parser.error('provide an ELF or --self-test')
