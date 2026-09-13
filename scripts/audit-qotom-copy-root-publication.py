#!/usr/bin/env python3
"""Audit the linked production-bound Qotom root-publication wrapper."""
import json
import re
import subprocess
import sys

SYMBOL = 'lab_publish_qotom_copy_roots'
ROOT_BYTES = 11 * 4096


def audit(disassembly, symbols):
    instructions = []
    for line in disassembly.splitlines():
        match = re.match(r'^\s*[0-9a-f]+:\s+(?:[0-9a-f]{2}\s+)+\s*(\S+)(?:\s+(.*))?$', line)
        if match:
            instructions.append((match.group(1), match.group(2) or ''))
    if not instructions:
        raise ValueError('missing copy-root publication instructions')
    if any(op in {'stac', 'clac', 'iret', 'iretq', 'ret', 'retq'}
           for op, _ in instructions):
        raise ValueError('unsupported copy-root publication instruction')
    cr3_reads = sum('%cr3' in args and not args.rstrip().endswith('%cr3')
                    for _, args in instructions)
    cr3_writes = sum('%cr3' in args and args.rstrip().endswith('%cr3')
                     for _, args in instructions)
    calls = [args for op, args in instructions if op.startswith('call')]
    if sum('<leanos_copy_root_transfer>' in args for args in calls) != 1:
        raise ValueError('wrapper must call the audited transfer exactly once')
    if sum('<leanos_qotom_copy_root_publication_query>' in args for args in calls) != 4:
        raise ValueError('wrapper must make the four publication queries')
    if cr3_reads != 1 or cr3_writes != 0:
        raise ValueError('wrapper must only read CR3 once; the audited helper writes it')
    parsed = {}
    for line in symbols.splitlines():
        match = re.fullmatch(r'([0-9a-f]+)\s+([0-9a-f]+)\s+[bB]\s+(qotom_(?:closed|copy)_root)', line.strip())
        if match:
            parsed[match.group(3)] = (int(match.group(1), 16), int(match.group(2), 16))
    if set(parsed) != {'qotom_closed_root', 'qotom_copy_root'}:
        raise ValueError('missing root-storage symbols')
    for address, size in parsed.values():
        if address == 0 or address & 0xfff or address >= 0x1000000 or size != ROOT_BYTES:
            raise ValueError('invalid linked root storage')
    left = parsed['qotom_closed_root'][0]
    right = parsed['qotom_copy_root'][0]
    if not (left + ROOT_BYTES <= right or right + ROOT_BYTES <= left):
        raise ValueError('linked root storage overlaps')
    return {'schema': 'leanos-qotom-copy-root-publication-audit-v1',
            'symbol': SYMBOL, 'instruction_count': len(instructions),
            'transfer_calls': 1, 'boundary_calls': 4,
            'cr3_reads': 1, 'cr3_writes': 0, 'stac_clac': 0,
            'root_bytes': ROOT_BYTES,
            'closed_root': left, 'copy_root': right}


def selftest():
    body = ('  1: e8 00 00 00 00 call 6 <leanos_copy_root_transfer>\n' +
            ''.join(f'  {i + 6:x}: e8 00 00 00 00 call b <leanos_qotom_copy_root_publication_query>\n'
                    for i in range(4)) +
            '  1a: 0f 20 d8 mov %cr3,%rax\n')
    syms = '00100000 0000b000 b qotom_closed_root\n0010b000 0000b000 b qotom_copy_root\n'
    audit(body, syms)
    mutations = [body + '  1d: 0f 01 cb stac\n',
                 body + '  1d: 0f 22 d8 mov %rax,%cr3\n',
                 body.replace('<leanos_copy_root_transfer>', '<other>'),
                 body.replace('<leanos_qotom_copy_root_publication_query>', '<other>', 1)]
    for mutation in mutations:
        try:
            audit(mutation, syms)
        except ValueError:
            continue
        raise SystemExit('copy-root publication audit accepted a mutation')
    for bad_symbols in (syms.replace('0000b000', '0000a000', 1),
                        syms.replace('0010b000', '0010a000')):
        try:
            audit(body, bad_symbols)
        except ValueError:
            continue
        raise SystemExit('copy-root publication audit accepted bad storage')


if __name__ == '__main__':
    if len(sys.argv) == 2 and sys.argv[1] == '--self-test':
        selftest()
        print('Qotom copy-root publication audit mutations rejected')
    elif len(sys.argv) == 2:
        disassembly = subprocess.check_output(
            ['objdump', '-d', '--disassemble=' + SYMBOL, sys.argv[1]], text=True)
        symbols = subprocess.check_output(['nm', '-S', sys.argv[1]], text=True)
        print(json.dumps(audit(disassembly, symbols), sort_keys=True))
    else:
        raise SystemExit('usage: audit-qotom-copy-root-publication.py ELF | --self-test')
