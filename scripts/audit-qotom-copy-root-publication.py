#!/usr/bin/env python3
"""Audit the linked production-bound Qotom root-publication wrapper."""
import json
import re
import subprocess
import sys

SYMBOL = 'lab_publish_qotom_copy_roots'
ROOT_BYTES = 11 * 4096
PAGE = 4096
# The two audited protected inventories (LeanOS.QotomCopyRootPublication):
# A text pages, protected frames, removed source aliases. 'dhcp-subject' is
# the --dhcp-subject image (issue #556), whose A text holds the DHCP client
# and the echo responder. Retained present leaves depend on the whole page
# plan and are checked only by the generated boundary on the machine.
# 'production' is the production network image (issue #569): A text holds
# the asm subjects and the DHCP client (two pages), and the inventory adds
# subject C's text page and stack page, which the image's three-root boot
# plan omits from A's root, so the source still maps only A's text and stack.
INVENTORIES = {'base': (1, 5, 3), 'dhcp-subject': (2, 6, 4), 'production': (2, 8, 4)}
RANGES = ('__user_a_text', '__user_a_stack', '__user_b_text', '__user_b_stack')
C_RANGES = ('__user_c_text', '__user_c_stack')


def inventory(symbols, variant):
    """The linked inventory the wrapper will derive, before any hardware run:
    the protected frames of A's and B's text and stack, of which the source
    root A maps A's text and stack (B's are omitted from it)."""
    if variant not in INVENTORIES:
        raise ValueError('unknown copy-root inventory variant')
    text_pages, protected, removed = INVENTORIES[variant]
    ranges = RANGES + (C_RANGES if variant == 'production' else ())
    addresses = {}
    for line in symbols.splitlines():
        fields = line.split()
        if len(fields) >= 3 and fields[-1].startswith(ranges):
            addresses[fields[-1]] = int(fields[0], 16)
    pages = {}
    for name in ranges:
        start, end = addresses.get(name + '_start'), addresses.get(name + '_end')
        if start is None or end is None or start % PAGE or end <= start:
            raise ValueError(f'copy-root inventory range {name}')
        pages[name] = (end - start + PAGE - 1) // PAGE
    observed = (pages['__user_a_text'], sum(pages.values()),
                pages['__user_a_text'] + pages['__user_a_stack'])
    if pages['__user_a_stack'] != 2 or observed != (text_pages, protected, removed) or \
            (variant == 'production' and (pages['__user_c_text'], pages['__user_c_stack']) != (1, 1)):
        raise ValueError(f'copy-root inventory differs from variant {variant}: '
                         f'A text pages, protected, removed = {observed}')
    return {'inventory_variant': variant, 'user_a_text_pages': observed[0],
            'protected_frames': observed[1], 'removed_aliases': observed[2]}


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
    ranges = ('00200000 T __user_a_text_start\n00201000 T __user_a_text_end\n'
              '00201000 B __user_a_stack_start\n00203000 B __user_a_stack_end\n'
              '00203000 T __user_b_text_start\n00203800 T __user_b_text_end\n'
              '00204000 B __user_b_stack_start\n00205000 B __user_b_stack_end\n')
    two_page = ranges.replace('00201000 T __user_a_text_end', '00201620 T __user_a_text_end')
    assert inventory(ranges, 'base')['protected_frames'] == 5
    assert inventory(two_page, 'dhcp-subject')['removed_aliases'] == 4
    with_c = ranges + ('00205000 T __user_c_text_start\n00205700 T __user_c_text_end\n'
                       '00206000 B __user_c_stack_start\n00207000 B __user_c_stack_end\n')
    with_c = with_c.replace('00201000 T __user_a_text_end', '00201620 T __user_a_text_end')
    assert inventory(with_c, 'production')['protected_frames'] == 8
    assert inventory(with_c, 'production')['removed_aliases'] == 4
    for symbols, variant in ((two_page, 'base'), (ranges, 'dhcp-subject'),
                             (ranges, 'production'),
                             (with_c.replace('00207000 B __user_c_stack_end',
                                             '00208000 B __user_c_stack_end'), 'production'),
                             (with_c.replace('00201620 T __user_a_text_end',
                                             '00201000 T __user_a_text_end'), 'production'),
                             (ranges, 'six-page'),
                             (ranges.replace('00203000 B __user_a_stack_end',
                                             '00202000 B __user_a_stack_end'), 'base'),
                             (ranges.replace('00203000 T __user_b_text_start', ''), 'base')):
        try:
            inventory(symbols, variant)
        except ValueError:
            continue
        raise SystemExit('copy-root publication audit accepted a wrong inventory')


if __name__ == '__main__':
    if len(sys.argv) == 2 and sys.argv[1] == '--self-test':
        selftest()
        print('Qotom copy-root publication audit mutations rejected')
    elif len(sys.argv) in (2, 4) and (len(sys.argv) == 2 or sys.argv[1] == '--inventory'):
        elf = sys.argv[-1]
        disassembly = subprocess.check_output(
            ['objdump', '-d', '--disassemble=' + SYMBOL, elf], text=True)
        symbols = subprocess.check_output(['nm', '-S', elf], text=True)
        result = audit(disassembly, symbols)
        if len(sys.argv) == 4:
            result.update(inventory(subprocess.check_output(['nm', elf], text=True),
                                    sys.argv[2]))
        print(json.dumps(result, sort_keys=True))
    else:
        raise SystemExit('usage: audit-qotom-copy-root-publication.py '
                         '[--inventory base|dhcp-subject|production] ELF | --self-test')
