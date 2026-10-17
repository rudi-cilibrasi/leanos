#!/usr/bin/env python3
"""Check the production Qotom network image (issue #569).

Run after scripts/build-qotom-production.py. Checks, on the linked ELF and
the boot page plan the build generated for it:

* the three subject address spaces: the plan has three roots; subject C's
  text and stack are user pages in root C only; A's and B's user pages are
  absent from root C; and every user page of a subject is absent from the
  other two roots;
* the production profile's linked contract
  (audit-qotom-blocking-ipc-integration.py --production-network) and the
  copy-root inventory (audit-qotom-copy-root-publication.py --inventory
  production);
* no recovery-lab harness: no watchdog reload or session-end code, no
  reset store, the absorbing terminal, and the production MODE record;
* the build manifest marks a production candidate with no recovery reset.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/qotom-production'
ELF = OUT / 'leanos-qotom-production.elf'
PLAN = OUT / 'final-page-plan.h'
PAGE = 4096


def plan_arrays(text):
    arrays = {}
    for name, body in re.findall(
            r'static const unsigned long long (leanos_boot_plan_[abc])\[4096\] = \{(.*?)\};',
            text, re.S):
        values = [int(v) for v in re.findall(r'([0-9]+)ULL', body)]
        if len(values) != 4096:
            raise SystemExit(f'{name} has {len(values)} leaves')
        arrays[name[-1]] = values
    return arrays


def symbol_table(elf):
    table = {}
    for line in subprocess.check_output(['nm', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) == 3:
            table[fields[2]] = int(fields[0], 16)
    return table


def pages(symbols, name):
    start, end = symbols[f'__user_{name}_start'], symbols[f'__user_{name}_end']
    if start % PAGE or end <= start:
        raise SystemExit(f'user range {name} is not page aligned')
    return range(start // PAGE, (end + PAGE - 1) // PAGE)


def main() -> int:
    symbols = symbol_table(ELF)
    plan = plan_arrays(PLAN.read_text())
    if sorted(plan) != ['a', 'b', 'c']:
        raise SystemExit('the production boot plan must have three roots')
    user = 4
    owned = {'a': list(pages(symbols, 'a_text')) + list(pages(symbols, 'a_stack')),
             'b': list(pages(symbols, 'b_text')) + list(pages(symbols, 'b_stack')),
             'c': list(pages(symbols, 'c_text')) + list(pages(symbols, 'c_stack'))}
    if len(owned['c']) != 2:
        raise SystemExit('subject C must have one text page and one stack page')
    for subject, frames in owned.items():
        for page in frames:
            leaf = plan[subject][page]
            if not leaf & 1 or not leaf & user or leaf >> 12 & ((1 << 40) - 1) != page:
                raise SystemExit(f'subject {subject} page {page:#x} is not its own user page')
            for other in 'abc':
                if other != subject and plan[other][page] != 0:
                    raise SystemExit(f'root {other} maps subject {subject} page {page:#x}')
    for subject in 'abc':
        user_pages = {page for page, leaf in enumerate(plan[subject]) if leaf & 1 and leaf & user}
        if user_pages != set(owned[subject]):
            raise SystemExit(f'root {subject} has user pages outside its subject')

    for command in (
            ['python3', 'scripts/audit-qotom-blocking-ipc-integration.py',
             '--production-network', str(ELF)],
            ['python3', 'scripts/audit-qotom-copy-root-publication.py', '--inventory',
             'production', str(ELF)]):
        subprocess.run(command, cwd=ROOT, check=True, capture_output=True)

    required = {'frame_window_transfer', 'page_map_level_4_c', 'qotom_echo_subject_entry',
                'qotom_echo_subject_main', 'qotom_dhcp_subject_main', 'user_c_stack',
                'leanos_frame_window_operand', 'leanos_frame_port_check',
                'leanos_qotom_broadcom_assign_admission'}
    if not required <= symbols.keys():
        raise SystemExit(f'missing production symbols: {sorted(required - symbols.keys())}')
    if any(name.startswith('qotom_watchdog_') or name.startswith('qotom_net_')
           for name in symbols):
        raise SystemExit('the production image retains lab watchdog or network-subject code')
    disassembly = subprocess.check_output(['objdump', '-d', '--no-show-raw-insn', str(ELF)],
                                          text=True)
    if re.search(r'\$0xcf9\b', disassembly) or re.search(r'\$0x460\b', disassembly):
        raise SystemExit('the production image retains a reset or watchdog port')
    # finish() is the absorbing halt; the compiler may inline it, and then no
    # out-of-line body remains. Either way no reset or watchdog port is
    # reachable (checked above over the whole image).
    finish = subprocess.check_output(['objdump', '-d', '--no-show-raw-insn',
                                      '--disassemble=finish', str(ELF)], text=True)
    finish_rows = re.findall(r'^\s*[0-9a-f]+:\s+(\S+)', finish, re.M)
    if finish_rows and ('hlt' not in finish_rows or
                        any(op in ('out', 'call') for op in finish_rows)):
        raise SystemExit('finish is not the absorbing halt')
    raw = ELF.read_bytes()
    if b'MODE qotom-production final=halt watchdog=none' not in raw or \
            b'qotom-reset-after-final' in raw:
        raise SystemExit('the production MODE record is missing or a reset mode remains')
    manifest = json.loads((OUT / 'manifest.json').read_text())
    if manifest.get('evidence_class') != 'production-candidate' or \
            manifest.get('recovery_seconds') is not None or \
            not manifest.get('production_network'):
        raise SystemExit('the build manifest does not describe a production candidate')
    print('PASS Qotom production image: three roots, root C separate, production '
          'contract, copy-root inventory, no watchdog or reset')
    return 0


if __name__ == '__main__':
    sys.exit(main())
