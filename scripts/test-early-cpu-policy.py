#!/usr/bin/env python3
"""Reject altered linked CPU guards, including bypass and infinite UART paths."""
import importlib.util
from pathlib import Path
import struct
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('early_idt', root / 'scripts/check-early-idt-policy.py')
idt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(idt)
elf = Path(sys.argv[1])
symbols = idt.read_symbols(elf)
sections = idt.read_sections(elf)
raw = elf.read_bytes()
checker = root / 'scripts/check-early-cpu-policy.py'
subprocess.run([sys.executable, str(checker), str(elf)], check=True)


def offset(address):
    for base, file_offset, size in sections:
        if base <= address < base + size:
            return file_offset + address - base
    raise AssertionError(address)


def replace_region(data, first, past, old, new):
    start, end = offset(symbols[first]), offset(symbols[past])
    part = data[start:end]
    assert old in part and len(old) == len(new)
    data[start:end] = part.replace(old, new)


with tempfile.TemporaryDirectory() as directory:
    cases = []
    data = bytearray(raw)
    replace_region(data, 'boot_cpu_gate_begin', 'boot_cpu_gate_end',
                   struct.pack('<I', 0x07800869), struct.pack('<I', 0x07800849))
    cases.append(('missing-msr-feature', data))
    data = bytearray(raw)
    replace_region(data, 'boot_cpu_gate_begin', 'boot_cpu_gate_end',
                   struct.pack('<I', 0x20100800), struct.pack('<I', 0x20000800))
    cases.append(('missing-nx-feature', data))
    data = bytearray(raw)
    replace_region(data, 'boot_cpu_gate_begin', 'boot_cpu_gate_end',
                   struct.pack('<I', 0x20100000), struct.pack('<I', 0x20000000))
    cases.append(('intel-missing-nx-feature', data))
    data = bytearray(raw)
    address = symbols['boot_idt32_published']
    data[offset(address):offset(address)+5] = b'\xe9' + struct.pack('<i', symbols['boot_cpu_gate_end'] - address - 5)
    cases.append(('bypass-cpu-gate', data))
    data = bytearray(raw)
    replace_region(data, 'boot_cpu_rejected', 'boot_cpu_rejected_end',
                   b'\xbf\x00\x00\x01\x00', b'\xbf\x00\x00\x00\x00')
    cases.append(('zero-uart-budget', data))
    data = bytearray(raw)
    replace_region(data, 'boot_cpu_rejected', 'boot_cpu_rejected_end',
                   b'\x83\xef\x01', b'\x90\x90\x90')
    cases.append(('unbounded-uart-poll', data))
    for name, data in cases:
        target = Path(directory) / (name + '.elf')
        target.write_bytes(data)
        result = subprocess.run([sys.executable, str(checker), str(target)], text=True, capture_output=True)
        if result.returncode == 0 or 'error: early CPU' not in result.stderr:
            raise AssertionError((name, result.returncode, result.stdout, result.stderr))
        print(f'Early CPU fixture {name}: rejected')
    # Correct 32-bit decoding must still discover real I/O, rather than merely
    # suppress the former false opcode decoded from the far-jump address.
    data = bytearray(raw)
    position = offset(symbols['boot_cpu_gate_begin'])
    data[position:position+2] = b'\xec\x90'  # in (%dx),%al; nop
    target = Path(directory) / 'real-bootstrap-io.elf'
    target.write_bytes(data)
    result = subprocess.run([sys.executable, str(root / 'scripts/check-direct-port-sites.py'),
                             str(target)], cwd=root, text=True, capture_output=True)
    if result.returncode == 0 or 'unauthorized final-ELF port-I/O site boot_cpu_gate_begin' not in result.stderr:
        raise AssertionError(('real-bootstrap-io', result.stdout, result.stderr))
    print('Early CPU fixture real-bootstrap-io: detected by port audit')
