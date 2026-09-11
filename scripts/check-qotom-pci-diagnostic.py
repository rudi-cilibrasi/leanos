#!/usr/bin/env python3
"""Replay a bounded native PCI boot capture without granting platform admission."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

SPEC = importlib.util.spec_from_file_location(
    'cpu_diagnostic', Path(__file__).with_name('check-j1900-diagnostic.py'))
CPU = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CPU)
DiagnosticError = CPU.DiagnosticError
MAX_CAPTURE = 16384
# QotomPCIInventory.Error.code and PCIHeaderObservation.Error.code. Unknown
# results are a protocol mismatch, even though no outcome grants admission.
INVENTORY_RESULTS = {1, 0x10000, 0x10001}
INVENTORY_RESULTS.update(0x20000 + reason * 256 + index
                         for reason in range(5) for index in range(15))
INVENTORY_RESULTS.update(base + index for base in (0x30000, 0x40000, 0x50000, 0x60000)
                         for index in range(15))


def load_protocol(path):
    wanted = {('25', name) for name in ('BOOT', 'CPU', 'CONTROL', 'PCI-SCAN', 'PCI-HEADER')}
    wanted.add(('3', 'FINAL'))
    found = {}
    for line in Path(path).read_text().splitlines():
        fields = line.split('\t')
        if len(fields) == 5 and fields[0] == 'record' and tuple(fields[1:3]) in wanted:
            if fields[2] in found:
                raise DiagnosticError('duplicate protocol identity')
            found[fields[2]] = fields[4]
    if len(found) != len(wanted):
        raise DiagnosticError('missing protocol identity')
    return found


def classify(raw, protocol, cpu_replay, pci_replay):
    if not raw or len(raw) > MAX_CAPTURE or not raw.endswith(b'\n'):
        raise DiagnosticError('capture length or terminator')
    if any(byte != 10 and not 32 <= byte <= 126 for byte in raw):
        raise DiagnosticError('capture contains non-text bytes')
    lines = raw.decode('ascii').splitlines()
    if not 3 <= len(lines) <= 21:
        raise DiagnosticError('record count')
    boot = protocol['BOOT'] + ' target=qotom-j1900-candidate phase=pci-inventory-diagnostic platform-admitted=0 cpl3=0'
    if lines[0] != boot:
        raise DiagnosticError('boot identity or admission claim')
    # Reuse the generated CPU/MSR replay and its exact rejection boundaries.
    cpu_lines = [lines[0].replace('phase=pci-inventory-diagnostic', 'phase=cpu-diagnostic'), lines[1]]
    has_control = lines[2].startswith(protocol['CONTROL'] + ' ')
    if has_control:
        cpu_lines.append(lines[2])
    has_scan = len(lines) > 4 and lines[3].startswith(protocol['PCI-SCAN'] + ' ')
    cpu_lines.append(protocol['FINAL'] + ' status=FAIL reason=qotom-platform-pending' if has_scan else lines[-1])
    result = CPU.classify(('\n'.join(cpu_lines) + '\n').encode(), protocol, cpu_replay)
    scan = None
    headers = []
    inventory = None
    if result['terminal_reason'] != 'qotom-platform-pending':
        if len(lines) != len(cpu_lines):
            raise DiagnosticError('PCI records follow rejected CPU or MSR')
    else:
        if not has_scan:
            raise DiagnosticError('accepted CPU/MSR lacks PCI scan')
        names = ('status', 'count', 'bus', 'device', 'function', 'offset')
        pattern = re.escape(protocol['PCI-SCAN']) + ' codec=1' + ''.join(
            ' ' + name + '=(' + CPU.DECIMAL + ')' for name in names)
        match = re.fullmatch(pattern, lines[3])
        if not match:
            raise DiagnosticError('malformed PCI scan')
        scan = dict(zip(names, map(int, match.groups())))
        if any(scan[name] > limit for name, limit in zip(names, (3, 16, 255, 31, 7, 60))) or scan['offset'] % 4:
            raise DiagnosticError('PCI scan width or alignment')
        if scan['status']:
            if scan['count'] or len(lines) != 5:
                raise DiagnosticError('failed scan publishes headers')
            if scan['status'] == 2 and scan['offset']:
                raise DiagnosticError('capacity failure offset')
            if scan['status'] == 3 and any(scan[name] for name in names[1:]):
                raise DiagnosticError('invalid argument failure location')
            reason = 'qotom-pci-enumeration'
        else:
            if any(scan[name] for name in names[2:]) or len(lines) != 5 + scan['count']:
                raise DiagnosticError('successful scan location or count')
            previous = None
            for index, line in enumerate(lines[4:-1]):
                pattern = (re.escape(protocol['PCI-HEADER']) + ' codec=1 index=' + str(index)
                           + r' width=19 words=(' + CPU.DECIMAL + r'(?:,' + CPU.DECIMAL + r'){18})')
                match = re.fullmatch(pattern, line)
                if not match:
                    raise DiagnosticError('malformed or unordered PCI header')
                words = list(map(int, match[1].split(',')))
                if any(word > limit for word, limit in zip(words, [255, 31, 7] + [0xffffffff] * 16)):
                    raise DiagnosticError('PCI header word width')
                address = tuple(words[:3])
                if previous is not None and address <= previous:
                    raise DiagnosticError('PCI addresses not strictly increasing')
                if words[3] & 0xffff == 0xffff:
                    raise DiagnosticError('absent function published')
                previous = address
                headers.append(words)
            inventory = CPU.replay_words(pci_replay, 'inventory',
                                         [len(headers), *(word for header in headers for word in header)])
            # The executable is generated from the inventory model; its result
            # is observational and never substitutes for DMA quarantine.
            if inventory not in INVENTORY_RESULTS:
                raise DiagnosticError('unknown generated inventory result')
            reason = 'qotom-platform-pending'
        if lines[-1] != protocol['FINAL'] + ' status=FAIL reason=' + reason:
            raise DiagnosticError('terminal result disagrees with scan')
        result['terminal_reason'] = reason
    result.update(schema='leanos-qotom-pci-diagnostic-replay-v1',
                  capture_sha256=hashlib.sha256(raw).hexdigest(),
                  pci_scan=scan, pci_headers=headers, inventory_result=inventory)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('--protocol', type=Path, default=Path('build/boot/serial-protocol.tsv'))
    parser.add_argument('--cpu-replay', type=Path, default=Path('build/j1900-cpu-host/host'))
    parser.add_argument('--pci-replay', type=Path, default=Path('build/qotom-pci-inventory-host/host'))
    args = parser.parse_args()
    try:
        with args.capture.open('rb') as stream:
            raw = stream.read(MAX_CAPTURE + 1)
        result = classify(raw, load_protocol(args.protocol), args.cpu_replay.resolve(), args.pci_replay.resolve())
        for name, path in [('protocol', args.protocol), ('cpu_replay', args.cpu_replay), ('pci_replay', args.pci_replay)]:
            result[name + '_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(json.dumps(result, indent=2))
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f'error: {error}\n')


if __name__ == '__main__':
    main()
