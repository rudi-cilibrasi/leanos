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
    wanted.update((('16', 'DIRECT-PORT-CONTROL'), ('17', 'ENTRY-MANIFEST')))
    qualified = {
        ('6', 'COPY'),
        ('8', 'PAGING'),
        ('9', 'CAPREUSE'),
        ('10', 'IPC'),
        ('10', 'FINAL'),
        ('11', 'USER-FAULT'),
    }
    found = {}
    for line in Path(path).read_text().splitlines():
        fields = line.split('\t')
        identity = tuple(fields[1:3])
        if len(fields) == 5 and fields[0] == 'record' and identity in wanted | qualified:
            key = '/'.join(identity) if identity in qualified else fields[2]
            if key in found:
                raise DiagnosticError('duplicate protocol identity')
            found[key] = fields[4]
    if len(found) != len(wanted) + len(qualified):
        raise DiagnosticError('missing protocol identity')
    return found


def classify(raw, protocol, cpu_replay, pci_replay, *, native_inventory=False, native_kernel=False):
    if native_kernel and not native_inventory:
        raise DiagnosticError("kernel native inventory requires the native replay profile")
    if native_inventory:
        checked = subprocess.run([str(pci_replay)], capture_output=True, timeout=30, check=True)
        if checked.stdout != b'Hosted native Qotom inventory replay passed\n':
            raise DiagnosticError('native inventory replay identity mismatch')
    if not raw or len(raw) > MAX_CAPTURE or not raw.endswith(b'\n'):
        raise DiagnosticError('capture length or terminator')
    if any(byte != 10 and not 32 <= byte <= 126 for byte in raw):
        raise DiagnosticError('capture contains non-text bytes')
    lines = raw.decode('ascii').splitlines()
    kernel_inventory = None
    if native_kernel and len(lines) >= 2 and lines[-2].startswith('LEANOS-LAB/1 NATIVE-PCI '):
        record = re.fullmatch(
            r'LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 status=([034])'
            r' index=(' + CPU.DECIMAL + r') count=(' + CPU.DECIMAL + r')', lines.pop(-2))
        if not record:
            raise DiagnosticError('malformed kernel native inventory record')
        kernel_inventory = dict(zip(('status', 'index', 'count'), map(int, record.groups())))
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
            allowed = INVENTORY_RESULTS
            if native_inventory:
                allowed = allowed | {0x20000 + reason * 256 + 15 for reason in range(5)} | {
                    base + 15 for base in (0x30000, 0x40000, 0x50000, 0x60000)}
            if inventory == 1 and len(headers) != (16 if native_inventory else 15):
                raise DiagnosticError('inventory success disagrees with selected profile count')
            if inventory not in allowed:
                raise DiagnosticError('unknown generated inventory result')
            reason = 'qotom-platform-pending'
            if native_kernel:
                status = 0 if inventory == 1 else 3 if inventory == 0x10000 else 4
                index = inventory & 0xff if status == 4 else 0
                expected = {'status': status, 'index': index, 'count': len(headers)}
                if kernel_inventory != expected:
                    raise DiagnosticError('kernel native inventory disagrees with generated replay')
                if status != 0:
                    reason = 'qotom-native-inventory'
        if lines[-1] != protocol['FINAL'] + ' status=FAIL reason=' + reason:
            raise DiagnosticError('terminal result disagrees with scan')
        result['terminal_reason'] = reason
    if kernel_inventory is not None and (scan is None or scan['status'] != 0):
        raise DiagnosticError('kernel native inventory follows an incomplete scan')
    result.update(schema='leanos-qotom-pci-diagnostic-replay-v1',
                  capture_sha256=hashlib.sha256(raw).hexdigest(),
                  pci_scan=scan, pci_headers=headers, inventory_result=inventory)
    if native_inventory:
        result['inventory_profile'] = 'qotom-native-ecam-v1'
    if native_kernel:
        result['native_kernel_inventory'] = kernel_inventory
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('--protocol', type=Path, default=Path('build/boot/serial-protocol.tsv'))
    parser.add_argument('--cpu-replay', type=Path, default=Path('build/j1900-cpu-host/host'))
    parser.add_argument('--pci-replay', type=Path, default=Path('build/qotom-pci-inventory-host/host'))
    parser.add_argument('--native-inventory', action='store_true')
    parser.add_argument('--native-kernel', action='store_true')
    args = parser.parse_args()
    try:
        with args.capture.open('rb') as stream:
            raw = stream.read(MAX_CAPTURE + 1)
        result = classify(raw, load_protocol(args.protocol), args.cpu_replay.resolve(), args.pci_replay.resolve(), native_inventory=args.native_inventory, native_kernel=args.native_kernel)
        for name, path in [('protocol', args.protocol), ('cpu_replay', args.cpu_replay), ('pci_replay', args.pci_replay)]:
            result[name + '_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(json.dumps(result, indent=2))
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f'error: {error}\n')


if __name__ == '__main__':
    main()
