#!/usr/bin/env python3
"""Boot the real PCI diagnostic ELF and compare its inventory with QMP."""
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import socket
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def verify_acpi_memory(monitor, directory, metadata, tables):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as connection:
        connection.connect(str(monitor))
        with connection.makefile('rwb') as stream:
            json.loads(stream.readline())
            commands = [{'execute': 'qmp_capabilities'}]
            for table in metadata['tables']:
                path = directory / f"qmp-{table['address']:016x}.bin"
                commands.append({'execute': 'pmemsave', 'arguments': {
                    'val': table['address'], 'size': table['length'], 'filename': str(path)}})
            for command in commands:
                stream.write((json.dumps(command) + '\n').encode()); stream.flush()
                while True:
                    response = json.loads(stream.readline())
                    if 'error' in response: raise RuntimeError(response['error'])
                    if 'return' in response: break
            for table in metadata['tables']:
                name = f"{table['address']:016x}.bin"
                if (directory / ('qmp-' + name)).read_bytes() != tables[name]:
                    raise RuntimeError('serial ACPI copy differs from independent QMP physical memory')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--elf', type=Path, default=ROOT / 'build/boot/leanos-qotom-pci-diagnostic.elf')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/qotom-pci-diagnostic-image')
    parser.add_argument('--lab-completion', action='store_true',
                        help='require the lab completion-mode prefix before diagnostic records')
    parser.add_argument('--handoff-capture', action='store_true')
    parser.add_argument('--acpi-capture', action='store_true')
    args = parser.parse_args()
    if args.acpi_capture and not args.handoff_capture:
        parser.error('--acpi-capture requires --handoff-capture')
    if args.handoff_capture and not args.lab_completion:
        parser.error('--handoff-capture requires --lab-completion')
    handoff = runpy.run_path(str(ROOT / 'scripts/check-qotom-handoff-capture.py')) if args.handoff_capture else None
    elf = args.elf.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = output / 'results.json'
    report.unlink(missing_ok=True)
    diagnostic = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
    native = runpy.run_path(str(ROOT / 'scripts/test-pci-config-read-qemu.py'))
    protocol_path = ROOT / 'build/boot/serial-protocol.tsv'
    protocol = diagnostic['load_protocol'](protocol_path)
    cpu_replay = ROOT / 'build/j1900-cpu-host/host'
    pci_replay = ROOT / 'build/qotom-pci-inventory-host/host'
    subprocess.run(['grub-file', '--is-x86-multiboot2', str(elf)], check=True)
    if subprocess.check_output(['nm', '-u', str(elf)]).strip():
        raise RuntimeError('diagnostic ELF has unresolved symbols')
    grub = output / 'iso/boot/grub'
    grub.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(elf, grub.parent / 'leanos.elf')
    shutil.copyfile(ROOT / 'boot/grub.cfg', grub / 'grub.cfg')
    iso = output / 'diagnostic.iso'
    with (output / 'grub.log').open('w') as log:
        subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    accepted_cpu = 'max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off'
    cases = [('root-bus', accepted_cpu, False, False, 65536),
             ('two-bridges', accepted_cpu, True, False, 65536),
             ('capacity', accepted_cpu, True, True, 65536),
             ('wrong-vendor', accepted_cpu.replace('GenuineIntel', 'AuthenticAMD'), False, False, 5),
             ('wrong-stepping', accepted_cpu.replace('stepping=8', 'stepping=9'), False, False, 6),
             ('missing-smep', accepted_cpu + ',smep=off', False, False, 9),
             ('unexpected-smap', accepted_cpu.replace('smap=off', 'smap=on'), False, False, 11),
             ('missing-structured-leaf', accepted_cpu + ',level=6', False, False, 2)]
    results = []
    for name, cpu, bridged, capacity, selected in cases:
        directory = output / name
        directory.mkdir(exist_ok=True)
        capture = directory / 'serial.log'
        capture.unlink(missing_ok=True)
        with tempfile.TemporaryDirectory(prefix='leanos-pci-boot-', dir='/tmp') as tmp:
            monitor = Path(tmp) / 'qmp.sock'
            # No debug-exit device: the diagnostic's terminal halt keeps QMP
            # available for an independent post-enumeration inventory query.
            command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', cpu,
                       '-m', '128', '-smp', '1', '-display', 'none', '-serial', f'file:{capture}',
                       '-monitor', 'none', '-nic', 'none', '-no-reboot', '-no-shutdown',
                       '-qmp', f'unix:{monitor},server=on,wait=off', '-cdrom', str(iso)]
            if bridged:
                command += ['-device', 'pci-bridge,id=bridge1,chassis_nr=1,addr=2',
                            '-device', 'pci-bridge,id=bridge2,chassis_nr=2,addr=3',
                            '-device', 'pci-testdev,bus=bridge1,addr=5',
                            '-device', 'pci-testdev,bus=bridge2,addr=6']
            if capacity:
                for slot in range(8, 18):
                    command += ['-device', f'pci-testdev,bus=bridge1,addr={slot:x}']
            (directory / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
            with (directory / 'qemu.log').open('w') as log:
                process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
                try:
                    deadline = time.monotonic() + 30
                    while True:
                        raw = capture.read_bytes() if capture.exists() else b''
                        if len(raw) > diagnostic['MAX_CAPTURE'] + (handoff['MAX_TRANSPORT'] if handoff else 0) + (196608 if args.acpi_capture else 0):
                            raise RuntimeError(name + ': capture exceeds bound')
                        if raw.endswith(b'\n') and protocol['FINAL'].encode() in raw:
                            break
                        if process.poll() is not None or time.monotonic() >= deadline:
                            raise RuntimeError(f'{name}: incomplete guest execution: {raw!r}')
                        time.sleep(0.05)
                    payload = raw
                    if args.lab_completion:
                        mode = b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
                        if not raw.startswith(mode) or raw.count(mode) != 1:
                            raise RuntimeError(name + ': missing or repeated lab completion mode')
                        payload = raw[len(mode):]
                    if handoff:
                        consumed, binary, metadata = handoff['parse_prefix'](payload)
                        if metadata['status'] or not metadata['tag_chain_valid']:
                            raise RuntimeError('QEMU did not supply a valid bounded handoff')
                        (directory / 'multiboot2.bin').write_bytes(binary)
                        (directory / 'handoff.json').write_text(json.dumps(metadata, indent=2) + '\n')
                        payload = payload[consumed:]
                    if args.acpi_capture:
                        acpi = runpy.run_path(str(ROOT / 'scripts/check-qotom-acpi-capture.py'))
                        payload, metadata, tables = acpi['extract'](payload, binary)
                        if metadata is not None:
                            (directory / 'acpi').mkdir(exist_ok=True)
                            for filename, content in tables.items():
                                (directory / 'acpi' / filename).write_bytes(content)
                            verify_acpi_memory(monitor, directory, metadata, tables)
                            metadata['qmp_memory_match'] = True
                            (directory / 'acpi.json').write_text(json.dumps(metadata, indent=2) + '\n')
                    result = diagnostic['classify'](payload, protocol, cpu_replay, pci_replay)
                    if result['cpu_selection'] != selected:
                        raise RuntimeError(name + ': wrong CPU result')
                    qmp = native['query_pci'](monitor)
                    (directory / 'query-pci.json').write_text(json.dumps(qmp, indent=2) + '\n')
                    inventory = native['monitor_inventory'](qmp)
                    if selected != 65536:
                        if result['pci_scan'] is not None:
                            raise RuntimeError(name + ': PCI scan after CPU rejection')
                    elif capacity:
                        if len(inventory) <= 16 or result['pci_scan']['status'] != 2 or result['pci_headers']:
                            raise RuntimeError('capacity fixture did not reject without partial publication')
                        if tuple(result['pci_scan'][field] for field in ('bus', 'device', 'function')) != sorted(inventory)[16]:
                            raise RuntimeError('capacity failure does not identify the seventeenth device')
                    else:
                        observed = {tuple(words[:3]): (words[3], words[5] >> 16)
                                    for words in result['pci_headers']}
                        if result['pci_scan']['status'] != 0 or observed != inventory:
                            raise RuntimeError(name + ': capture differs from independent QMP inventory')
                        if bridged and len({bus for bus, _, _ in observed if bus}) != 2:
                            raise RuntimeError('fixture lacks two downstream buses')
                    (directory / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
                    results.append({'case': name, 'capture_sha256': hashlib.sha256(raw).hexdigest(),
                                    'cpu_selection': selected, 'qmp_device_count': len(inventory),
                                    'terminal_reason': result['terminal_reason']})
                finally:
                    if process.poll() is None:
                        process.terminate()
                    process.wait(timeout=5)
        print('Qotom PCI diagnostic image:', name, 'PASS', flush=True)
    report.write_text(json.dumps({
        'lab_completion_transport': args.lab_completion, 'handoff_capture': args.handoff_capture, 'acpi_capture': args.acpi_capture,
        'physical_reset_verified': False,
        'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest(),
        'iso_sha256': hashlib.sha256(iso.read_bytes()).hexdigest(),
        'protocol_sha256': hashlib.sha256(protocol_path.read_bytes()).hexdigest(),
        'cpu_replay_sha256': hashlib.sha256(cpu_replay.read_bytes()).hexdigest(),
        'pci_replay_sha256': hashlib.sha256(pci_replay.read_bytes()).hexdigest(),
        'qemu': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True).splitlines()[0],
        'results': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
