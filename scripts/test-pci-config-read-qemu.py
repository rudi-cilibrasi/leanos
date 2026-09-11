#!/usr/bin/env python3
"""Execute mechanism-1 reads and compare the complete inventory with QMP."""
import hashlib
import json
import os
from pathlib import Path
import runpy
import socket
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def query_pci(path):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.settimeout(3)
        sock.connect(str(path))
        stream = sock.makefile('rwb')
        json.loads(stream.readline())
        for command in ['qmp_capabilities', 'query-pci']:
            stream.write((json.dumps({'execute': command}) + '\n').encode())
            stream.flush()
            while True:
                response = json.loads(stream.readline())
                if 'error' in response:
                    raise RuntimeError(response['error'])
                if 'return' in response:
                    break
        return response['return']


def monitor_inventory(buses):
    result = {}

    def devices(items):
        for device in items:
            key = (device['bus'], device['slot'], device['function'])
            if key in result:
                raise RuntimeError('duplicate QMP BDF')
            result[key] = (device['id']['vendor'] | device['id']['device'] << 16,
                           device['class_info']['class'])
            devices(device.get('pci_bridge', {}).get('devices', []))
    for bus in buses:
        devices(bus['devices'])
    return result


def validate(raw, inventory, bridged):
    lines = raw.decode('ascii').splitlines()
    if len(lines) < 4 or lines[-1] != 'D':
        raise ValueError('incomplete capture')
    for index, seed in enumerate([0x47, 0x247]):
        fields = lines[index].split()
        if len(fields) != 4 or fields[:2] != ['F', f'{seed:08x}']:
            raise ValueError('malformed flags record')
        if fields[2] != f'{seed:08x}':
            raise ValueError('flags mismatch')
        if fields[3] != f'{inventory[(0, 0, 0)][0]:08x}':
            raise ValueError('host identity mismatch')
    status = lines[2].split()
    if status != ['S', '00000000', f'{len(inventory):08x}', *(['00000000'] * 4)]:
        raise ValueError('enumeration did not complete with expected count')
    observed = {}
    previous = None
    for line in lines[3:-1]:
        fields = line.split()
        if len(fields) != 20 or fields[0] != 'H':
            raise ValueError('header record width')
        values = [int(x, 16) for x in fields[1:]]
        bdf = tuple(values[:3])
        if previous is not None and bdf <= previous:
            raise ValueError('duplicate or unordered BDF')
        previous = bdf
        words = values[3:]
        observed[bdf] = (words[0], words[2] >> 16)
    if observed != inventory:
        raise ValueError('guest inventory differs from independent QMP inventory')
    if bridged and len({b for b, _, _ in observed if b}) != 2:
        raise ValueError('fixture did not exercise two downstream buses')


def main():
    cc = os.environ.get('LEANOS_CC', 'gcc')
    out = ROOT / 'build/pci-config-read' / ('qemu-' + Path(cc).name)
    out.mkdir(parents=True, exist_ok=True)
    report = out / 'results.json'
    report.unlink(missing_ok=True)
    asm = (ROOT / 'boot/pci-config-read.S').read_text()
    header = (ROOT / 'boot/pci-config-read.h').read_text()
    cases = [
        ('root-bus', False, None, None),
        ('two-bridges', True, None, None),
        ('bus-zero-only', True, None, ('(uint32_t)bus << 16', '(uint32_t)bus * 0')),
        ('wrong-data-port', True, ('$0xcfc', '$0xcf8'), None),
        ('lost-flags', True, ('    popfq', '    add $8, %rsp'), None),
        ('unconditional-sti', True, ('    popfq', '    popfq\n    sti'), None),
    ]
    expected_rejections = {
        'bus-zero-only': 'enumeration did not complete with expected count',
        'wrong-data-port': 'host identity mismatch',
        'lost-flags': 'flags mismatch',
        'unconditional-sti': 'flags mismatch',
    }
    results = []
    audit = runpy.run_path(str(ROOT / 'scripts/check-pci-config-read.py'))['check']
    for name, bridged, asm_change, header_change in cases:
        directory = out / name
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        native = directory / 'read.S'
        native.write_text(asm.replace(*asm_change) if asm_change else asm)
        (directory / 'pci-config-read.h').write_text(
            header.replace(*header_change) if header_change else header)
        for source, change in [(asm, asm_change), (header, header_change)]:
            if change and source.count(change[0]) != 1:
                raise RuntimeError('mutation no longer unique: ' + name)
        objects = []
        for source, obj in [(ROOT / 'experiments/pci-read/fixture.S', 'entry.o'),
                            (ROOT / 'experiments/pci-read/fixture.c', 'fixture.o'),
                            (native, 'read.o')]:
            target = directory / obj
            subprocess.run([cc, '-m64', '-O2', '-Wall', '-Wextra', '-Werror',
                            '-ffreestanding', '-fno-builtin', '-fno-stack-protector',
                            '-fno-pie', '-mno-red-zone', '-mgeneral-regs-only',
                            '-I' + str(directory), '-Iboot', '-c', str(source),
                            '-o', str(target)], cwd=ROOT, check=True)
            objects.append(str(target))
        if not asm_change:
            audit(directory / 'read.o')
        elf = grub.parent / 'test.elf'
        subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T',
                        'experiments/pci-read/fixture.ld', '-o', str(elf), *objects],
                       cwd=ROOT, check=True)
        (grub / 'grub.cfg').write_text(
            'set timeout=0\nmenuentry "PCI read" {\n multiboot2 /boot/test.elf\n boot\n}\n')
        iso = directory / 'fixture.iso'
        with (directory / 'grub.log').open('w') as log:
            subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        capture = directory / 'debug.log'
        capture.unlink(missing_ok=True)
        with tempfile.TemporaryDirectory(prefix='leanos-pci-', dir='/tmp') as tmp:
            monitor = Path(tmp) / 'qmp.sock'
            command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', 'max',
                       '-m', '128', '-smp', '1', '-display', 'none', '-serial', 'none',
                       '-monitor', 'none', '-nic', 'none', '-no-reboot', '-no-shutdown',
                       '-debugcon', f'file:{capture}', '-qmp', f'unix:{monitor},server=on,wait=off',
                       '-cdrom', str(iso)]
            if bridged:
                command += ['-device', 'pci-bridge,id=bridge1,chassis_nr=1,addr=2',
                            '-device', 'pci-bridge,id=bridge2,chassis_nr=2,addr=3',
                            '-device', 'pci-testdev,bus=bridge1,addr=5',
                            '-device', 'pci-testdev,bus=bridge2,addr=6']
            (directory / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
            with (directory / 'qemu.log').open('w') as log:
                process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
                try:
                    deadline = time.monotonic() + 20
                    while True:
                        raw = capture.read_bytes() if capture.exists() else b''
                        if raw.endswith(b'D\n'):
                            break
                        if process.poll() is not None or time.monotonic() >= deadline:
                            raise RuntimeError(f'{name}: incomplete guest execution: {raw!r}')
                        time.sleep(0.05)
                    qmp = query_pci(monitor)
                    (directory / 'query-pci.json').write_text(json.dumps(qmp, indent=2) + '\n')
                    inventory = monitor_inventory(qmp)
                    rejection = None
                    try:
                        validate(raw, inventory, bridged)
                    except ValueError as error:
                        if not (asm_change or header_change):
                            raise
                        rejection = str(error)
                    if rejection != expected_rejections.get(name):
                        raise RuntimeError(f'{name}: unexpected rejection: {rejection!r}')
                    results.append({'case': name, 'rejection': rejection,
                                    'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest(),
                                    'native_sha256': hashlib.sha256((directory / 'read.o').read_bytes()).hexdigest(),
                                    'qmp_device_count': len(inventory)})
                finally:
                    if process.poll() is None:
                        process.terminate()
                    process.wait(timeout=5)
        print('PCI native read:', name, 'PASS')
    report.write_text(json.dumps({
        'compiler': subprocess.check_output([cc, '--version'], text=True).splitlines()[0],
        'qemu': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True).splitlines()[0],
        'results': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
