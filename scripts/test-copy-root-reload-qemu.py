#!/usr/bin/env python3
"""Execute the isolated root-reload prototype; never access physical hardware."""
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/copy-roots/qemu'


def qmp_command(path, command=None):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.settimeout(2)
        sock.connect(str(path))
        stream = sock.makefile('rwb')
        json.loads(stream.readline())
        for command in [{'execute': 'qmp_capabilities'},
                        command or {'execute': 'human-monitor-command', 'arguments': {'command-line': 'info registers'}}]:
            stream.write((json.dumps(command) + '\n').encode())
            stream.flush()
            while True:
                response = json.loads(stream.readline())
                if 'error' in response:
                    raise RuntimeError(response['error'])
                if 'return' in response:
                    break
        return response['return']


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    report = OUT / 'results.json'
    report.unlink(missing_ok=True)
    results = []
    cc = os.environ.get('LEANOS_CC', 'gcc')
    subprocess.run([cc, '-m64', '-c', 'experiments/copy-roots/reload.S', '-o', str(OUT / 'reload.o')], cwd=ROOT, check=True)
    mutation = OUT / 'missing-reload.S'
    source = (ROOT / 'experiments/copy-roots/reload.S').read_text()
    needle = '    mov %rdi, %cr3'
    if source.count(needle) != 1:
        raise RuntimeError('missing-reload mutation no longer applies uniquely')
    mutation.write_text(source.replace(needle, '    nop'))
    subprocess.run([cc, '-m64', '-c', str(mutation), '-o', str(OUT / 'missing-reload.o')], check=True)
    cases = list(enumerate(['reloads', 'zero-root', 'unaligned-root', 'outside-arena', 'pge', 'pcid', 'interrupts-enabled']))
    readback = OUT / 'readback-mismatch.S'
    needle = '    mov %cr3, %rax'
    if source.count(needle) != 1:
        raise RuntimeError('readback mutation no longer applies uniquely')
    readback.write_text(source.replace(needle, '    xor %eax, %eax'))
    subprocess.run([cc, '-m64', '-c', str(readback), '-o', str(OUT / 'readback-mismatch.o')], check=True)
    cases.extend([(0, 'missing-reload'), (7, 'closed-denial'), (8, 'readback-mismatch'), (9, 'nmi-closure'), (10, 'identity-denial')])
    exit_cases = {'reloads': (33, b'RSTP'), 'missing-reload': (35, b'RF'), 'closed-denial': (33, b'RDP'), 'nmi-closure': (33, b'RNP'), 'identity-denial': (33, b'RDP')}
    for number, name in cases:
        directory = OUT / name
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        elf = grub.parent / 'test.elf'
        (directory / 'terminal-registers.txt').unlink(missing_ok=True)
        reload_object = OUT / (name + '.o' if name in {'missing-reload', 'readback-mismatch'} else 'reload.o')
        subprocess.run([cc, '-m64', f'-DFIXTURE={number}', '-c', 'experiments/copy-roots/fixture.S',
                        '-o', str(directory / 'fixture.o')], cwd=ROOT, check=True)
        subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T', 'experiments/copy-roots/fixture.ld',
                        '-o', str(elf), str(directory / 'fixture.o'), str(reload_object)], cwd=ROOT, check=True)
        symbols = subprocess.check_output(['nm', '-S', str(elf)], text=True)
        terminal = next(line.split() for line in symbols.splitlines() if line.endswith(' leanos_copy_root_terminal'))
        terminal_start, terminal_size = int(terminal[0], 16), int(terminal[1], 16)
        (grub / 'grub.cfg').write_text('set timeout=0\nmenuentry "copy-root test" {\n multiboot2 /boot/test.elf\n boot\n}\n')
        iso = directory / 'fixture.iso'
        with (directory / 'grub.log').open('w') as log:
            subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)], stdout=log, stderr=subprocess.STDOUT, check=True)
        capture, monitor = directory / 'debug.log', directory / 'qmp.sock'
        monitor.unlink(missing_ok=True)
        command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', 'max,smap=off',
                   '-m', '128', '-smp', '1', '-display', 'none', '-serial', 'none', '-monitor', 'none', '-nic', 'none',
                   '-debugcon', f'file:{capture}', '-qmp', f'unix:{monitor},server=on,wait=off',
                   '-device', 'isa-debug-exit,iobase=0xf4,iosize=4', '-no-reboot', '-cdrom', str(iso)]
        (directory / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
        with (directory / 'qemu.log').open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 15
                injected_nmi = False
                while True:
                    raw = capture.read_bytes() if capture.exists() else b''
                    status = process.poll()
                    if name == 'nmi-closure' and not injected_nmi and raw == b'R' and status is None and monitor.exists():
                        qmp_command(monitor, {'execute': 'inject-nmi'})
                        injected_nmi = True
                    if name in exit_cases and status is not None:
                        expected_status, expected_raw = exit_cases[name]
                        if status != expected_status or raw != expected_raw:
                            raise RuntimeError(f'{name}: exit={status}, capture={raw!r}')
                        observation = {'kind': 'exit', 'status': status, 'injected_nmi': injected_nmi}
                        break
                    if name not in exit_cases and raw == b'R' and status is None and monitor.exists():
                        registers = qmp_command(monitor)
                        match = re.search(r'RIP=([0-9a-fA-F]+)', registers)
                        if match and terminal_start <= int(match[1], 16) < terminal_start + terminal_size and 'HLT=1' in registers:
                            (directory / 'terminal-registers.txt').write_text(registers)
                            observation = {'kind': 'terminal', 'rip': int(match[1], 16), 'halted': True}
                            break
                    if status is not None or time.monotonic() >= deadline:
                        raise RuntimeError(f'{name}: did not reach expected terminal; exit={status}, capture={raw!r}')
                    time.sleep(0.05)
            finally:
                if process.poll() is None:
                    process.terminate()
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
        results.append({'case': name, 'observation': observation,
                        'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest(),
                        'capture': capture.read_text(),
                        'reload_object_sha256': hashlib.sha256(reload_object.read_bytes()).hexdigest()})
        print(f'copy-root QEMU {name}: PASS', flush=True)
    report.write_text(json.dumps({'scope': 'isolated QEMU TCG prototype; no physical or CPL3 admission',
                                 'compiler_version': subprocess.check_output([cc, '--version'], text=True),
                                 'qemu_version': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True),
                                 'cases': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
