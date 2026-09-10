#!/usr/bin/env python3
"""Execute the isolated closed-root CPL3 return primitive; never access physical hardware."""
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import socket
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/closed-root-return' / ('qemu-' + Path(os.environ.get('LEANOS_CC', 'gcc')).name)


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
    audit = runpy.run_path(str(ROOT / 'scripts/check-closed-root-return.py'))['check']
    cc = os.environ.get('LEANOS_CC', 'gcc')
    subprocess.run([cc, '-m64', '-c', 'experiments/copy-roots/return.S', '-o', str(OUT / 'return.o')], cwd=ROOT, check=True)
    cases = list(enumerate(['returns', 'zero-root', 'unaligned-root', 'outside-arena',
                           'pge', 'pcid', 'interrupts-enabled', 'not-closed', 'same-root']))
    exit_cases = {'returns': (33, b'RP'), 'wrong-register': (35, b'RF'),
                  'nmi-before-restore': (33, b'RIN'), 'nmi-before-iret': (33, b'RIN')}
    source = (ROOT / 'experiments/copy-roots/return.S').read_text()
    checkpoint = "    mov $'I', %al\n    out %al, $0xe9\n99: pause\n    jmp 99b\n"
    mutations = {
        'wrong-register': ('    pop %r15', '    pop %r14'),
        'missing-reload': ('    mov %rdi, %cr3', '    nop'),
        'readback-mismatch': ('    mov %cr3, %rax\n    cmp %rdi',
                              '    xor %eax, %eax\n    cmp %rdi'),
        'nmi-before-restore': ('    pop %r15', checkpoint + '    pop %r15'),
        'nmi-before-iret': ('    iretq', checkpoint + '    iretq'),
    }
    for name, (old, new) in mutations.items():
        if source.count(old) != 1:
            raise RuntimeError(f'mutation no longer unique: {name}')
        asm = OUT / (name + '.S')
        asm.write_text(source.replace(old, new))
        subprocess.run([cc, '-m64', '-c', str(asm), '-o', str(OUT / (name + '.o'))], check=True)
        cases.append((0, name))
    for number, name in cases:
        directory = OUT / name
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        elf = grub.parent / 'test.elf'
        (directory / 'terminal-registers.txt').unlink(missing_ok=True)
        reload_object = OUT / ((name if name in mutations else 'return') + '.o')
        subprocess.run([cc, '-m64', f'-DFIXTURE={number}', '-c', 'experiments/copy-roots/return-fixture.S',
                        '-o', str(directory / 'fixture.o')], cwd=ROOT, check=True)
        subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T', 'experiments/copy-roots/fixture.ld',
                        '-o', str(elf), str(directory / 'fixture.o'), str(reload_object)], cwd=ROOT, check=True)
        if name == 'returns':
            audit(elf, within_bundle=True)
        symbols = subprocess.check_output(['nm', '-S', str(elf)], text=True)
        terminal = next(line.split() for line in symbols.splitlines() if line.endswith(' leanos_closed_root_return_terminal'))
        terminal_start, terminal_size = int(terminal[0], 16), int(terminal[1], 16)
        (grub / 'grub.cfg').write_text('set timeout=0\nmenuentry "copy-root test" {\n multiboot2 /boot/test.elf\n boot\n}\n')
        iso = directory / 'fixture.iso'
        with (directory / 'grub.log').open('w') as log:
            subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)], stdout=log, stderr=subprocess.STDOUT, check=True)
        # UNIX socket limits apply even when artifact paths themselves are valid.
        with tempfile.TemporaryDirectory(prefix='leanos-root-', dir='/tmp') as socket_dir:
            capture = directory / 'debug.log'
            capture.unlink(missing_ok=True)
            monitor = Path(socket_dir) / 'qmp.sock'
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
                        if name.startswith('nmi-') and not injected_nmi and raw == b'RI' and status is None and monitor.exists():
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
                        'reload_object_sha256': hashlib.sha256(reload_object.read_bytes()).hexdigest(),
                        'register_bank_words': 20})
        print(f'closed-root return QEMU {name}: PASS', flush=True)
    report.write_text(json.dumps({'scope': 'isolated QEMU TCG CPL3 return; no production or physical admission',
                                 'compiler_version': subprocess.check_output([cc, '--version'], text=True),
                                 'qemu_version': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True),
                                 'cases': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
