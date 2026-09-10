#!/usr/bin/env python3
"""Execute bounded copies and prove closure by a deliberate post-return fault."""
import hashlib
import importlib.util
import re
import tempfile
import time
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/copy-roots' / ('transfer-qemu-' + Path(os.environ.get('LEANOS_CC', 'gcc')).name)


def observe_rejection(command, directory, capture, elf, direction):
    spec = importlib.util.spec_from_file_location('reload_test', ROOT / 'scripts/test-copy-root-reload-qemu.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    symbols = {}
    for line in subprocess.check_output(['nm', '-S', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) in (3, 4):
            symbols[fields[-1]] = (int(fields[0], 16), int(fields[1], 16) if len(fields) == 4 else 0)
    terminal, size = symbols['leanos_copy_root_terminal']
    closed = symbols['root_b'][0]
    with tempfile.TemporaryDirectory(prefix='leanos-transfer-', dir='/tmp') as temp:
        monitor = Path(temp) / 'qmp.sock'
        command = command + ['-qmp', f'unix:{monitor},server=on,wait=off']
        (directory / 'command.json').write_text(json.dumps(command, indent=2)+'\n')
        with (directory / 'qemu.log').open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 20
                while True:
                    raw = capture.read_bytes() if capture.exists() else b''
                    if process.poll() is not None or time.monotonic() >= deadline:
                        raise RuntimeError(f'oversize did not halt: {process.poll()}, {raw!r}')
                    if raw == b'R' and monitor.exists():
                        registers = module.qmp_command(monitor)
                        rip = re.search(r'RIP=([0-9a-fA-F]+)', registers)
                        cr3 = re.search(r'CR3=([0-9a-fA-F]+)', registers)
                        if rip and terminal <= int(rip[1], 16) < terminal + size and 'HLT=1' in registers:
                            if not cr3 or int(cr3[1], 16) != closed:
                                raise RuntimeError('oversize halted without the closed root')
                            (directory / 'terminal-registers.txt').write_text(registers)
                            break
                    time.sleep(0.05)
                pattern = bytes(range(0x10, 0x20))
                expected_kernel = bytes([0xa5])*8 + pattern + bytes([0xa5])*8 if direction else bytes([0xa5])*32
                expected_user = bytes([0xa5])*32 if direction else bytes([0xa5])*8+pattern+bytes([0xa5])*8
                hashes = {}
                for name, address, expected in (
                    ('kernel', symbols['transfer_buffer'][0], expected_kernel),
                    ('user', symbols['value_a'][0]+4080, expected_user),
                ):
                    dump = directory / (name + '-after.bin')
                    dump.unlink(missing_ok=True)
                    response = module.qmp_command(monitor, {'execute': 'human-monitor-command',
                        'arguments': {'command-line': f'pmemsave {address:#x} 32 {json.dumps(str(dump))}'}})
                    if response.strip():
                        raise RuntimeError(f'physical dump failed: {response}')
                    actual = dump.read_bytes()
                    if actual != expected:
                        raise RuntimeError(f'oversize mutated {name} bytes: {actual.hex()}')
                    hashes[name] = hashlib.sha256(actual).hexdigest()
                return {'kind': 'terminal', 'halted': True, 'closed_root': closed, 'memory_sha256': hashes}
            finally:
                process.terminate()
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    report = OUT / 'results.json'
    report.unlink(missing_ok=True)
    cc = os.environ.get('LEANOS_CC', 'gcc')
    objects = []
    for name in ('reload', 'transfer'):
        obj = OUT / (name + '.o')
        subprocess.run([cc, '-m64', '-c', f'experiments/copy-roots/{name}.S', '-o', str(obj)], cwd=ROOT, check=True)
        objects.append(str(obj))
    results = []
    for direction, count in ((d, n) for d in (0, 1) for n in (0, 1, 8, 16, 17)):
        directory = OUT / f'{direction}-{count}'
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        elf = grub.parent / 'test.elf'
        obj = directory / 'fixture.o'
        subprocess.run([cc, '-m64', '-DFIXTURE=7', '-DTRANSFER_FIXTURE', f'-DTRANSFER_COUNT={count}', f'-DCOPY_OUT={direction}',
                        '-c', 'experiments/copy-roots/fixture.S', '-o', str(obj)], cwd=ROOT, check=True)
        subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T', 'experiments/copy-roots/fixture.ld',
                        '-o', str(elf), str(obj), *objects], cwd=ROOT, check=True)
        (grub / 'grub.cfg').write_text('set timeout=0\nmenuentry "copy transfer" {\n multiboot2 /boot/test.elf\n boot\n}\n')
        iso = directory / 'fixture.iso'
        with (directory / 'grub.log').open('w') as log:
            subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)], stdout=log, stderr=subprocess.STDOUT, check=True)
        capture = directory / 'debug.log'
        capture.unlink(missing_ok=True)
        command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', 'max,smap=off',
                   '-m', '128', '-smp', '1', '-display', 'none', '-serial', 'none', '-monitor', 'none', '-nic', 'none',
                   '-debugcon', f'file:{capture}', '-device', 'isa-debug-exit,iobase=0xf4,iosize=4',
                   '-no-reboot', '-cdrom', str(iso)]
        (directory / 'command.json').write_text(json.dumps(command, indent=2)+'\n')
        if count > 16:
            observation = observe_rejection(command, directory, capture, elf, direction)
        else:
            with (directory / 'qemu.log').open('w') as log:
                result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=20)
            raw = capture.read_bytes()
            if result.returncode != 33 or raw != b'RTP':
                raise RuntimeError(f'count {count}: exit {result.returncode}, capture {raw!r}')
            observation = {'kind': 'exit', 'exit': result.returncode}
        results.append({'direction': 'out' if direction else 'in', 'count': count,
                        'observation': observation, 'capture': capture.read_text(),
                        'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest()})
        print(f'copy-root transfer direction={direction} {count} bytes: PASS', flush=True)
    sources = ['experiments/copy-roots/'+name for name in ('fixture.S', 'fixture.ld', 'transfer-fixture.inc', 'reload.S', 'transfer.S')]
    report.write_text(json.dumps({'scope': 'isolated no-SMAP TCG copy-in/copy-out and post-return closure; no production admission',
        'cases': results, 'sources': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
        'compiler': subprocess.check_output([cc, '--version'], text=True),
        'qemu': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True)}, indent=2)+'\n')


if __name__ == '__main__':
    main()
