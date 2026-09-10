#!/usr/bin/env python3
"""Execute bounded copies and prove closure by a deliberate post-return fault."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/copy-roots/transfer-qemu'


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
    for count in (0, 1, 8, 16):
        directory = OUT / str(count)
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        elf = grub.parent / 'test.elf'
        obj = directory / 'fixture.o'
        subprocess.run([cc, '-m64', '-DFIXTURE=7', '-DTRANSFER_FIXTURE', f'-DTRANSFER_COUNT={count}',
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
        with (directory / 'qemu.log').open('w') as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=20)
        raw = capture.read_bytes()
        if result.returncode != 33 or raw != b'RTP':
            raise RuntimeError(f'count {count}: exit {result.returncode}, capture {raw!r}')
        results.append({'count': count, 'exit': result.returncode, 'capture': raw.decode(),
                        'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest()})
        print(f'copy-root transfer {count} bytes: PASS', flush=True)
    sources = ['experiments/copy-roots/'+name for name in ('fixture.S', 'fixture.ld', 'transfer-fixture.inc', 'reload.S', 'transfer.S')]
    report.write_text(json.dumps({'scope': 'isolated no-SMAP TCG copy-in and post-return closure; no production admission',
        'cases': results, 'sources': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
        'compiler': subprocess.check_output([cc, '--version'], text=True),
        'qemu': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True)}, indent=2)+'\n')


if __name__ == '__main__':
    main()
