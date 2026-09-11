#!/usr/bin/env python3
"""Execute native control reads and invalidation against isolated RAM mappings."""
import hashlib
import json
from pathlib import Path
import subprocess
import runpy

ROOT = Path(__file__).resolve().parents[1]


def main():
    out = ROOT / 'build/qotom-ecam-native-qemu'
    grub = out / 'iso/boot/grub'
    grub.mkdir(parents=True, exist_ok=True)
    result = out / 'results.json'
    result.unlink(missing_ok=True)
    objects = []
    for source, name in [('experiments/ecam-native/fixture.S', 'entry'),
                         ('experiments/ecam-native/fixture.c', 'fixture'),
                         ('hardware/lab/qotom-ecam-native.S', 'native')]:
        obj = out / (name + '.o')
        subprocess.run(['gcc', '-m64', '-O2', '-Wall', '-Wextra', '-Werror',
                        '-ffreestanding', '-fno-builtin', '-fno-stack-protector',
                        '-fno-pie', '-mno-red-zone', '-mgeneral-regs-only',
                        '-Ihardware/lab', '-c', source, '-o', str(obj)], cwd=ROOT, check=True)
        objects.append(str(obj))
    runpy.run_path(str(ROOT / 'scripts/check-qotom-ecam-native.py'))['check'](out / 'native.o')
    elf = grub.parent / 'test.elf'
    subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T',
                    'experiments/ecam-native/fixture.ld', '-o', str(elf), *objects], cwd=ROOT, check=True)
    (grub / 'grub.cfg').write_text('set timeout=0\nmenuentry "ECAM primitives" {\n multiboot2 /boot/test.elf\n boot\n}\n')
    iso = out / 'fixture.iso'
    with (out / 'grub.log').open('w') as log:
        subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    results = []
    for name, cpu, expected in [
        ('available', 'max', b'PASS controls=matched remap=observed restore=invalidated\n'),
        ('missing-pat', 'max,pat=off', b'UNAVAILABLE output=unchanged\n')]:
        capture = out / (name + '.raw')
        capture.unlink(missing_ok=True)
        command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', cpu,
                   '-m', '32', '-smp', '1', '-display', 'none', '-serial', 'none',
                   '-monitor', 'none', '-nic', 'none', '-no-reboot',
                   '-debugcon', f'file:{capture}', '-device', 'isa-debug-exit,iobase=0xf4,iosize=4',
                   '-cdrom', str(iso)]
        with (out / (name + '.log')).open('w') as log:
            completed = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=30)
        raw = capture.read_bytes()
        if completed.returncode != 1 or raw != expected:
            raise RuntimeError(f'{name}: exit={completed.returncode} capture={raw!r}')
        results.append({'case': name, 'command': command, 'capture_sha256': hashlib.sha256(raw).hexdigest()})
    result.write_text(json.dumps({'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest(),
        'cases': results, 'physical_ecam_validated': False}, indent=2) + '\n')
    print('Native ECAM QEMU: control reads, RAM remapping/invalidation and missing-PAT gate PASS')


if __name__ == '__main__':
    main()
