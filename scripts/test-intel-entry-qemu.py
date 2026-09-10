#!/usr/bin/env python3
"""CPL3 Intel entry-denial execution fixtures; no physical/platform admission."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/intel-entry'


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    report = OUT / 'results.json'
    report.unlink(missing_ok=True)
    source = (ROOT / 'boot/boot.S').read_text()
    start, end = '.global normalize_fast_entry_msrs\n', '.global normalize_extended_state_cr0\n'
    if source.count(start) != 1 or source.count(end) != 1:
        raise RuntimeError('production normalization boundaries are not unique')
    block = source.split(start, 1)[1].split(end, 1)[0]
    if block.count('    wrmsr\n') != 8:
        raise RuntimeError('production normalization must contain eight reviewed MSR writes')
    normalization = start + block
    (OUT / 'normalization.inc').write_text(normalization)
    cc = os.environ.get('LEANOS_CC', 'gcc')
    cases = [('syscall', 0, [], 33, b'R6P'), ('sysenter', 1, [], 33, b'RGP'),
             ('amd-vector-rejected', 1, ['-DEXPECTED_VECTOR=6'], 35, b'RF'),
             ('cpl0-origin-rejected', 1, ['-DWRONG_ORIGIN=1'], 35, b'RF')]
    results = []
    for name, probe, extra, expected_status, expected_bytes in cases:
        directory = OUT / name
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        elf = grub.parent / 'test.elf'
        subprocess.run([cc, '-m64', f'-DPROBE={probe}', *extra, '-I' + str(OUT), '-c',
                        'experiments/intel-entry/fixture.S', '-o', str(directory / 'fixture.o')], cwd=ROOT, check=True)
        subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T', 'experiments/intel-entry/fixture.ld',
                        '-o', str(elf), str(directory / 'fixture.o')], cwd=ROOT, check=True)
        (grub / 'grub.cfg').write_text('set timeout=0\nmenuentry "Intel entry fixture" {\n multiboot2 /boot/test.elf\n boot\n}\n')
        iso = directory / 'fixture.iso'
        with (directory / 'grub.log').open('w') as log:
            subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        capture = directory / 'debug.log'
        capture.unlink(missing_ok=True)
        command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg',
                   '-cpu', 'max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off',
                   '-m', '128', '-smp', '1', '-display', 'none', '-serial', 'none', '-monitor', 'none',
                   '-nic', 'none', '-debugcon', f'file:{capture}',
                   '-device', 'isa-debug-exit,iobase=0xf4,iosize=4', '-no-reboot', '-cdrom', str(iso)]
        (directory / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
        with (directory / 'qemu.log').open('w') as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=15)
        raw = capture.read_bytes() if capture.exists() else b''
        if result.returncode != expected_status or raw != expected_bytes:
            raise RuntimeError(f'{name}: exit={result.returncode}, capture={raw!r}')
        results.append({'case': name, 'exit': result.returncode, 'capture': raw.decode('ascii'),
                        'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest()})
        print(f'Intel entry QEMU {name}: PASS', flush=True)
    report.write_text(json.dumps({'scope': 'isolated TCG CPL3 denial; no physical/platform admission',
                                 'normalization_sha256': hashlib.sha256(normalization.encode()).hexdigest(),
                                 'compiler_version': subprocess.check_output([cc, '--version'], text=True),
                                 'qemu_version': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True),
                                 'cases': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
