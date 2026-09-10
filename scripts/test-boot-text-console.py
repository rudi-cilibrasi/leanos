#!/usr/bin/env python3
"""Compile the console geometry boundary and exercise its bounded C writer."""
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
out = root / 'build/text-console'
out.mkdir(parents=True, exist_ok=True)
subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '-c',
                str(out / 'BootTextConsole.c'), 'LeanOS/BootTextConsole.lean'], cwd=root, check=True)
prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=root, text=True).strip()
cc = os.environ.get('LEANOS_HOST_CC', 'gcc-13')
for mode, sanitizer in [('ordinary', []), ('sanitized', ['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-fno-sanitize-recover=all'])]:
    objects = []
    for name, source in [('gate', out / 'BootTextConsole.c'), ('test', root / 'tests/boot-text-console.c')]:
        obj = out / (mode + '-' + name + '.o')
        subprocess.run([cc, '-O1', '-g', '-ffunction-sections', '-fdata-sections',
                        '-I' + prefix + '/include', '-I' + str(root / 'include'),
                        *sanitizer, '-c', str(source), '-o', str(obj)], check=True)
        objects.append(str(obj))
    exe = out / mode
    if sanitizer:
        subprocess.run(['bash', '-c', 'source scripts/hosted-sanitizer-config.sh; leanos_link_sanitized_host "$@"',
                        'console-link', str(exe), *objects], cwd=root, check=True)
        subprocess.run(['bash', '-c', 'source scripts/hosted-sanitizer-config.sh; leanos_run_sanitized "$@"',
                        'console-run', str(exe)], cwd=root, check=True)
    else:
        subprocess.run(['lake', 'env', 'leanc', '-Wl,--gc-sections', *objects, '-o', str(exe)], cwd=root, check=True)
        subprocess.run([str(exe)], check=True)
compiler = os.environ.get('LEANOS_CC', 'gcc')
flags = ['-m64', '-O2', '-ffreestanding', '-fno-stack-protector', '-fno-pic',
         '-mno-red-zone', '-mgeneral-regs-only', '-ffunction-sections', '-fdata-sections']
if 'clang' in subprocess.check_output([compiler, '--version'], text=True).lower():
    flags += ['-ffp-eval-method=source', '-Wno-error=pragmas', '-fno-jump-tables']
obj = out / 'freestanding.o'
subprocess.run([compiler, *flags, '-I' + prefix + '/include', '-c',
                str(out / 'BootTextConsole.c'), '-o', str(obj)], check=True)
elf = out / 'freestanding.elf'
subprocess.run(['ld', '--gc-sections', '-e', 'leanos_boot_text_surface', str(obj), '-o', str(elf)], check=True)
assert not subprocess.check_output(['nm', '-u', str(elf)]).strip(), 'console selector depends on runtime'
print('Boot text freestanding selector has no unresolved runtime dependencies')
