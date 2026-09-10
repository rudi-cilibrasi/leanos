#!/usr/bin/env python3
"""Compile the console geometry boundary and exercise its bounded C writer."""
import argparse
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
out = root / 'build/text-console'
out.mkdir(parents=True, exist_ok=True)
subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '-c',
                str(out / 'BootTextConsole.c'), 'LeanOS/BootTextConsole.lean'], cwd=root, check=True)
prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=root, text=True).strip()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--freestanding-only', action='store_true')
args = parser.parse_args()
if not args.freestanding_only:
    env = dict(os.environ, LEANOS_HOSTED_BOUNDARY_ID='boot-text')
    for mode in ['ordinary', 'sanitized']:
        subprocess.run(['./scripts/check-boot-handoff-host.sh', mode],
                       cwd=root, env=env, check=True)
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
