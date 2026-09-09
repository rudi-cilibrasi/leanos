#!/usr/bin/env python3
"""Build an explicitly noncanonical Qotom reset experiment from prepared inputs."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--prepared-repo', type=Path, required=True)
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
prepared = a.prepared_repo.resolve()
out = root / 'build' / 'qotom-lab'
out.mkdir(parents=True, exist_ok=True)
build = root / 'build' / 'boot'
build.mkdir(parents=True, exist_ok=True)
source = root / 'boot' / 'kernel.c'
if source.read_bytes() != (prepared / 'boot/kernel.c').read_bytes():
    raise SystemExit('prepared kernel source differs; rebuild canonical inputs first')
for item in (prepared / 'build/boot').iterdir():
    if item.is_file() and item.suffix in {'.h', '.c', '.mk'}:
        shutil.copy2(item, build / item.name)
text = source.read_text()
old = '''static __attribute__((noreturn)) void finish(uint8_t value) {
    out8(DEBUG_EXIT, value);
    for (;;) {
        __asm__ volatile ("cli; hlt");
    }
}'''
if text.count(old) != 1 or text.count('    serial_init();') != 1:
    raise SystemExit('unsupported kernel terminal/init shape')
text = text.replace(old, (root / 'hardware/lab/qotom-finish.c.inc').read_text())
text = text.replace('    serial_init();', '    serial_init();\n    serial_puts("LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\\n");')
overlay = out / 'kernel.c'
overlay.write_text(text)
graph = (build / 'generated-image-objects.mk').read_text().replace(str(prepared), str(root))
graph = '\n'.join('IMAGE_CC := gcc' if s.startswith('IMAGE_CC :=') else s for s in graph.splitlines()) + '\n'
graph = graph.replace(str(source), str(overlay))
makefile = out / 'objects.mk'
makefile.write_text(graph)
subprocess.run(['make', '-f', str(makefile), '-j4', str(build / 'leanos.elf')], cwd=root, check=True)
elf = out / 'leanos-qotom-lab.elf'
shutil.copy2(build / 'leanos.elf', elf)
subprocess.run(['grub-file', '--is-x86-multiboot2', str(elf)], check=True)
files = [source, overlay, root / 'hardware/lab/qotom-finish.c.inc', elf]
manifest = {'evidence_class': 'lab-recovery-experiment', 'canonical_halt_evidence': False,
            'recovery_seconds': 30, 'hang_recovery': False,
            'source_revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=root, text=True).strip(),
            'files': {str(f.relative_to(root)): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(elf)
