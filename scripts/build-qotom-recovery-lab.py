#!/usr/bin/env python3
"""Build an explicitly noncanonical Qotom reset experiment from prepared inputs."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import shlex
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--prepared-repo', type=Path, required=True)
p.add_argument('--mode', choices=('completion', 'kernel-hang'), default='completion')
p.add_argument('--pci-diagnostic', action='store_true',
               help='build the PCI diagnostic with completion reset transport')
p.add_argument('--handoff-capture', action='store_true',
               help='retain bounded raw GRUB handoff before PCI diagnostic')
a = p.parse_args()
if a.handoff_capture and not a.pci_diagnostic:
    p.error('--handoff-capture requires --pci-diagnostic')
if a.pci_diagnostic and a.mode != 'completion':
    p.error('--pci-diagnostic requires --mode completion')
root = Path(__file__).resolve().parent.parent
prepared = a.prepared_repo.resolve()
out = root / 'build' / ('qotom-pci-lab' if a.pci_diagnostic else
                       'qotom-lab' if a.mode == 'completion' else 'qotom-kernel-hang')
out.mkdir(parents=True, exist_ok=True)
build = root / 'build' / 'boot'
build.mkdir(parents=True, exist_ok=True)
source = root / 'boot' / 'kernel.c'
if source.read_bytes() != (prepared / 'boot/kernel.c').read_bytes():
    raise SystemExit('prepared kernel source differs; rebuild canonical inputs first')
prepared_graph = (prepared / 'build/boot/generated-image-objects.mk').read_text()
if str(prepared / 'boot/kernel.c') not in prepared_graph:
    raise SystemExit('prepared graph names a different checkout; regenerate it in the prepared repository')
for item in (prepared / 'build/boot').iterdir():
    if item.is_file() and item.suffix in {'.h', '.c', '.mk', '.tsv'}:
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
if a.mode == 'completion':
    text = text.replace(old, (root / 'hardware/lab/qotom-finish.c.inc').read_text())
    text = text.replace('    serial_init();', '    serial_init();\n    serial_puts("LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\\n");')
else:
    text = text.replace('    serial_init();', '''    serial_init();
    serial_puts("LEANOS-LAB/1 KERNEL-HANG stage=before-boot-record interrupts=disabled\\n");
    for (;;) {
        __asm__ volatile ("cli; hlt");
    }''')
if a.handoff_capture:
    marker = 'void kernel_main(uint32_t multiboot_magic, uint32_t multiboot_info) {'
    if text.count(marker) != 1:
        raise SystemExit('unsupported kernel entry shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-handoff.c.inc').read_text() + '\n' + marker)
    text = text.replace('    initialize_early_text(multiboot_magic, multiboot_info);',
                        '    initialize_early_text(multiboot_magic, multiboot_info);\n    lab_capture_handoff(multiboot_magic, multiboot_info);')
overlay = out / 'kernel.c'
overlay.write_text(text)
graph = prepared_graph.replace(str(prepared), str(root))
graph = '\n'.join('IMAGE_CC := gcc -I' + shlex.quote(str(root / 'boot'))
                  if s.startswith('IMAGE_CC :=') else s for s in graph.splitlines()) + '\n'
graph = graph.replace(str(source), str(overlay))
makefile = out / 'objects.mk'
makefile.write_text(graph)
target = build / ('leanos-qotom-pci-diagnostic.elf' if a.pci_diagnostic else 'leanos.elf')
subprocess.run(['make', '-f', str(makefile), '-j4', str(target)], cwd=root, check=True)
elf = out / ('leanos-qotom-lab.elf' if a.mode == 'completion' else 'leanos-qotom-kernel-hang.elf')
shutil.copy2(target, elf)
subprocess.run(['grub-file', '--is-x86-multiboot2', str(elf)], check=True)
files = [source, overlay, Path(__file__).resolve(), makefile, elf]
if a.mode == 'completion':
    files.append(root / 'hardware/lab/qotom-finish.c.inc')
if a.handoff_capture:
    files.extend([root / 'hardware/lab/qotom-handoff.c.inc', root / 'include/boot_handoff_capture.h'])
manifest = {'handoff_capture': a.handoff_capture, 'evidence_class': 'lab-recovery-experiment', 'canonical_halt_evidence': False,
            'mode': a.mode, 'pci_diagnostic': a.pci_diagnostic,
            'recovery_seconds': 30 if a.mode == 'completion' else None, 'hang_recovery': False,
            'source_revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=root, text=True).strip(),
            'source_dirty': bool(subprocess.check_output(['git','status','--porcelain'], cwd=root, text=True)),
            'prepared_revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=prepared, text=True).strip(),
            'compiler': subprocess.check_output(['gcc','--version'], text=True).splitlines()[0],
            'files': {str(f.relative_to(root)): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(elf)
