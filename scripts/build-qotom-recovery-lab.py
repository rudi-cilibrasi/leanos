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
p.add_argument('--acpi-capture', action='store_true', help='copy and retain root-selected ACPI tables')
p.add_argument('--pci-read-trace', action='store_true')
p.add_argument('--bootstrap-capture', action='store_true')
p.add_argument('--ecam-memory-capture', action='store_true')
p.add_argument('--dsdt-capture', action='store_true')
p.add_argument('--ecam-read', action='store_true', help='use firmware-gated ECAM for the lab PCI scan')
p.add_argument('--native-inventory', action='store_true', help='check the complete native PCI snapshot in the ECAM lab image')
p.add_argument('--bsp-topology', action='store_true', help='bind root-selected MADT entries to a fresh BSP observation')
p.add_argument('--pci-capabilities', action='store_true', help='capture bounded conventional capability lists after native inventory acceptance')
p.add_argument('--af-observation', action='store_true', help='observe AF control/status after native capability capture')
p.add_argument('--ehci-capabilities', action='store_true', help='read native EHCI capability registers through a separate window')
p.add_argument('--ehci-handoff', action='store_true', help='request bounded cooperative EHCI firmware handoff')
p.add_argument('--ehci-legacy', action='store_true', help='observe bounded EHCI extended list and legacy control/status')
a = p.parse_args()
if a.ehci_handoff and not a.ehci_legacy:
    p.error('--ehci-handoff requires --ehci-legacy')
if a.ehci_legacy and not a.ehci_capabilities:
    p.error('--ehci-legacy requires --ehci-capabilities')
if a.ehci_capabilities and not a.af_observation:
    p.error('--ehci-capabilities requires --af-observation')
if a.af_observation and not a.pci_capabilities:
    p.error('--af-observation requires --pci-capabilities')
if a.pci_capabilities and not a.native_inventory:
    p.error('--pci-capabilities requires --native-inventory')
if a.bsp_topology and not a.native_inventory:
    p.error('--bsp-topology requires --native-inventory')
if a.native_inventory and not a.ecam_read:
    p.error('--native-inventory requires --ecam-read')
if a.ecam_read and (not a.dsdt_capture or not a.ecam_memory_capture or a.pci_read_trace):
    p.error('--ecam-read requires --dsdt-capture and --ecam-memory-capture, and excludes --pci-read-trace')
if a.dsdt_capture and not a.acpi_capture:
    p.error('--dsdt-capture requires --acpi-capture')
if a.ecam_memory_capture and not a.bootstrap_capture:
    p.error('--ecam-memory-capture requires --bootstrap-capture')
if a.bootstrap_capture and not a.pci_diagnostic:
    p.error('--bootstrap-capture requires --pci-diagnostic')
if a.pci_read_trace and not a.pci_diagnostic:
    p.error('--pci-read-trace requires --pci-diagnostic')
if a.acpi_capture and not a.handoff_capture:
    p.error('--acpi-capture requires --handoff-capture')
if a.handoff_capture and not a.pci_diagnostic:
    p.error('--handoff-capture requires --pci-diagnostic')
if a.pci_diagnostic and a.mode != 'completion':
    p.error('--pci-diagnostic requires --mode completion')
root = Path(__file__).resolve().parent.parent
prepared = a.prepared_repo.resolve()
out = root / 'build' / ('qotom-handoff-lab' if a.ehci_handoff else 'qotom-legacy-lab' if a.ehci_legacy else
                       'qotom-ehci-lab' if a.ehci_capabilities else
                       'qotom-af-lab' if a.af_observation else
                       'qotom-capabilities-lab' if a.pci_capabilities else
                       'qotom-bsp-lab' if a.bsp_topology else
                       'qotom-pci-lab' if a.pci_diagnostic else
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
if a.ehci_handoff:
    text = '#define LEANOS_QOTOM_EHCI_HANDOFF 1\n' + text
if a.ehci_legacy:
    text = '#define LEANOS_QOTOM_EHCI_LEGACY 1\n' + text
if a.af_observation:
    text = '#define LEANOS_QOTOM_AF_OBSERVATION 1\n' + text
if a.ecam_read:
    text = '#define LEANOS_LAB_ECAM_READ 1\n' + text
if a.dsdt_capture:
    text = '#define LEANOS_LAB_DSDT_CAPTURE 1\n' + text
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
if a.acpi_capture:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    text = text.replace(marker, 'static uint32_t lab_mb2_magic, lab_mb2_address;\nstatic void lab_capture_acpi(void);\n' + marker)
    gate = '    if (result != 1) pre_admission_fail("j1900-msr-readback");'
    if text.count(gate) != 1:
        raise SystemExit('unsupported CPU/MSR gate shape')
    text = text.replace(gate, gate + '\n    lab_capture_acpi();')
    marker = 'void kernel_main(uint32_t multiboot_magic, uint32_t multiboot_info) {'
    text = text.replace(marker, (root / 'hardware/lab/qotom-acpi.c.inc').read_text() + '\n' + marker)
    text = text.replace('    lab_capture_handoff(multiboot_magic, multiboot_info);',
                        '    lab_mb2_magic = multiboot_magic; lab_mb2_address = multiboot_info;\n    lab_capture_handoff(multiboot_magic, multiboot_info);')
if a.pci_read_trace:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    call = 'pci_enumerate_segment(pci_config_read, 0, &snapshot);'
    if text.count(marker) != 1 or text.count(call) != 1:
        raise SystemExit('unsupported PCI diagnostic shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-pci-read-trace.c.inc').read_text() + '\n' + marker)
    text = text.replace(call, 'pci_enumerate_segment(lab_pci_read, 0, &snapshot);\n    lab_report_pci_read();')
if a.bootstrap_capture:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    gate = '    if (result != 1) pre_admission_fail("j1900-msr-readback");'
    if text.count(marker) != 1 or text.count(gate) != 1:
        raise SystemExit('unsupported CPU/MSR bootstrap gate shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-bootstrap.c.inc').read_text() + '\n' + marker)
    text = text.replace(gate, gate + '\n    lab_capture_bootstrap((uint32_t)w[9]);')
if a.ecam_memory_capture:
    marker = 'static void lab_capture_bootstrap(uint32_t cpuid_edx) {'
    call = '    lab_capture_bootstrap((uint32_t)w[9]);'
    if text.count(marker) != 1 or text.count(call) != 1:
        raise SystemExit('unsupported ECAM memory capture shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-ecam-memory.c.inc').read_text() + '\n' + marker)
    text = text.replace(call, call + '\n    lab_capture_ecam_memory((uint32_t)w[9]);')
if a.ecam_read:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    call = 'pci_enumerate_segment(pci_config_read, 0, &snapshot);'
    gate = '    lab_capture_acpi();'
    if text.count(marker) != 1 or text.count(call) != 1 or text.count(gate) != 1:
        raise SystemExit('unsupported ECAM diagnostic shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-ecam.c.inc').read_text() + '\n' + marker)
    text = text.replace(gate, gate + '\n    lab_prepare_ecam();')
    text = text.replace(call, 'pci_enumerate_segment(qotom_ecam_read, &lab_ecam_reader, &snapshot);\n    lab_ecam_window.armed = 0;')
    subprocess.run(['python3', 'scripts/generate-qotom-ecam-firmware.py',
                    str(build / 'qotom-ecam-firmware-inputs.h')], cwd=root, check=True)
if a.native_inventory:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    stop = '#endif\n    pre_admission_fail("qotom-platform-pending");'
    if text.count(marker) != 1 or text.count(stop) != 1:
        raise SystemExit('unsupported native inventory diagnostic shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-native-inventory.c.inc').read_text() + '\n' + marker)
    text = text.replace(stop, '    lab_check_native_inventory(scan.status, &snapshot);\n' + stop)
    native_pci_dir = out / 'native-pci'
    subprocess.run(['scripts/build-qotom-native-pci-object.sh', str(native_pci_dir)], cwd=root, check=True)
    native_pci = native_pci_dir / 'native-pci.o'
    # Prepared canonical inputs predate this export; refresh the generated ABI.
    shutil.copy2(root / 'build/boundary-abi/boundary-abi.h', build / 'boundary-abi.h')
if a.pci_capabilities:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    call = '    lab_check_native_inventory(scan.status, &snapshot);'
    if text.count(marker) != 1 or text.count(call) != 1:
        raise SystemExit('unsupported capability collection shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-pci-capabilities.c.inc').read_text() + '\n' + marker)
    text = text.replace(call, call + '\n    lab_capture_pci_capabilities(&snapshot);')
if a.ehci_capabilities:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    call = '    lab_capture_pci_capabilities(&snapshot);'
    if text.count(marker) != 1 or text.count(call) != 1:
        raise SystemExit('unsupported EHCI collection shape')
    text = text.replace(marker, (root / 'hardware/lab/qotom-ehci.c.inc').read_text() + '\n' + marker)
    text = text.replace(call, call + '\n    lab_capture_ehci(&snapshot);')
if a.bsp_topology:
    marker = 'static __attribute__((noinline, noipa)) void report_j1900_cpu_candidate(void) {'
    end = '    serial_puts("LEANOS-LAB/1 ACPI-END\\n");'
    if text.count(marker) != 1 or text.count(end) != 1:
        raise SystemExit('unsupported BSP copy-consumer shape')
    text = text.replace(marker, 'static uint32_t lab_bsp_copied_count;\n' +
                        (root / 'hardware/lab/qotom-bsp.c.inc').read_text() + '\n' + marker)
    text = text.replace(end, end + '\n    lab_bsp_copied_count = entries.count;')
    gate = '    lab_prepare_ecam();'
    if text.count(gate) != 1:
        raise SystemExit('unsupported BSP firmware gate shape')
    text = text.replace(gate, gate + '\n    lab_check_bsp(lab_bsp_copied_count);')
    bsp_dir = out / 'bsp'
    subprocess.run(['scripts/build-qotom-bsp-object.sh', str(bsp_dir)], cwd=root, check=True)
    bsp_object = bsp_dir / 'bsp.o'
    shutil.copy2(root / 'build/boundary-abi/boundary-abi.h', build / 'boundary-abi.h')
overlay = out / 'kernel.c'
overlay.write_text(text)
graph = prepared_graph.replace(str(prepared), str(root))
graph = '\n'.join('IMAGE_CC := gcc -I' + shlex.quote(str(root / 'boot'))
                  if s.startswith('IMAGE_CC :=') else s for s in graph.splitlines()) + '\n'
graph = graph.replace(str(source), str(overlay))
if a.ecam_read:
    graph = graph.replace('IMAGE_CC := gcc ', 'IMAGE_CC := gcc -I' + shlex.quote(str(root / 'hardware/lab')) + ' ')
    native = build / 'qotom-ecam-native.o'
    anchor = str(build / 'pci-config-read.o')
    lines = graph.splitlines()
    for i, line in enumerate(lines):
        if ('leanos-qotom-pci-diagnostic-prelink.' in line or
                'leanos-qotom-pci-diagnostic.' in line) and anchor in line:
            lines[i] = line.replace(anchor, anchor + ' ' + str(native))
    graph = '\n'.join(lines) + '\n'
    graph += f'{native}: {root / "hardware/lab/qotom-ecam-native.S"}\n\t$(IMAGE_CC) -m64 -c $< -o $@\n'
if a.native_inventory:
    anchor = str(build / 'pci-config-read.o')
    lines = graph.splitlines()
    inserted = 0
    for i, line in enumerate(lines):
        if ('leanos-qotom-pci-diagnostic-prelink.' in line or
                'leanos-qotom-pci-diagnostic.' in line) and anchor in line:
            lines[i] = line.replace(anchor, anchor + ' ' + str(native_pci))
            inserted += 1
    if inserted < 2:
        raise SystemExit('native inventory object missing prelink/final graph anchors')
    graph = '\n'.join(lines) + '\n'
if a.bsp_topology:
    anchor = str(build / 'pci-config-read.o')
    lines = graph.splitlines()
    inserted = 0
    for i, line in enumerate(lines):
        if ('leanos-qotom-pci-diagnostic-prelink.' in line or
                'leanos-qotom-pci-diagnostic.' in line) and anchor in line:
            lines[i] = line.replace(anchor, anchor + ' ' + str(bsp_object))
            inserted += 1
    if inserted < 2:
        raise SystemExit('BSP object missing prelink/final graph anchors')
    graph = '\n'.join(lines) + '\n'
makefile = out / 'objects.mk'
makefile.write_text(graph)
target = build / ('leanos-qotom-pci-diagnostic.elf' if a.pci_diagnostic else 'leanos.elf')
if a.acpi_capture or a.pci_read_trace or a.bootstrap_capture:
    plan = build / 'boot-page-plan-qotom-pci-diagnostic.h'
    prelink = build / 'leanos-qotom-pci-diagnostic-prelink.elf'
    subprocess.run(['make', '-f', str(makefile), '-j4', str(prelink)], cwd=root, check=True)
    subprocess.run(['scripts/generate-boot-page-plan.sh', str(prelink), str(plan)], cwd=root, check=True)
subprocess.run(['make', '-f', str(makefile), '-j4', str(target)], cwd=root, check=True)
if a.acpi_capture or a.pci_read_trace or a.bootstrap_capture:
    final_plan = out / 'final-page-plan.h'
    subprocess.run(['scripts/generate-boot-page-plan.sh', str(target), str(final_plan)], cwd=root, check=True)
    if final_plan.read_bytes() != plan.read_bytes():
        raise SystemExit('ACPI lab final ELF differs from prelink page plan')
elf = out / ('leanos-qotom-lab.elf' if a.mode == 'completion' else 'leanos-qotom-kernel-hang.elf')
shutil.copy2(target, elf)
subprocess.run(['grub-file', '--is-x86-multiboot2', str(elf)], check=True)
if a.bsp_topology:
    msr_audit = out / 'msr-write-audit.json'
    checked = subprocess.run(['python3', 'scripts/audit-qotom-msr-writes.py', str(elf)],
                             cwd=root, check=True, capture_output=True)
    msr_audit.write_bytes(checked.stdout)
files = [source, overlay, Path(__file__).resolve(), makefile, elf]
if a.ecam_read:
    files.extend([root / 'hardware/lab' / name for name in (
        'qotom-ecam.c.inc', 'qotom-ecam-arm.h', 'qotom-ecam-firmware.h',
        'qotom-ecam-root.h', 'qotom-ecam-window.h', 'qotom-ecam-memory.h',
        'qotom-ecam-native.h', 'qotom-ecam-native.S')])
    files.extend([root / 'boot/qotom-ecam-read.h', build / 'qotom-ecam-firmware-inputs.h', native])
if a.mode == 'completion':
    files.append(root / 'hardware/lab/qotom-finish.c.inc')
if a.handoff_capture:
    files.extend([root / 'hardware/lab/qotom-handoff.c.inc', root / 'include/boot_handoff_capture.h'])
if a.acpi_capture:
    files.append(root / 'hardware/lab/qotom-acpi.c.inc')
if a.pci_read_trace:
    files.append(root / 'hardware/lab/qotom-pci-read-trace.c.inc')
if a.acpi_capture or a.pci_read_trace or a.bootstrap_capture:
    files.extend([plan, final_plan])
if a.bootstrap_capture:
    files.append(root / 'hardware/lab/qotom-bootstrap.c.inc')
if a.ecam_memory_capture:
    files.append(root / 'hardware/lab/qotom-ecam-memory.c.inc')
if a.dsdt_capture:
    files.append(root / 'boot/acpi-dsdt-address.h')
if a.native_inventory:
    files.extend([root / 'hardware/lab/qotom-native-inventory.c.inc',
                  root / 'boot/qotom-native-inventory.h',
                  root / 'scripts/build-qotom-native-pci-object.sh',
                  root / 'LeanOS/PCIHeaderObservation.lean',
                  root / 'LeanOS/QotomNativePCIFields.lean',
                  root / '.lake/build/ir/LeanOS/PCIHeaderObservation.c',
                  root / '.lake/build/ir/LeanOS/QotomNativePCIFields.c',
                  build / 'boundary-abi.h', native_pci, native_pci_dir / 'symbols.txt'])
if a.bsp_topology:
    files.extend([root / 'scripts/audit-qotom-msr-writes.py', msr_audit,
                  root / 'hardware/lab/qotom-bsp.c.inc',
                  root / 'include/qotom_bsp_consumer.h',
                  root / 'scripts/build-qotom-bsp-object.sh',
                  root / 'LeanOS/QotomMadtStream.lean', bsp_dir / 'QotomMadtStream.c',
                  bsp_object, bsp_dir / 'symbols.txt'])
if a.pci_capabilities:
    files.extend([root / 'hardware/lab/qotom-pci-capabilities.c.inc',
                  root / 'boot/pci-capabilities.h'])
if a.af_observation:
    files.append(root / 'boot/pci-af-observation.h')
if a.ehci_capabilities:
    files.extend([root / 'hardware/lab/qotom-ehci.c.inc',
                  root / 'hardware/lab/qotom-ehci-arm.h',
                  root / 'hardware/lab/qotom-ehci-window.h',
                  root / 'boot/qotom-ehci-capabilities.h'])
if a.ehci_legacy:
    files.append(root / 'boot/qotom-ehci-legacy.h')
if a.ehci_handoff:
    files += [root / name for name in ('boot/qotom-ehci-handoff.h', 'hardware/lab/qotom-ehci-semaphore.h', 'hardware/lab/qotom-ehci-semaphore-arm.h', 'hardware/lab/qotom-pm-delay.h', 'hardware/lab/qotom-ehci-handoff.c.inc')]
manifest = {'ehci_handoff': a.ehci_handoff, 'ehci_legacy': a.ehci_legacy, 'ehci_capabilities': a.ehci_capabilities, 'af_observation': a.af_observation, 'pci_capabilities': a.pci_capabilities, 'bsp_topology': a.bsp_topology, 'native_inventory': a.native_inventory, 'ecam_read': a.ecam_read, 'dsdt_capture': a.dsdt_capture, 'ecam_memory_capture': a.ecam_memory_capture, 'bootstrap_capture': a.bootstrap_capture, 'pci_read_trace': a.pci_read_trace, 'acpi_capture': a.acpi_capture, 'handoff_capture': a.handoff_capture, 'evidence_class': 'lab-recovery-experiment', 'canonical_halt_evidence': False,
            'mode': a.mode, 'pci_diagnostic': a.pci_diagnostic,
            'recovery_seconds': 30 if a.mode == 'completion' else None, 'hang_recovery': False,
            'source_revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=root, text=True).strip(),
            'source_dirty': bool(subprocess.check_output(['git','status','--porcelain'], cwd=root, text=True)),
            'prepared_revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=prepared, text=True).strip(),
            'compiler': subprocess.check_output(['gcc','--version'], text=True).splitlines()[0],
            'files': {str(f.relative_to(root)): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(elf)
