#!/usr/bin/env python3
"""Boot the actual ECAM lab ELF and require rejection of foreign q35 firmware."""
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--elf', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    elf, output = args.elf.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    result = output / 'result.json'
    result.unlink(missing_ok=True)
    diagnostic = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
    protocol = diagnostic['load_protocol'](ROOT / 'build/boot/serial-protocol.tsv')
    handoff = runpy.run_path(str(ROOT / 'scripts/check-qotom-handoff-capture.py'))
    acpi = runpy.run_path(str(ROOT / 'scripts/check-qotom-acpi-capture.py'))
    image = runpy.run_path(str(ROOT / 'scripts/test-qotom-pci-diagnostic-image.py'))
    subprocess.run(['grub-file', '--is-x86-multiboot2', str(elf)], check=True)
    grub = output / 'iso/boot/grub'
    grub.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(elf, grub.parent / 'leanos.elf')
    shutil.copyfile(ROOT / 'boot/grub.cfg', grub / 'grub.cfg')
    iso = output / 'diagnostic.iso'
    with (output / 'grub.log').open('w') as log:
        subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    capture = output / 'serial.raw'
    capture.unlink(missing_ok=True)
    cpu = 'max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off'
    expected = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-ecam-arm\n'
    with tempfile.TemporaryDirectory(prefix='ecam-qemu-') as tmp:
        monitor = Path(tmp) / 'qmp.sock'
        command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', cpu,
                   '-m', '128', '-smp', '1', '-display', 'none', '-serial', f'file:{capture}',
                   '-monitor', 'none', '-nic', 'none', '-no-reboot', '-no-shutdown',
                   '-qmp', f'unix:{monitor},server=on,wait=off', '-cdrom', str(iso)]
        (output / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
        with (output / 'qemu.log').open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 45
                while True:
                    raw = capture.read_bytes() if capture.exists() else b''
                    if len(raw) > 393216:
                        raise RuntimeError('ECAM capture exceeds bound')
                    if raw.endswith(b'\n') and protocol['FINAL'].encode() in raw:
                        break
                    if process.poll() is not None or time.monotonic() >= deadline:
                        raise RuntimeError('incomplete ECAM guest execution')
                    time.sleep(0.05)
                if raw.count(expected) != 1 or not raw.endswith(expected):
                    raise RuntimeError('foreign firmware did not reach the ECAM arm rejection')
                if b'LEANOS-LAB/1 ECAM-ARM ' in raw or protocol['PCI-SCAN'].encode() in raw:
                    raise RuntimeError('foreign firmware entered ECAM enumeration')
                mode = b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
                if not raw.startswith(mode):
                    raise RuntimeError('missing lab mode')
                payload = raw[len(mode):]
                consumed, binary, handoff_meta = handoff['parse_prefix'](payload)
                if handoff_meta['status'] or not handoff_meta['tag_chain_valid']:
                    raise RuntimeError('invalid handoff')
                remaining, metadata, tables = acpi['extract'](payload[consumed:], binary, dsdt=True)
                if metadata is None:
                    raise RuntimeError('missing complete firmware evidence')
                image['verify_acpi_memory'](monitor, output, metadata, tables)
                decoder = runpy.run_path(str(ROOT / 'scripts/check-qotom-ecam-capture.py'))
                _, ecam = decoder['extract'](remaining, protocol, metadata, tables)
                if ecam is None or ecam['armed'] or ecam['firmware_matches']:
                    raise RuntimeError('foreign firmware rejection decoder mismatch')
                (output / 'multiboot2.bin').write_bytes(binary)
                (output / 'acpi.json').write_text(json.dumps(metadata, indent=2) + '\n')
                result.write_text(json.dumps({
                    'schema': 'leanos-ecam-foreign-firmware-rejection-v1',
                    'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest(),
                    'serial_sha256': hashlib.sha256(raw).hexdigest(),
                    'firmware_qmp_match': True, 'ecam_arm_rejected': True,
                    'physical_ecam_validated': False}, indent=2) + '\n')
            finally:
                if process.poll() is None:
                    process.terminate()
                    try: process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill(); process.wait()
    print('ECAM image: foreign firmware rejected before enumeration; QMP ACPI bytes match PASS')


if __name__ == '__main__':
    main()
