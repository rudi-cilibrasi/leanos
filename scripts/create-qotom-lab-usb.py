#!/usr/bin/env python3
"""Create a local BIOS lab disk image. Never writes a physical disk."""
import argparse
import hashlib
from pathlib import Path
import subprocess
import tempfile
import uuid


def run(*args, **kwargs):
    return subprocess.run(list(args), check=True, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--freebsd-boot-uuid', required=True)
    parser.add_argument('--kernel-hang-elf', type=Path)
    args = parser.parse_args()
    boot_uuid = str(uuid.UUID(args.freebsd_boot_uuid))
    root = Path(__file__).resolve().parent.parent
    output = root / 'build/qotom-lab'
    elf = output / 'leanos-qotom-lab.elf'
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    template = (root / 'hardware/lab/grub-qotom.cfg.in').read_text()
    config = template.replace('@FREEBSD_BOOT_UUID@', boot_uuid).replace('@ELF_SHA256@', digest)
    hang_digest = hashlib.sha256(args.kernel_hang_elf.read_bytes()).hexdigest() if args.kernel_hang_elf else 'disabled'
    config = config.replace('@KERNEL_HANG_ENABLED@', '1' if args.kernel_hang_elf else '0').replace('@KERNEL_HANG_SHA256@', hang_digest)
    if args.kernel_hang_elf:
        (output / 'kernel-hang.sha256').write_text(hang_digest + '  /boot/leanos-qotom-kernel-hang.elf\n')
    (output / 'grub.cfg').write_text(config)
    (output / 'leanos.sha256').write_text(digest + '  /boot/leanos-qotom-lab.elf\n')
    # Work on a new regular file, then replace the previous image only on success.
    with tempfile.TemporaryDirectory(prefix='usb-', dir=output) as directory:
        staging = Path(directory)
        image = staging / 'usb.img'
        with image.open('xb') as stream:
            stream.truncate(96 * 1024 * 1024)
        run('sfdisk', str(image), input='label: dos\nstart=2048, type=c, bootable\n', text=True)
        loop = subprocess.check_output(
            ['sudo', '-n', 'losetup', '--find', '--show', '--partscan', str(image)], text=True).strip()
        mount = staging / 'mount'
        mount.mkdir()
        try:
            run('sudo', '-n', 'mkfs.vfat', '-F', '32', '-n', 'LEANOSLAB', loop + 'p1')
            run('sudo', '-n', 'mount', loop + 'p1', str(mount))
            try:
                run('sudo', '-n', 'grub-install', '--target=i386-pc',
                    '--boot-directory=' + str(mount / 'boot'), '--no-floppy', loop)
                run('sudo', '-n', 'cp', str(output / 'grub.cfg'), str(mount / 'boot/grub/grub.cfg'))
                run('sudo', '-n', 'cp', str(root / 'hardware/lab/grub-qotom-watchdog-window.cfg'),
                    str(mount / 'boot/grub/watchdog-window.cfg'))
                run('sudo', '-n', 'cp', str(root / 'hardware/lab/grub-qotom-watchdog.cfg'),
                    str(mount / 'boot/grub/watchdog.cfg'))
                run('sudo', '-n', 'grub-editenv', str(mount / 'boot/grub/grubenv'), 'create')
                run('sudo', '-n', 'grub-editenv', str(mount / 'boot/grub/grubenv'), 'set', 'request=none')
                run('sudo', '-n', 'cp', str(elf), str(mount / 'boot'))
                run('sudo', '-n', 'cp', str(output / 'leanos.sha256'), str(mount / 'boot/leanos.sha256'))
                if args.kernel_hang_elf:
                    run('sudo', '-n', 'cp', str(args.kernel_hang_elf), str(mount / 'boot/leanos-qotom-kernel-hang.elf'))
                    run('sudo', '-n', 'cp', str(output / 'kernel-hang.sha256'), str(mount / 'boot/kernel-hang.sha256'))
            finally:
                run('sudo', '-n', 'umount', str(mount))
        finally:
            run('sudo', '-n', 'losetup', '-d', loop)
        image.replace(output / 'usb.img')
    image = output / 'usb.img'
    print(hashlib.sha256(image.read_bytes()).hexdigest(), image)


if __name__ == '__main__':
    main()
