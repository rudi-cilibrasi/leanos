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
    args = parser.parse_args()
    boot_uuid = str(uuid.UUID(args.freebsd_boot_uuid))
    root = Path(__file__).resolve().parent.parent
    output = root / 'build/qotom-lab'
    elf = output / 'leanos-qotom-lab.elf'
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    template = (root / 'hardware/lab/grub-qotom.cfg.in').read_text()
    config = template.replace('@FREEBSD_BOOT_UUID@', boot_uuid).replace('@ELF_SHA256@', digest)
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
                run('sudo', '-n', 'cp', str(root / 'hardware/lab/grub-qotom-watchdog.cfg'),
                    str(mount / 'boot/grub/qotom-watchdog.cfg'))
                run('sudo', '-n', 'grub-editenv', str(mount / 'boot/grub/grubenv'), 'create')
                run('sudo', '-n', 'grub-editenv', str(mount / 'boot/grub/grubenv'), 'set', 'request=none')
                run('sudo', '-n', 'cp', str(elf), str(mount / 'boot'))
                run('sudo', '-n', 'cp', str(output / 'leanos.sha256'), str(mount / 'boot/leanos.sha256'))
            finally:
                run('sudo', '-n', 'umount', str(mount))
        finally:
            run('sudo', '-n', 'losetup', '-d', loop)
        image.replace(output / 'usb.img')
    image = output / 'usb.img'
    print(hashlib.sha256(image.read_bytes()).hexdigest(), image)


if __name__ == '__main__':
    main()
