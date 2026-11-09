#!/usr/bin/env python3
"""Boot the Qotom internal-disk GRUB (issue #620) in QEMU, on a disk laid out
like the Qotom's.

The disk is a sparse image with the Qotom's GPT, written here: the EFI system
partition at 40, freebsd-boot at 532520, the new bios-boot partition at
533544 and freebsd-zfs at 534528, 250069680 sectors in all. Its first sector
starts as the Qotom's protective MBR with a sentinel in place of FreeBSD's
pmbr (hardware/lab/pmbr-sentinel.S), which prints the BIOS drive it is given.
The test builds the bundle with scripts/build-qotom-internal-grub.py from
that sector, installs it as hardware/lab/install-internal-grub.sh does
(core.img in the bios-boot partition, mbr.bin in sector 0, the rest in
/leanos on the ESP), and checks each case's serial records:

- default: no request; the menu times out to FreeBSD, whose pmbr gets DL 0x80;
- leanos: a request for the installed image boots it once, and the request is
  consumed before the image loads;
- stale: a request for another digest is consumed and FreeBSD boots;
- hash-mismatch: an image whose SHA-256 list fails falls back to FreeBSD;
- stick-chain: a first disk standing in for the lab stick chainloads this
  disk's MBR (as hardware/lab/grub-qotom-ssd.cfg.in does), and the menu and
  FreeBSD's pmbr see the disk as hd1 (DL 0x81).
"""
import argparse
import hashlib
from pathlib import Path
import runpy
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import uuid
import zlib

ROOT = Path(__file__).resolve().parent.parent
BUILD = runpy.run_path(str(ROOT / 'scripts/build-qotom-internal-grub.py'))
SECTOR = 512
TOTAL = 250069680
LAYOUT = [  # first, last, type, label: the Qotom's ada0, plus bios-boot as ada0p4
    (40, 532519, 'c12a7328-f81f-11d2-ba4b-00a0c93ec93b', 'efiboot0'),
    (532520, 533543, '83bd6b9d-7f41-11dc-be0b-001560b84f0f', 'gptboot0'),
    (534528, 250068991, '516e7cba-6ecf-11d6-8ff8-00022d09712b', 'zfs0'),
    (533544, 534527, '21686148-6449-6e6f-744e-656564454649', 'grubboot0'),
]
CORE_LBA, CORE_SECTORS = 533544, 984
ESP = 40 * SECTOR
STICK_EARLY = """serial --unit=0 --speed=38400 --word=8 --parity=no --stop=1
terminal_input console serial
terminal_output console serial
echo 'LEANOS-LAB/1 CHAIN freebsd disk=hd1'
set root=(hd1)
chainloader +1
boot
"""


def run(*args, **kwargs):
    return subprocess.run([str(a) for a in args], check=True, stdout=subprocess.DEVNULL, **kwargs)


def protective_mbr(code):
    """The Qotom's first sector with `code` as its boot code."""
    sector = bytearray(SECTOR)
    sector[:len(code)] = code
    # One 0xEE entry from LBA 1 over the whole disk, as on the Qotom.
    struct.pack_into('<B3sB3sII', sector, 0x1BE, 0, b'\x00\x02\x00', 0xEE, b'\xff\xff\xff', 1, TOTAL - 1)
    sector[0x1FE:] = b'\x55\xaa'
    return bytes(sector)


def gpt(total, layout):
    """(primary, backup): the GPT headers and entry arrays, as (offset, bytes) writes."""
    entries = bytearray(128 * 128)
    for index, (first, last, kind, label) in enumerate(layout):
        name = label.encode('utf-16-le')
        struct.pack_into('<16s16sQQQ72s', entries, index * 128, uuid.UUID(kind).bytes_le,
                         uuid.uuid5(uuid.NAMESPACE_URL, 'leanos-620-' + label).bytes_le, first, last, 0, name)
    disk = uuid.uuid5(uuid.NAMESPACE_URL, 'leanos-620-disk').bytes_le

    def header(current, backup, table):
        fields = [b'EFI PART', 0x00010000, 92, 0, 0, current, backup, 34, total - 34, disk, table, 128, 128,
                  zlib.crc32(entries)]
        raw = struct.pack('<8sIIIIQQQQ16sQIII', *fields)
        fields[3] = zlib.crc32(raw)
        return struct.pack('<8sIIIIQQQQ16sQIII', *fields).ljust(SECTOR, b'\0')
    return [(SECTOR, header(1, total - 1, 2)), (2 * SECTOR, bytes(entries)),
            ((total - 33) * SECTOR, bytes(entries)), ((total - 1) * SECTOR, header(total - 1, 1, total - 33))]


def esp_image(path, files):
    run('mformat', '-C', '-i', path, '-T', 131072, '-h', 16, '-s', 32, '::')
    run('mmd', '-i', path, '::/leanos', '::/leanos/grub')
    for name, data in files.items():
        local = path.parent / ('esp-' + name.replace('/', '_'))
        local.write_bytes(data)
        run('mcopy', '-o', '-i', path, local, '::/' + name)


def write_at(image, offset, data):
    with image.open('r+b') as stream:
        stream.seek(offset)
        stream.write(data)


def read_grubenv(image):
    out = subprocess.run(['mtype', '-i', f'{image}@@{ESP}', '::/leanos/grub/grubenv'],
                         check=True, stdout=subprocess.PIPE).stdout
    return out


def qemu(log, drives, timeout, expected):
    args = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-nodefaults', '-cpu', 'max', '-m', '256M',
            '-display', 'none', '-monitor', 'none', '-serial', 'file:' + str(log), '-no-reboot',
            '-nic', 'none',
            '-device', 'intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,'
                       'dma-translation=on,snoop-control=off',
            '-device', 'VGA,bus=pcie.0,addr=0x1', '-device', 'isa-debug-exit,iobase=0xf4,iosize=0x04']
    for index, image in enumerate(drives):
        args += ['-drive', f'id=d{index},if=none,format=raw,file={image}',
                 '-device', f'ide-hd,drive=d{index},bus=ide.{index}']
    process = subprocess.Popen(args, stderr=subprocess.DEVNULL)
    deadline = time.monotonic() + timeout
    try:
        while time.monotonic() < deadline:
            data = log.read_bytes() if log.exists() else b''
            if all(e in data for e in expected):
                return data
            if process.poll() is not None:
                return log.read_bytes() if log.exists() else b''
            time.sleep(0.5)
        return log.read_bytes() if log.exists() else b''
    finally:
        if process.poll() is None:
            process.kill()
        process.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--elf', type=Path, default=ROOT / 'build/boot/leanos.elf',
                        help='a q35 LeanOS kernel to stand in for the lab image')
    parser.add_argument('--final', default='FINAL status=PASS',
                        help="the kernel's last serial record, which the leanos case requires")
    parser.add_argument('--case', action='append', help='run only these cases')
    parser.add_argument('--keep', type=Path, help='keep the serial logs here')
    args = parser.parse_args()
    elf = args.elf.read_bytes()
    digest = hashlib.sha256(elf).hexdigest()
    failures = []
    with tempfile.TemporaryDirectory(prefix='qotom-internal-grub-') as directory:
        tmp = Path(directory)
        run('as', '--32', ROOT / 'hardware/lab/pmbr-sentinel.S', '-o', tmp / 'sentinel.o')
        run('ld', '-m', 'elf_i386', '-Ttext', '0x7c00', '--oformat', 'binary', tmp / 'sentinel.o',
            '-o', tmp / 'sentinel.bin')
        code = (tmp / 'sentinel.bin').read_bytes()
        assert len(code) < 0x1B8, len(code)
        current = protective_mbr(code)
        bundle = BUILD['build'](tmp / 'bundle', current, CORE_LBA, CORE_SECTORS, timeout=1)
        base = tmp / 'disk.img'
        with base.open('wb') as stream:
            stream.truncate(TOTAL * SECTOR)
        for offset, data in gpt(TOTAL, LAYOUT):
            write_at(base, offset, data)
        # What install-internal-grub.sh writes: core, then sector 0 last.
        write_at(base, CORE_LBA * SECTOR, bundle['core.img'])
        write_at(base, 0, bundle['mbr.bin'])
        # The stand-in stick: GRUB in an MBR gap, chainloading hd1.
        stick = tmp / 'stick.img'
        with stick.open('wb') as stream:
            stream.truncate(16 * 1024 * 1024)
        stick_raw = tmp / 'stick-core-raw.img'
        BUILD['mkimage'](Path('/usr/lib/grub/i386-pc'), '(hd0)/', STICK_EARLY, BUILD['MODULES'], stick_raw)
        blank = bytes(510) + b'\x55\xaa'
        stick_mbr, stick_core = BUILD['setup'](Path('/usr/lib/grub/i386-pc/boot.img').read_bytes(),
                                               stick_raw.read_bytes(), blank, 1, 2047)
        write_at(stick, SECTOR, stick_core)
        write_at(stick, 0, stick_mbr)

        def esp_files(request, sums=None):
            return {
                'leanos/leanos-qotom-lab.elf': elf,
                'leanos/leanos.sha256': (sums or f'{digest}  leanos-qotom-lab.elf\n').encode(),
                'leanos/leanos-digest.cfg': f'set leanos_digest={digest}\n'.encode(),
                'leanos/grub/grub.cfg': bundle['grub.cfg'],
                'leanos/grub/freebsd-mbr.bin': bundle['freebsd-mbr.bin'],
                'leanos/grub/grubenv': BUILD['grubenv'](request),
            }

        consumed = b'LEANOS-DISK/1 REQUEST consumed=1'
        cases = {
            'default': (esp_files('none'), False, 60,
                        [b'LEANOS-DISK/1 MENU disk=hd0 default=freebsd',
                         b'LEANOS-DISK/1 CHAIN freebsd disk=hd0', b'FREEBSD-PMBR-SENTINEL dl=80\n']),
            'leanos': (esp_files('leanos-' + digest), False, 600,
                       [consumed, b'LEANOS-DISK/1 MENU disk=hd0 default=leanos timeout=0',
                        b'LEANOS-DISK/1 LEANOS load=1', b'leanos-qotom-lab.elf: OK', args.final.encode()]),
            'stale': (esp_files('leanos-' + '0' * 64), False, 60,
                      [consumed, b'LEANOS-DISK/1 MENU disk=hd0 default=freebsd',
                       b'FREEBSD-PMBR-SENTINEL dl=80\n']),
            'hash-mismatch': (esp_files('leanos-' + digest, sums='0' * 64 + '  leanos-qotom-lab.elf\n'),
                              False, 120,
                              [consumed, b'LEANOS-DISK/1 LOAD-FAILED fallback=freebsd',
                               b'FREEBSD-PMBR-SENTINEL dl=80\n']),
            'stick-chain': (esp_files('none'), True, 60,
                            [b'LEANOS-LAB/1 CHAIN freebsd disk=hd1', b'LEANOS-DISK/1 MENU disk=hd1 default=freebsd',
                             b'LEANOS-DISK/1 CHAIN freebsd disk=hd1', b'FREEBSD-PMBR-SENTINEL dl=81\n']),
        }
        for name, (files, chained, seconds, expected) in cases.items():
            if args.case and name not in args.case:
                continue
            disk = tmp / f'disk-{name}.img'
            subprocess.run(['cp', '--sparse=always', str(base), str(disk)], check=True)
            esp = tmp / f'esp-{name}.img'
            esp_image(esp, files)
            write_at(disk, ESP, esp.read_bytes())
            log = tmp / f'{name}.log'
            data = qemu(log, ([stick] if chained else []) + [disk], seconds, expected)
            missing = [e for e in expected if e not in data]
            # Every case ends with no request: none was set, or GRUB consumed it.
            if b'\nrequest=none\n' not in read_grubenv(disk):
                missing.append(b'grubenv request=none afterwards')
            if args.keep:
                args.keep.mkdir(parents=True, exist_ok=True)
                shutil.copy(log, args.keep / log.name)
            if missing:
                failures.append(name)
                print(f'FAIL {name}: missing {missing}')
                sys.stdout.write(data.decode(errors='replace')[-3000:] + '\n')
            else:
                print(f'ok   {name}')
            disk.unlink()
    if failures:
        raise SystemExit(f'{len(failures)} case(s) failed: {", ".join(failures)}')
    print('qotom internal GRUB: all cases passed')


if __name__ == '__main__':
    main()
