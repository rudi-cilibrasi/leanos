#!/usr/bin/env python3
"""Build GRUB for the Qotom's internal disk, beside FreeBSD (issue #620).

The bundle boots LeanOS from the internal disk without the lab stick:

- core.img: i386-pc GRUB with every module it needs built in, a serial console
  from its first line and the prefix (,gpt1)/leanos/grub. It goes in a
  bios-boot partition at --core-lba.
- mbr.bin: GRUB's boot sector, set up for a core at --core-lba, with the BPB
  area and the partition table (0x1B8-0x1FD) of --current-mbr kept byte for
  byte. It replaces the disk's first sector.
- freebsd-mbr.bin: --current-mbr unchanged, FreeBSD's pmbr. GRUB chainloads
  it, so FreeBSD boots exactly as before.
- grub.cfg: hardware/lab/grub-qotom-internal.cfg.in.
- grubenv: an empty one-shot request (request=none).
- SHA256SUMS.

This is the setup step grub-bios-setup does for an embedded core, done
here so that the exact bytes can be tested on an image (see
scripts/test-qotom-internal-grub.py) before they are written to the disk.
"""
import argparse
import hashlib
from pathlib import Path
import struct
import subprocess
import tempfile

SECTOR = 512
# include/grub/i386/pc/boot.h
BPB_START, BPB_END = 0x03, 0x5A
KERNEL_SECTOR = 0x5C
BOOT_DRIVE = 0x64
DRIVE_CHECK = 0x66
NT_MAGIC, PART_END = 0x1B8, 0x1FE
LIST_SIZE = 12  # the default blocklist at the end of diskboot.img
MODULES = [
    'biosdisk', 'part_gpt', 'part_msdos', 'fat', 'normal', 'configfile', 'echo', 'test',
    'serial', 'terminal', 'terminfo', 'regexp', 'loadenv', 'hashsum', 'gcry_sha256',
    'multiboot2', 'chain', 'sleep', 'reboot', 'halt', 'ls', 'cat', 'search', 'probe', 'minicmd',
]
EARLY = """serial --unit=0 --speed=38400 --word=8 --parity=no --stop=1
terminal_input console serial
terminal_output console serial
echo "LEANOS-DISK/1 CORE root=$root prefix=$prefix"
"""


def mkimage(grub_dir, prefix, early, modules, out):
    with tempfile.TemporaryDirectory() as tmp:
        cfg = Path(tmp) / 'early.cfg'
        cfg.write_text(early)
        subprocess.run(['grub-mkimage', '-d', str(grub_dir), '-O', 'i386-pc', '-C', 'xz',
                        '-p', prefix, '-c', str(cfg), '-o', str(out)] + modules, check=True)


def setup(boot_img, core_img, current_mbr, core_lba, max_sectors):
    """Return (mbr, core) for a core embedded at core_lba, as grub-bios-setup would."""
    if len(boot_img) != SECTOR or len(current_mbr) != SECTOR:
        raise SystemExit('boot.img and the current MBR must be one sector each')
    if current_mbr[0x1FE:] != b'\x55\xaa':
        raise SystemExit('the current MBR has no 55AA signature')
    core = bytearray(core_img)
    core += bytes(-len(core) % SECTOR)
    sectors = len(core) // SECTOR
    if sectors > max_sectors:
        raise SystemExit(f'core.img is {sectors} sectors, the partition holds {max_sectors}')
    start, length, segment = struct.unpack_from('<QHH', core, SECTOR - LIST_SIZE)
    if length != sectors - 1 or segment != 0x820:
        raise SystemExit(f'unexpected diskboot blocklist: start={start} len={length} seg={segment:#x}')
    struct.pack_into('<Q', core, SECTOR - LIST_SIZE, core_lba + 1)
    mbr = bytearray(boot_img)
    mbr[BPB_START:BPB_END] = current_mbr[BPB_START:BPB_END]
    struct.pack_into('<Q', mbr, KERNEL_SECTOR, core_lba)
    if mbr[BOOT_DRIVE] != 0xFF:
        raise SystemExit('boot.img does not take the boot drive from DL')
    # A hard disk: replace the jump over the BIOS drive-number workaround.
    mbr[DRIVE_CHECK:DRIVE_CHECK + 2] = b'\x90\x90'
    mbr[NT_MAGIC:PART_END] = current_mbr[NT_MAGIC:PART_END]
    return bytes(mbr), bytes(core)


def grubenv(request='none'):
    text = f'# GRUB Environment Block\nrequest={request}\n'.encode()
    return text + b'#' * (1024 - len(text))


def build(out, current_mbr, core_lba, core_sectors, timeout, grub_dir=Path('/usr/lib/grub/i386-pc'),
          early=EARLY, prefix='(,gpt1)/leanos/grub'):
    root = Path(__file__).resolve().parent.parent
    out.mkdir(parents=True, exist_ok=True)
    raw = out / 'core-raw.img'
    mkimage(grub_dir, prefix, early, MODULES, raw)
    mbr, core = setup((grub_dir / 'boot.img').read_bytes(), raw.read_bytes(), current_mbr,
                      core_lba, core_sectors)
    raw.unlink()
    files = {
        'mbr.bin': mbr,
        'core.img': core,
        'freebsd-mbr.bin': current_mbr,
        'grub.cfg': (root / 'hardware/lab/grub-qotom-internal.cfg.in').read_text()
                    .replace('@MENU_TIMEOUT@', str(timeout)).encode(),
        'grubenv': grubenv(),
    }
    for name, data in files.items():
        (out / name).write_bytes(data)
    (out / 'SHA256SUMS').write_text(''.join(
        f'{hashlib.sha256(data).hexdigest()}  {name}\n' for name, data in sorted(files.items())))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--current-mbr', type=Path, required=True,
                        help="the disk's first sector as it is now (FreeBSD's pmbr and the protective MBR)")
    parser.add_argument('--core-lba', type=int, default=533544,
                        help='first sector of the bios-boot partition (the Qotom: 533544)')
    parser.add_argument('--core-sectors', type=int, default=984, help='its size in sectors (the Qotom: 984)')
    parser.add_argument('--timeout', type=int, default=5, help='menu timeout in seconds')
    parser.add_argument('--out', type=Path, default=Path('build/qotom-internal-grub'))
    args = parser.parse_args()
    files = build(args.out, args.current_mbr.read_bytes(), args.core_lba, args.core_sectors, args.timeout)
    print(f"{args.out}: core.img {len(files['core.img']) // SECTOR} sectors at LBA {args.core_lba}")
    print((args.out / 'SHA256SUMS').read_text(), end='')


if __name__ == '__main__':
    main()
