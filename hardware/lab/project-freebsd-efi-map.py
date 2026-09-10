#!/usr/bin/env python3
"""Conservative hosted E820 projection of a FreeBSD amd64 raw EFI map.

This is an offline decoder fixture conversion, not a GRUB handoff capture or
permission to allocate live OS memory. Preserve descriptor order and bounds;
reserve loader, boot-services, runtime and persistent memory roles; reject unsupported types.
"""
import argparse
from pathlib import Path
import struct

MAX_BYTES = 65536
NAMES = {1: 'System RAM', 2: 'Reserved', 3: 'ACPI Tables',
         4: 'ACPI Non-volatile Storage', 5: 'Unusable memory'}


def project(raw):
    # FreeBSD amd64 efi_map_header is 24 bytes, rounded up to 32 before the
    # descriptor vector. Padding/descriptor extension bytes are not fields.
    if not 32 <= len(raw) <= 32 + MAX_BYTES:
        raise ValueError('EFI map: captured byte count exceeds bounds')
    size, stride, version = struct.unpack_from('<QQI', raw)
    if version != 1 or not 40 <= stride <= 256:
        raise ValueError('EFI map: unsupported descriptor version or size')
    if not size or size % stride or size != len(raw) - 32:
        raise ValueError('EFI map: incomplete or inconsistent descriptor vector')
    rows = []
    for offset in range(32, len(raw), stride):
        kind, base, _virtual, pages, attributes = struct.unpack_from('<I4xQQQQ', raw, offset)
        if kind > 14:
            raise ValueError('EFI map: unsupported descriptor type')
        if not pages or base % 4096 or base + pages * 4096 > 1 << 64:
            raise ValueError('EFI map: empty, unaligned or overflowing range')
        # Only conventional memory is usable. This intentionally does not
        # reclaim EFI loader/boot-services memory, even after ExitBootServices.
        projected = {7: 1, 9: 3, 10: 4, 8: 5}.get(kind, 2)
        if attributes & (1 << 63):
            projected = 2
        rows.append((base, pages * 4096, projected))
    return rows


def render(rows):
    return 'index\tstart\tend\ttype\n' + ''.join(
        f'{index}\t{base:#x}\t{base + length - 1:#x}\t{NAMES[kind]}\n'
        for index, (base, length, kind) in enumerate(rows))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('raw_map', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    # Bound the read itself, not just subsequent interpretation.
    with args.raw_map.open('rb') as source:
        raw = source.read(MAX_BYTES + 33)
    text = render(project(raw))
    with args.output.open('x') as target:
        target.write(text)


if __name__ == '__main__':
    main()
