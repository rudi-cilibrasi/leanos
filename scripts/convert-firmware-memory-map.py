#!/usr/bin/env python3
"""Convert a digest-bound Linux sysfs firmware capture to Multiboot2 bytes.

This creates a replay wrapper, not a claim that GRUB supplied those bytes.
It never repairs, sorts by address, coalesces or drops firmware entries.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import struct

MAX_ENTRIES = 256
MAX_FILE_BYTES = 65536
TYPE_CODES = {'System RAM': 1, 'Reserved': 2, 'reserved': 2,
              'ACPI Tables': 3, 'ACPI Non-volatile Storage': 4,
              'Unusable memory': 5}
HEX = re.compile(r'0x[0-9a-fA-F]+\n?\Z')


class CaptureError(ValueError):
    pass


def bounded(path):
    with path.open('rb') as stream:
        data = stream.read(MAX_FILE_BYTES + 1)
    if len(data) > MAX_FILE_BYTES:
        raise CaptureError(f'{path.name}: file exceeds capture bound')
    return data


def verified_files(root, inventory_digest):
    inventory = bounded(root / 'SHA256SUMS')
    if hashlib.sha256(inventory).hexdigest() != inventory_digest:
        raise CaptureError('capture inventory digest mismatch')
    entries = {}
    for line in inventory.decode('ascii').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        if not match:
            raise CaptureError('malformed capture digest inventory')
        digest, name = match.groups()
        path = PurePosixPath(name)
        if (path.is_absolute() or '..' in path.parts or str(path) != name
                or name in entries or name == 'SHA256SUMS'):
            raise CaptureError('unsafe or duplicate capture path')
        entries[name] = digest
    directories = {str(parent) for name in entries
                   for parent in PurePosixPath(name).parents if str(parent) != '.'}
    names = set()
    for count, path in enumerate(root.rglob('*'), 1):
        if count > MAX_ENTRIES * 4 + 4:
            raise CaptureError('capture path count exceeds bound')
        name = path.relative_to(root).as_posix()
        if path.is_symlink():
            raise CaptureError('capture contains a symlink')
        if path.is_file():
            names.add(name)
        elif not path.is_dir() or name not in directories:
            raise CaptureError('capture contains an unexpected directory or special file')
    if names != set(entries) | {'SHA256SUMS'}:
        raise CaptureError('capture file inventory differs')
    files = {}
    for name, digest in entries.items():
        data = bounded(root / name)
        if hashlib.sha256(data).hexdigest() != digest:
            raise CaptureError(f'{name}: capture digest mismatch')
        files[name] = data
    return files


def convert(root, inventory_digest):
    files = verified_files(root, inventory_digest)
    try:
        metadata = json.loads(files['capture.json'])
    except (KeyError, ValueError) as error:
        raise CaptureError('capture metadata is missing or invalid') from error
    if (not isinstance(metadata, dict)
            or metadata.get('schema') != 'leanos-firmware-capture-draft-v1'
            or type(metadata.get('entry_count')) is not int
            or not 0 < metadata['entry_count'] <= MAX_ENTRIES):
        raise CaptureError('unsupported capture schema or entry count')
    indexes = set()
    for name in files:
        if name in {'capture.json', 'APIC.bin'}:
            continue
        match = re.fullmatch(r'memmap/(0|[1-9][0-9]*)/(start|end|type)', name)
        if not match:
            raise CaptureError(f'unsupported capture file: {name}')
        indexes.add(int(match.group(1)))
    if len(indexes) != metadata['entry_count']:
        raise CaptureError('captured entry count differs')
    encoded = []
    for index in sorted(indexes):  # firmware order exposed by sysfs, not address order
        try:
            raw = {field: files[f'memmap/{index}/{field}'].decode('ascii')
                   for field in ('start', 'end', 'type')}
        except (KeyError, UnicodeDecodeError) as error:
            raise CaptureError(f'entry {index}: incomplete or non-ASCII fields') from error
        if not HEX.fullmatch(raw['start']) or not HEX.fullmatch(raw['end']):
            raise CaptureError(f'entry {index}: invalid address syntax')
        start, end = int(raw['start'], 16), int(raw['end'], 16)
        length = end - start + 1
        if not (0 <= start <= end < 2**64 and 0 < length < 2**64):
            raise CaptureError(f'entry {index}: invalid inclusive range')
        kind = raw['type'].removesuffix('\n')
        if kind not in TYPE_CODES:
            raise CaptureError(f'entry {index}: unsupported memory type {kind!r}')
        encoded.append(struct.pack('<QQII', start, length, TYPE_CODES[kind], 0))
    tag = struct.pack('<IIII', 6, 16 + 24 * len(encoded), 24, 0) + b''.join(encoded)
    return struct.pack('<II', 8 + len(tag) + 8, 0) + tag + struct.pack('<II', 0, 8)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('--inventory-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        data = convert(args.capture, args.inventory_sha256)
        with args.output.open('xb') as stream:
            stream.write(data)
    except (CaptureError, OSError, UnicodeError) as error:
        parser.exit(1, f'capture conversion failed: {error}\n')


if __name__ == '__main__':
    main()
