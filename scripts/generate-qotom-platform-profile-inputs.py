#!/usr/bin/env python3
"""Generate the exact Qotom E820 tag used by the live platform gate."""
import hashlib
import json
from pathlib import Path
import struct
import sys

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / 'hardware/lab/observations/qotom-platform-admission-20260913'
PROFILE = ROOT / 'hardware/profiles/qotom-j1900-clbtm210-v2.json'


def checked(relative):
    manifest = json.loads((CAPTURE / 'manifest.json').read_text())
    raw = (CAPTURE / relative).read_bytes()
    if hashlib.sha256(raw).hexdigest() != manifest['files'][relative]:
        raise ValueError('retained platform artifact hash mismatch: ' + relative)
    return raw


def memory_map_tag(raw):
    if len(raw) < 16 or struct.unpack_from('<II', raw) != (len(raw), 0):
        raise ValueError('invalid retained Multiboot2 information')
    offset = 8
    found = []
    while offset + 8 <= len(raw):
        kind, size = struct.unpack_from('<II', raw, offset)
        if size < 8 or offset + size > len(raw):
            raise ValueError('invalid retained Multiboot2 tag')
        if kind == 6:
            found.append(raw[offset:offset + size])
        advance = (size + 7) & ~7
        if kind == 0:
            if size != 8 or offset + advance != len(raw):
                raise ValueError('invalid retained Multiboot2 terminator')
            break
        offset += advance
    if len(found) != 1:
        raise ValueError('retained handoff lacks one memory-map tag')
    tag = found[0]
    if len(tag) != 472 or struct.unpack_from('<II', tag, 8) != (24, 0):
        raise ValueError('unexpected Qotom memory-map layout')
    return tag


def render(tag):
    lines = [
        '/* Generated exact Qotom platform inputs; do not edit. */',
        '#ifndef LEANOS_LAB_QOTOM_PLATFORM_PROFILE_INPUTS_H',
        '#define LEANOS_LAB_QOTOM_PLATFORM_PROFILE_INPUTS_H',
        f'#define QOTOM_PLATFORM_MEMORY_MAP_TAG_BYTES {len(tag)}u',
        'static const uint8_t qotom_platform_memory_map_tag[] = {',
    ]
    for offset in range(0, len(tag), 16):
        lines.append('    ' + ','.join(f'0x{x:02x}' for x in tag[offset:offset + 16]) + ',')
    lines.extend(['};', '#endif', ''])
    return '\n'.join(lines)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: generate-qotom-platform-profile-inputs.py OUTPUT')
    raw = checked('cycle-1/multiboot2.bin')
    tag = memory_map_tag(raw)
    memory = json.loads(PROFILE.read_text())['components']['memory_map']
    if hashlib.sha256(raw).hexdigest() != memory['multiboot2_sha256'] or \
       hashlib.sha256(tag).hexdigest() != memory['tag_sha256']:
        raise ValueError('retained Qotom memory-map profile binding differs')
    Path(sys.argv[1]).write_text(render(tag))
