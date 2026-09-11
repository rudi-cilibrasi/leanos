"""Actual GRUB bytes as a memory-only corpus row; no reconstructed ACPI tables."""
import hashlib
import json
from pathlib import Path
import struct

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'firmware-corpus/qotom-native-handoff.json'
CASE = 'qotom-native-grub-20260911'
MUTATIONS = {'bad-magic': 1, 'unaligned-pointer': 2, 'truncated': 6,
             'reserved-header': 7, 'entry-version': 17, 'zero-entry': 20,
             'overflow-entry': 21, 'duplicate-map': 15}


def inputs():
    manifest = json.loads(MANIFEST.read_text())
    capture = ROOT / manifest['capture']
    for name, digest in json.loads((capture / 'manifest.json').read_text())['files'].items():
        if hashlib.sha256((capture / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native handoff capture hash mismatch: ' + name)
    data = (capture / 'cycle-1/multiboot2.bin').read_bytes()
    metadata = json.loads((capture / 'cycle-1/handoff.json').read_text())
    if (manifest['schema'] != 'leanos-native-handoff-corpus-v1'
            or hashlib.sha256(data).hexdigest() != manifest['raw_sha256']
            or manifest['magic'] != metadata['magic'] or manifest['address'] != metadata['address']
            or metadata['status'] != 0 or len(data) != metadata['length']):
        raise ValueError('native handoff provenance mismatch')
    maps = [tag for tag in metadata['tags'] if tag['type'] == 6]
    if len(maps) != 1 or maps[0]['memory_map_entry_size'] != 24:
        raise ValueError('native capture memory-map layout changed')
    offset, size = maps[0]['offset'], maps[0]['size']
    if struct.unpack_from('<II', data, offset) != (6, size):
        raise ValueError('native capture memory-map projection mismatch')
    result = [('captured', data, manifest['magic'], manifest['address'], manifest['words'])]
    for name, error in MUTATIONS.items():
        raw = bytearray(data)
        magic, address = manifest['magic'], manifest['address']
        if name == 'bad-magic': magic = 0
        elif name == 'unaligned-pointer': address += 1
        elif name == 'truncated': raw = raw[:-8]
        elif name == 'reserved-header': struct.pack_into('<I', raw, 4, 1)
        elif name == 'entry-version': struct.pack_into('<I', raw, offset + 12, 1)
        elif name == 'zero-entry': struct.pack_into('<Q', raw, offset + 24, 0)
        elif name == 'overflow-entry': struct.pack_into('<QQ', raw, offset + 16, 0xffffffffffffffff, 2)
        elif name == 'duplicate-map':
            raw = raw[:-8] + raw[offset:offset + size] + raw[-8:]
            struct.pack_into('<I', raw, 0, len(raw))
        result.append((name, bytes(raw), magic, address, [1, 2, error, 0, 0]))
    return result


def rows(out):
    target = out / CASE
    target.mkdir(parents=True, exist_ok=True)
    result = []
    for name, data, magic, address, words in inputs():
        path = target / (name + '.bin')
        path.write_bytes(data)
        result.append({'case': CASE, 'input': CASE + '/' + name, 'stage': 'handoff',
                       'path': path, 'words': words, 'result': 'accepted' if name == 'captured' else 'decoder-rejected:' + name,
                       'handoff_args': (magic, address)})
    return result
