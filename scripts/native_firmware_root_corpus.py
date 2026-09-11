"""Root replay from exact native Qotom bytes; never reconstruct the handoff."""
import hashlib
import json
from pathlib import Path
import runpy
from dataclasses import replace
import firmware_root_corpus as roots

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'hardware/lab/observations/qotom-native-acpi-20260911'


def load(directory=DIRECTORY):
    manifest = json.loads((directory / 'manifest.json').read_text())
    for name, digest in manifest['files'].items():
        path = directory / name
        if Path(name).is_absolute() or '..' in Path(name).parts or path.is_symlink() or not path.resolve().is_relative_to(directory.resolve()):
            raise ValueError('unsafe native firmware manifest path')
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('native firmware capture hash mismatch: ' + name)
    cycle = directory / 'cycle-1'
    events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
    raw = (cycle / 'serial.raw').read_bytes()
    if raw != b''.join(bytes.fromhex(event['hex']) for event in events):
        raise ValueError('native firmware event stream differs')
    handoff = runpy.run_path(str(ROOT / 'scripts/check-qotom-handoff-capture.py'))
    _, info, metadata = handoff['parse_prefix'](raw[raw.index(b'LEANOS-LAB/1 HANDOFF status='):])
    if metadata['status'] or info != (cycle / 'multiboot2.bin').read_bytes():
        raise ValueError('native handoff differs from serial transport')
    decoder = runpy.run_path(str(ROOT / 'scripts/check-qotom-acpi-capture.py'))
    _, tables_meta, tables = decoder['extract'](raw, info)
    if tables_meta != json.loads((cycle / 'acpi.json').read_text()):
        raise ValueError('native ACPI metadata differs from serial transport')
    ordered = []
    for entry in tables_meta['tables']:
        address = entry['address']; name = f'{address:016x}.bin'
        if tables[name] != (cycle / 'acpi' / name).read_bytes():
            raise ValueError('native ACPI file differs from serial transport')
        ordered.append((address, tables[name]))
    address, root = ordered[0]
    replay = roots.RootReplay(info, root, address, tuple(ordered[1:]),
                              magic=metadata['magic'], info_address=metadata['address'])
    return replay, metadata['apic']


def inputs():
    base, executing = load()
    result = {'native-root':base, **roots.mutations(base)}
    result.update({'native-bad-magic':replace(base,magic=0),
                   'native-unaligned-address':replace(base,info_address=base.info_address+1)})
    return result, executing


def rows(out):
    metadata = json.loads((ROOT / 'firmware-corpus/qotom-native-root.json').read_text())
    if metadata.get('schema') != 'leanos-native-root-replay-v1':
        raise ValueError('unsupported native firmware replay schema')
    if hashlib.sha256((DIRECTORY / 'manifest.json').read_bytes()).hexdigest() != metadata['capture_manifest_sha256']:
        raise ValueError('native firmware capture manifest differs')
    cases, executing = inputs()
    if set(cases) != set(metadata['inputs']):
        raise ValueError('native firmware replay case set differs')
    vocabulary = runpy.run_path(str(ROOT / 'scripts/firmware-corpus.py'))
    result = []
    for name, replay in cases.items():
        entry = metadata['inputs'][name]
        words = entry['words']
        if len(words) != 6 or any(type(word) is not int or not 0 <= word < 2**64 for word in words) or words[0] != 1 or words[5] != 0:
            raise ValueError('native firmware projection shape differs: ' + name)
        if words[1] == 2:
            if entry['result'] != roots.rejection_name(words[:5]):
                raise ValueError('native firmware result disagrees with words: ' + name)
        else:
            try:
                vocabulary['check_result'](
                    name, entry['result'], words[:5], vocabulary['MADT_RESULT_TABLES'])
            except vocabulary['CorpusError'] as error:
                raise ValueError('native firmware result disagrees with words: ' + name) from error
        if replay.digest() != entry['normalized_sha256']:
            raise ValueError('native firmware normalized bytes differ: ' + name)
        path = replay.write(out / 'qotom-native-root' / name)
        result.append({'case':'qotom-native-root', 'input':'qotom-native-root/' + name,
                       'stage':'root', 'path':path, 'root':replay, 'executing':executing,
                       'words':entry['words'], 'result':entry['result']})
    return result
