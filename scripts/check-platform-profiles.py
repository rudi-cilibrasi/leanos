#!/usr/bin/env python3
"""Validate the closed platform registry and its complete manifests."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / 'hardware/platform-profiles.json'

EXPECTED = {
    'q35-v1': {
        'code': 1, 'version': 1,
        'components': {
            'firmware_root': 0x351, 'memory_map': 0x352, 'pci': 0x353,
            'bsp': 0x354, 'isolation': 0x355,
        },
        'uart': (0x3f8, 38400, '8N1'), 'bsp': (0, 1, False),
        'facilities': ('required', 'supported'), 'scenario': (10, 'blocking-ipc'),
    },
    'qotom-j1900-clbtm210-v2': {
        'code': 2, 'version': 2,
        'components': {
            'firmware_root': 0x1901, 'memory_map': 0x1902, 'pci': 0x1903,
            'bsp': 0x1904, 'isolation': 0x1905,
        },
        'uart': (0x3f8, 38400, '8N1'), 'bsp': (0, 4, False),
        'facilities': ('not-applicable', 'not-applicable'),
        'scenario': (10, 'blocking-ipc'),
    },
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate(registry_path=REGISTRY):
    registry_path = Path(registry_path)
    registry = json.loads(registry_path.read_text())
    require(registry.get('schema') == 'leanos-platform-profile-registry-v1',
            'registry schema')
    rows = registry.get('profiles')
    require(isinstance(rows, list) and len(rows) == 2, 'closed profile count')
    require({row.get('id') for row in rows} == set(EXPECTED), 'closed profile ids')
    require(len({row.get('code') for row in rows}) == 2, 'profile code uniqueness')
    require(len({(row.get('code'), row.get('version')) for row in rows}) == 2,
            'profile identity uniqueness')
    require(len({row.get('release_asset') for row in rows}) == 2 and
            all(isinstance(row.get('release_asset'), str) and
                row['release_asset'].startswith('PLATFORM_PROFILE_') and
                '/' not in row['release_asset'] for row in rows),
            'release asset names')
    root = registry_path.parent
    for row in rows:
        expected = EXPECTED[row['id']]
        require(row.get('code') == expected['code'] and
                row.get('version') == expected['version'], 'registry identity')
        relative = row.get('manifest')
        require(isinstance(relative, str) and relative.startswith('profiles/') and
                '..' not in Path(relative).parts, 'manifest path')
        path = root / relative
        raw = path.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == row.get('sha256'),
                f'manifest digest: {row["id"]}')
        manifest = json.loads(raw)
        require(manifest.get('schema') == 'leanos-platform-profile-v1',
                'profile schema')
        require((manifest.get('profile_id'), manifest.get('profile_code'),
                 manifest.get('profile_version')) ==
                (row['id'], row['code'], row['version']), 'profile identity binding')
        components = manifest.get('components', {})
        require(set(components) == {'firmware_root', 'memory_map', 'pci', 'uart',
                                    'bsp', 'isolation'}, 'complete components')
        for name, word in expected['components'].items():
            require(components[name].get('profile_word') == word,
                    f'{row["id"]} {name} identity')
            require(components[name].get('accepted_required') is True,
                    f'{row["id"]} {name} acceptance')
        uart = components['uart']
        require((uart.get('base'), uart.get('baud'), uart.get('mode')) ==
                expected['uart'], 'UART contract')
        bsp = components['bsp']
        require((bsp.get('executing_apic_id'), bsp.get('advertised_processors'),
                 bsp.get('ap_start_published')) == expected['bsp'], 'BSP contract')
        facilities = manifest.get('facilities', {})
        actual_facilities = tuple(
            value if isinstance(value, str) else value.get('status')
            for value in (facilities.get('vtd'), facilities.get('assigned_edu')))
        require(actual_facilities == expected['facilities'], 'facility policy')
        scenario = manifest.get('scenario', {})
        require((scenario.get('profile_word'), scenario.get('id')) ==
                expected['scenario'] and scenario.get('accepted_required') is True,
                'scenario contract')
        terminal = manifest.get('terminal', {})
        require(terminal.get('profile_word') == 1 and
                'serial-final' in terminal.get('semantic', '') and
                'halt' in terminal.get('semantic', ''), 'terminal contract')
        if row['id'].startswith('qotom'):
            require(facilities['vtd'].get('reason') and
                    facilities['assigned_edu'].get('reason'),
                    'not-applicable reasons')
            evidence = manifest.get('baseline_evidence', {})
            evidence_path = ROOT / evidence.get('manifest', '')
            require(evidence_path.is_file(), 'Qotom evidence manifest')
            require(hashlib.sha256(evidence_path.read_bytes()).hexdigest() ==
                    evidence.get('manifest_sha256'), 'Qotom evidence digest')
            observation = json.loads(evidence_path.read_text())
            require(observation.get('schema') ==
                    'leanos-qotom-platform-admission-observation-v1',
                    'Qotom evidence schema')
            require((observation.get('platform_profile'),
                     observation.get('platform_profile_version')) ==
                    (row['id'], row['version']), 'Qotom evidence profile binding')
            require(observation.get('source_dirty') is False and
                    observation.get('source_revision') ==
                    evidence.get('source_revision') and
                    observation.get('prepared_revision') ==
                    evidence.get('prepared_revision'),
                    'Qotom evidence source binding')
            require(observation.get('elf_sha256') == evidence.get('elf_sha256') and
                    observation.get('raw_serial_sha256') ==
                    evidence.get('serial_sha256') and
                    observation.get('terminal') == evidence.get('terminal'),
                    'Qotom evidence result binding')
            evidence_root = evidence_path.parent
            for relative, digest in observation.get('files', {}).items():
                item = Path(relative)
                require(not item.is_absolute() and '..' not in item.parts,
                        'Qotom evidence file path')
                artifact = evidence_root / item
                require(artifact.is_file() and
                        hashlib.sha256(artifact.read_bytes()).hexdigest() == digest,
                        f'Qotom evidence file digest: {relative}')
    return registry


def self_test():
    source = validate()
    mutations = {
        'unknown': lambda data: data['profiles'][0].update(id='unknown'),
        'duplicate-code': lambda data: data['profiles'][1].update(code=1),
        'wrong-version': lambda data: data['profiles'][1].update(version=1),
        'wrong-digest': lambda data: data['profiles'][1].update(sha256='0' * 64),
    }
    rejected = 0
    with tempfile.TemporaryDirectory(prefix='leanos-platform-profiles-') as directory:
        root = Path(directory)
        (root / 'profiles').mkdir()
        for row in source['profiles']:
            original = REGISTRY.parent / row['manifest']
            (root / row['manifest']).write_bytes(original.read_bytes())
        for name, mutate in mutations.items():
            candidate = copy.deepcopy(source)
            mutate(candidate)
            path = root / f'{name}.json'
            path.write_text(json.dumps(candidate))
            try:
                validate(path)
            except ValueError:
                rejected += 1
            else:
                raise AssertionError(f'accepted registry mutation: {name}')
    require(rejected == len(mutations), 'mutation coverage')
    print(f'Platform profile registry: 2 manifests and {rejected} mutations PASS')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
    else:
        registry = validate()
        print(f'Platform profile registry: {len(registry["profiles"])} manifests PASS')


if __name__ == '__main__':
    main()
