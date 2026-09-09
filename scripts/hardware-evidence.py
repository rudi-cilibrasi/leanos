#!/usr/bin/env python3
"""Capture and independently verify the opt-in physical-machine evidence tier."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import select
import shlex
import stat
import sys
import termios
import time
import tty

ROOT = Path(__file__).resolve().parent.parent
HARDWARE = ROOT / 'hardware'
MAX_BYTES = 1048576
PAYLOADS = {'profile.json', 'inventory.json', 'toolchain.json',
            'serial.raw', 'serial.normalized', 'events.jsonl', 'protocol.tsv', 'implementation.py'}


class EvidenceError(Exception):
    def __init__(self, category, detail):
        self.category = category
        super().__init__(detail)


def require(condition, detail, category='invalid-bundle'):
    if not condition:
        raise EvidenceError(category, detail)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def reject_duplicates(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result


def read_json(path):
    data = Path(path).read_bytes()
    require(len(data) <= MAX_BYTES, f'oversized JSON: {path}')
    return json.loads(data, object_pairs_hook=reject_duplicates,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          EvidenceError('invalid-bundle', f'nonfinite JSON: {value}')))


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def validate_schema(value, schema, where='$'):
    """Evaluate the small JSON Schema vocabulary used by bundle.schema.json.

    No network resolution, coercion, default insertion, or unknown keywords.
    The schema is repository-owned; unsupported future keywords fail closed.
    """
    supported = {'$schema', '$id', 'title', 'type', 'const', 'enum', 'properties',
                 'required', 'additionalProperties', 'minimum', 'maximum',
                 'minLength', 'pattern'}
    require(set(schema) <= supported, 'unsupported schema keyword')
    if 'type' in schema:
        types = {'object': dict, 'string': str, 'number': (int, float)}
        require(schema['type'] in types, 'unsupported schema type')
        require(isinstance(value, types[schema['type']]) and not isinstance(value, bool),
                f'{where}: wrong type')
    if 'const' in schema:
        require(type(value) is type(schema['const']) and value == schema['const'],
                f'{where}: wrong constant')
    if 'enum' in schema:
        require(value in schema['enum'], f'{where}: unexpected value')
    if isinstance(value, dict):
        require(set(schema.get('required', [])) <= value.keys(), f'{where}: missing field')
        if schema.get('additionalProperties') is False:
            require(value.keys() <= schema['properties'].keys(), f'{where}: unknown field')
        for key, sub in schema.get('properties', {}).items():
            if key in value:
                validate_schema(value[key], sub, f'{where}.{key}')
    if isinstance(value, (int, float)):
        require(math.isfinite(value), f'{where}: nonfinite number')
        require(value >= schema.get('minimum', -math.inf), f'{where}: too small')
        require(value <= schema.get('maximum', math.inf), f'{where}: too large')
    if isinstance(value, str):
        require(len(value) >= schema.get('minLength', 0), f'{where}: empty string')
        if 'pattern' in schema:
            require(re.fullmatch(schema['pattern'], value) is not None, f'{where}: invalid format')


def timestamp(text):
    require(isinstance(text, str), 'timestamp is not a string')
    try:
        value = dt.datetime.fromisoformat(text)
    except ValueError as error:
        raise EvidenceError('invalid-bundle', 'invalid timestamp') from error
    require(value.tzinfo is not None and value.utcoffset() == dt.timedelta(0),
            'timestamps must explicitly use UTC')
    return value.timestamp()


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def profile(scenario):
    manifest = read_json(HARDWARE / 'manifest.json')
    require(manifest['schema'] == 'leanos-hardware-manifest-v1', 'manifest version')
    rows = manifest['rows']
    require(len({row['id'] for row in rows}) == len(rows), 'duplicate hardware scenario')
    matches = [row for row in rows if row['id'] == scenario]
    require(len(matches) == 1, 'unknown hardware scenario')
    row = matches[0]
    require(row['tier'] == 'hardware' and row['result_class'] == 'controlled-rejection',
            'hardware tier/result mismatch')
    return row


def classify(raw, expected, quiet_seconds, minimum_quiet=10):
    start = raw.find(b'LEANOS/')
    if start < 0:
        return 'silence-timeout' if not raw else 'no-leanos-protocol'
    transcript = raw[start:].replace(b'\r\n', b'\n')
    # Exact comparison below rejects every other record, including all user,
    # timer, scheduler and syscall records, even ones unknown to this classifier.
    if re.search(rb'LEANOS/\d+ (?:ENTRY|ENTER|SYSCALL|TIMER|SWITCH|RESUME)\b', transcript) or \
            re.search(rb'LEANOS/\d+ FINAL status=PASS\b', transcript):
        return 'unexpected-success-or-cpl3'
    if transcript == expected:
        return 'exact-rejection' if quiet_seconds >= minimum_quiet else 'terminal-observation-timeout'
    if transcript.startswith(expected):
        return 'post-terminal-bytes'
    terminals = [line for line in transcript.splitlines() if b' FINAL ' in line]
    if terminals and any(line != expected.splitlines()[-1] for line in terminals):
        return 'wrong-rejection'
    return 'malformed-or-incomplete-protocol'


def artifact_check(row, iso, elf, source_revision, toolchain=None, protocol=None):
    require(source_revision == row['source_revision'], 'source revision mismatch', 'source-mismatch')
    for name, path in [('iso', iso), ('elf', elf)]:
        require(file_sha(path) == row['artifacts'][name], f'{name} digest mismatch', 'artifact-mismatch')
    if protocol is not None:
        require(file_sha(protocol) == row['artifacts']['protocol'],
                'protocol digest mismatch', 'artifact-mismatch')
    if toolchain is not None:
        require(file_sha(toolchain) == row['artifacts']['toolchain'],
                'toolchain digest mismatch', 'artifact-mismatch')


def verify(bundle, iso=None, elf=None):
    bundle = Path(bundle)
    require(not bundle.is_symlink(), 'symlink bundle')
    for path in bundle.iterdir():
        require(path.is_file() and not path.is_symlink(), 'bundle must contain plain files')
        require(path.name in PAYLOADS | {'bundle.json', 'result.json', 'reset.json'},
                f'unexpected bundle file: {path.name}')
        require(path.stat().st_size <= MAX_BYTES * 8, 'oversized bundle file')
    meta = read_json(bundle / 'bundle.json')
    validate_schema(meta, read_json(HARDWARE / 'bundle.schema.json'))
    row = profile(meta['scenario'])
    require(meta['source_revision'] == row['source_revision'], 'source revision drift', 'source-mismatch')
    require(meta['artifacts'] == row['artifacts'], 'artifact manifest drift', 'artifact-mismatch')
    for name, wanted in meta['files'].items():
        require(file_sha(bundle / name) == wanted, f'file hash mismatch: {name}')
    require(file_sha(bundle / 'implementation.py') ==
            meta['provenance']['capture_implementation_sha256'], 'capture implementation drift')
    require(read_json(bundle / 'profile.json') == row, 'profile differs from repository manifest')
    require(read_json(bundle / 'inventory.json') == read_json(HARDWARE / row['inventory']),
            'inventory differs from reviewed profile')
    require(file_sha(bundle / 'toolchain.json') == row['artifacts']['toolchain'], 'toolchain drift')
    require(file_sha(bundle / 'protocol.tsv') == row['artifacts']['protocol'], 'protocol drift')
    protocol_lines = (bundle / 'protocol.tsv').read_text().splitlines()
    require(protocol_lines[:2] == ['leanos-serial-protocol\t1',
            'source-revision\t' + row['source_revision']], 'protocol source binding')
    identities = {line.split('\t')[4] for line in protocol_lines
                  if line.startswith('record\t') and len(line.split('\t')) == 5}
    require(all(' '.join(line.split(' ')[:2]) in identities for line in row['expected_lines']),
            'expected record is outside pinned generated vocabulary')
    require((iso is None) == (elf is None), 'supply both --iso and --elf')
    if iso is not None:
        artifact_check(row, iso, elf, meta['source_revision'])
    cap = meta['capture']
    start, end, reset = [timestamp(cap[key]) for key in
                         ['started_utc', 'finished_utc', 'reset_declared_utc']]
    require(start <= reset <= end, 'reset declaration outside capture', 'reset-not-observed')
    if meta['provenance']['kind'] == 'live':
        require(read_json(bundle / 'reset.json') == {'declared_utc': cap['reset_declared_utc']},
                'reset marker differs from metadata', 'reset-not-observed')
    duration = cap['duration_seconds']
    require(abs(end - start - duration) <= 1, 'wall and monotonic durations disagree')
    require(cap['timeout_seconds'] == row['timeout_seconds'], 'capture timeout differs from profile')
    require(duration >= cap['timeout_seconds'], 'capture ended before bounded timeout', 'capture-timeout')
    raw = (bundle / 'serial.raw').read_bytes()
    require(len(raw) <= row['max_bytes'], 'serial byte limit exceeded', 'capture-overflow')
    require((bundle / 'serial.normalized').read_bytes() == raw.replace(b'\r\n', b'\n'),
            'normalized transcript does not match raw bytes')
    joined = bytearray()
    last_elapsed = 0.0
    previous_utc = start
    kernel_utc = None
    kernel_offset = raw.find(b'LEANOS/')
    for line in (bundle / 'events.jsonl').read_text().splitlines():
        event = json.loads(line, object_pairs_hook=reject_duplicates)
        require(set(event) == {'elapsed_seconds', 'utc', 'offset', 'length', 'hex'}, 'event fields')
        elapsed = event['elapsed_seconds']
        require(type(elapsed) in (float, int) and math.isfinite(elapsed) and
                last_elapsed <= elapsed <= duration, 'event time outside capture')
        observed = timestamp(event['utc'])
        require(previous_utc <= observed <= end and abs(observed - start - elapsed) <= 1,
                'event UTC/monotonic mismatch')
        require(type(event['offset']) is int and event['offset'] == len(joined), 'event offset')
        require(isinstance(event['hex'], str) and re.fullmatch(r'(?:[0-9a-f]{2})+', event['hex']),
                'event bytes must be nonempty lowercase hex')
        block = bytes.fromhex(event['hex'])
        require(type(event['length']) is int and event['length'] == len(block), 'event length')
        joined.extend(block)
        require(len(joined) <= row['max_bytes'], 'event byte limit')
        if event['offset'] <= kernel_offset < len(joined):
            kernel_utc = observed
        last_elapsed, previous_utc = elapsed, observed
    require(bytes(joined) == raw, 'events do not reconstruct raw capture')
    if kernel_utc is not None:
        require(reset <= kernel_utc, 'kernel output preceded declared reset', 'reset-not-observed')
    expected = ('\n'.join(row['expected_lines']) + '\n').encode('ascii')
    quiet = duration - last_elapsed
    result = classify(raw, expected, quiet, row['quiet_seconds'])
    return {'schema': 'leanos-hardware-result-v1', 'tier': 'hardware',
            'scenario': row['id'], 'classification': result,
            'result_class': row['result_class'], 'bytes_received': len(raw),
            'raw_sha256': sha(raw), 'quiet_seconds': quiet,
            'artifacts_checked': iso is not None,
            'provenance': meta['provenance']['kind']}


def mark_reset(bundle):
    # This is an operator assertion, not a power controller or reset detector.
    bundle = Path(bundle)
    require((bundle / 'serial.raw').exists() and not (bundle / 'bundle.json').exists(),
            'capture is not armed')
    with (bundle / 'reset.json').open('x') as stream:
        json.dump({'declared_utc': utc()}, stream)
    print('Reset declared: reboot/select USB now; leave the target untouched until capture ends.')


def capture(args):
    row = profile(args.scenario)
    require(bool(args.operator.strip()), 'operator identifier is empty')
    artifact_check(row, args.iso, args.elf, args.source_revision, args.toolchain, args.protocol)
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    args.capture_created = True
    fd = None
    raw = bytearray()
    try:
        fd = os.open(args.device, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
        require(stat.S_ISCHR(os.fstat(fd).st_mode), 'serial device must be a character device',
                'capture-infrastructure-failure')
        tty.setraw(fd, termios.TCSANOW)
        attrs = termios.tcgetattr(fd)
        attrs[0] &= ~(termios.IXON | termios.IXOFF | termios.IXANY)
        attrs[2] &= ~(termios.PARENB | termios.CSTOPB | termios.CSIZE | termios.CRTSCTS)
        attrs[2] |= termios.CS8 | termios.CLOCAL | termios.CREAD
        attrs[4] = attrs[5] = termios.B38400
        termios.tcsetattr(fd, termios.TCSANOW, attrs)
        termios.tcflush(fd, termios.TCIFLUSH)
        started_utc = utc()
        started = time.monotonic()
        with (out / 'serial.raw').open('wb') as log, (out / 'events.jsonl').open('w') as events:
            print('READY: 38400 8N1; run mark-reset, then reboot/select USB. Do not reset again.', flush=True)
            while time.monotonic() - started < row['timeout_seconds']:
                remaining = row['timeout_seconds'] - (time.monotonic() - started)
                if select.select([fd], [], [], max(0, min(1, remaining)))[0]:
                    block = os.read(fd, 65536)
                    require(bool(block), 'serial device disconnected', 'capture-infrastructure-failure')
                    offset = len(raw)
                    raw.extend(block)
                    log.write(block)
                    log.flush()
                    events.write(json.dumps({'elapsed_seconds': time.monotonic() - started,
                                             'utc': utc(), 'offset': offset,
                                             'length': len(block), 'hex': block.hex()}) + '\n')
                    events.flush()
                    require(len(raw) <= row['max_bytes'], 'capture byte limit', 'capture-overflow')
                    print(f'received {len(raw)} bytes', flush=True)
        duration = time.monotonic() - started
        finished_utc = utc()
        require((out / 'reset.json').exists(), 'no operator reset declaration', 'reset-not-observed')
        reset = read_json(out / 'reset.json')['declared_utc']
        (out / 'serial.normalized').write_bytes(bytes(raw).replace(b'\r\n', b'\n'))
        write_json(out / 'profile.json', row)
        (out / 'inventory.json').write_bytes((HARDWARE / row['inventory']).read_bytes())
        (out / 'toolchain.json').write_bytes(args.toolchain.read_bytes())
        (out / 'protocol.tsv').write_bytes(args.protocol.read_bytes())
        (out / 'implementation.py').write_bytes(Path(__file__).read_bytes())
        command = ['python3', 'scripts/hardware-evidence.py', 'capture']
        for name in ['scenario', 'iso', 'elf', 'toolchain', 'protocol', 'source_revision',
                     'device', 'operator', 'output']:
            command.extend(['--' + name.replace('_', '-'), str(getattr(args, name))])
        meta = {'schema': 'leanos-hardware-bundle-v1', 'tier': 'hardware',
                'scenario': row['id'], 'source_revision': args.source_revision,
                'artifacts': row['artifacts'], 'operator': args.operator,
                'capture': {'command': shlex.join(command), 'device': args.device,
                            'started_utc': started_utc, 'finished_utc': finished_utc,
                            'reset_declared_utc': reset, 'timeout_seconds': row['timeout_seconds'],
                            'duration_seconds': duration, 'baud': 38400, 'format': '8N1',
                            'flow_control': 'none'},
                'provenance': {'kind': 'live', 'capture_implementation_sha256': file_sha(__file__),
                               'original_result_sha256': 'not-applicable',
                               'note': 'Operator-declared reset; no automated power control or independent halt detector.'},
                'files': {name: file_sha(out / name) for name in sorted(PAYLOADS)}}
        write_json(out / 'bundle.json', meta)
        return verify(out, args.iso, args.elf)
    finally:
        if fd is not None:
            os.close(fd)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    c = sub.add_parser('capture')
    c.add_argument('--scenario', required=True)
    for name in ['iso', 'elf', 'toolchain', 'protocol', 'output']:
        c.add_argument('--' + name, type=Path, required=True)
    c.add_argument('--source-revision', required=True)
    c.add_argument('--device', required=True)
    c.add_argument('--operator', required=True)
    v = sub.add_parser('verify')
    v.add_argument('bundle', type=Path)
    v.add_argument('--iso', type=Path)
    v.add_argument('--elf', type=Path)
    m = sub.add_parser('mark-reset')
    m.add_argument('bundle', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'mark-reset':
            mark_reset(args.bundle)
            return 0
        result = capture(args) if args.command == 'capture' else verify(args.bundle, args.iso, args.elf)
    except EvidenceError as error:
        result = {'classification': error.category, 'detail': str(error)}
    except (OSError, termios.error) as error:
        result = {'classification': 'capture-infrastructure-failure' if args.command == 'capture'
                  else 'invalid-bundle', 'detail': str(error)}
    except (ValueError, TypeError, KeyError) as error:
        result = {'classification': 'invalid-bundle', 'detail': str(error)}
    if args.command == 'capture' and getattr(args, 'capture_created', False):
        # Failed captures retain partial logs and a non-passing report. Existing
        # evidence directories are never overwritten, including on mkdir failure.
        if not (args.output / 'result.json').exists():
            write_json(args.output / 'result.json', result)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result['classification'] == 'exact-rejection' else 1


if __name__ == '__main__':
    sys.exit(main())
