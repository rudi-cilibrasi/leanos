#!/usr/bin/env python3
"""Strictly replay CPU diagnostic records; never infer platform admission."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

MAX_CAPTURE = 4096
DECIMAL = r'(?:0|[1-9][0-9]{0,19})'


class DiagnosticError(ValueError):
    pass


def load_protocol(path):
    wanted = {('24', 'BOOT'), ('24', 'CPU'), ('24', 'CONTROL'), ('3', 'FINAL')}
    found = {}
    for line in Path(path).read_text().splitlines():
        fields = line.split('\t')
        if len(fields) == 5 and fields[0] == 'record' and tuple(fields[1:3]) in wanted:
            key = fields[2]
            if key in found:
                raise DiagnosticError('duplicate protocol identity')
            found[key] = fields[4]
    if len(found) != 4:
        raise DiagnosticError('missing protocol identity')
    return found


def replay_words(executable, mode, words):
    result = subprocess.run([str(executable), mode, *map(str, words)],
                            capture_output=True, timeout=10, check=True)
    if not re.fullmatch(rb'(?:0|[1-9][0-9]*)\n', result.stdout):
        raise DiagnosticError('malformed native replay result')
    return int(result.stdout)


def parse_words(line, prefix, count, field):
    pattern = (re.escape(prefix) + r' profile=j1900-cpu-v1 codec=1 width=' + str(count)
               + r' words=(' + DECIMAL + r'(?:,' + DECIMAL + r'){' + str(count - 1)
               + r'}) ' + field + r'=(' + DECIMAL + r')')
    match = re.fullmatch(pattern, line)
    if not match:
        raise DiagnosticError('malformed ' + field + ' record')
    words = [int(word) for word in match[1].split(',')]
    limit = (1 << (32 if count == 22 else 64)) - 1
    if any(word > limit for word in words):
        raise DiagnosticError('word exceeds capture width')
    return words, int(match[2])


def classify(raw, protocol, executable, *, ecam_failure=False):
    if not raw or len(raw) > MAX_CAPTURE or not raw.endswith(b'\n'):
        raise DiagnosticError('capture length or terminator')
    if any(byte != 10 and not 32 <= byte <= 126 for byte in raw):
        raise DiagnosticError('capture contains non-text bytes')
    lines = raw.decode('ascii').splitlines()
    if len(lines) not in (3, 4):
        raise DiagnosticError('record count')
    if lines[0] != protocol['BOOT'] + ' target=qotom-j1900-candidate phase=cpu-diagnostic platform-admitted=0 cpl3=0':
        raise DiagnosticError('boot identity or admission claim')
    cpu, claimed = parse_words(lines[1], protocol['CPU'], 22, 'selection')
    selected = replay_words(executable, 'cpu', cpu)
    if selected not in (*range(1, 13), 65536):
        raise DiagnosticError('unknown generated CPU result')
    if claimed != selected:
        raise DiagnosticError('CPU result disagrees with generated replay')
    msrs = None
    readback = None
    if selected != 65536:
        if len(lines) != 3:
            raise DiagnosticError('control readback follows rejected CPU')
        reason = 'j1900-cpu-profile'
    else:
        if len(lines) != 4:
            raise DiagnosticError('accepted CPU lacks control readback')
        msrs, claimed = parse_words(lines[2], protocol['CONTROL'], 8, 'readback')
        readback = replay_words(executable, 'msr', msrs)
        if readback not in (0, 1):
            raise DiagnosticError('unknown generated MSR result')
        if claimed != readback:
            raise DiagnosticError('MSR result disagrees with generated replay')
        reason = 'qotom-platform-pending' if readback == 1 else 'j1900-msr-readback'
        if ecam_failure and readback == 1:
            for failure in ('qotom-ecam-arm', 'qotom-ecam-transaction'):
                if lines[-1] == protocol['FINAL'] + ' status=FAIL reason=' + failure:
                    reason = failure
    if lines[-1] != protocol['FINAL'] + ' status=FAIL reason=' + reason:
        raise DiagnosticError('terminal result disagrees with replay')
    return {'schema': 'leanos-j1900-diagnostic-replay-v1',
            'capture_sha256': hashlib.sha256(raw).hexdigest(),
            'cpu_words': cpu, 'cpu_selection': selected,
            'msr_words': msrs, 'msr_readback': readback, 'terminal_reason': reason,
            'platform_admitted': False, 'cpl3_authorized': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('--protocol', type=Path, default=Path('build/boot/serial-protocol.tsv'))
    parser.add_argument('--replay', type=Path, default=Path('build/j1900-cpu-host/host'))
    args = parser.parse_args()
    try:
        with args.capture.open('rb') as stream:
            raw = stream.read(MAX_CAPTURE + 1)
        result = classify(raw, load_protocol(args.protocol), args.replay.resolve())
        result['protocol_sha256'] = hashlib.sha256(args.protocol.read_bytes()).hexdigest()
        result['replay_executable_sha256'] = hashlib.sha256(args.replay.read_bytes()).hexdigest()
        print(json.dumps(result, indent=2))
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f'error: {error}\n')


if __name__ == '__main__':
    main()
