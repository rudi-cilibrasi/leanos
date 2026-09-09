#!/usr/bin/env python3
"""Opt-in serial evidence capture; never writes boot media or reboots a host."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import select
import termios
import time
import tty


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def classify(raw, expected, quiet_seconds):
    start = raw.find(b'LEANOS/')
    if start < 0:
        return 'silence-timeout' if not raw else 'no-leanos-protocol'
    transcript = raw[start:].replace(b'\r\n', b'\n')
    lines = transcript.splitlines()
    if any(b'FINAL status=PASS' in line or b' ENTRY ' in line for line in lines):
        return 'unexpected-success-or-user-entry'
    if transcript == expected:
        return 'exact-rejection' if quiet_seconds >= 10 else 'insufficient-terminal-observation'
    if transcript.startswith(expected):
        return 'post-terminal-bytes'
    if any(b' FINAL ' in line and b'status=FAIL' in line for line in lines):
        terminal = expected.splitlines()[-1]
        if any(b' FINAL ' in line and line != terminal for line in lines):
            return 'wrong-rejection'
    return 'malformed-or-incomplete-protocol'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--image', type=Path, required=True)
    parser.add_argument('--elf', type=Path, required=True)
    parser.add_argument('--device', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=180)
    args = parser.parse_args()
    if args.timeout < 10 or args.timeout > 3600:
        parser.error('timeout must be between 10 and 3600 seconds')
    manifest = json.loads(args.manifest.read_text())
    # Exclusive evidence directory prevents accidental replacement of prior runs.
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    result = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'device': args.device, 'baud': 38400, 'format': '8N1',
              'flow_control': 'none', 'timeout_seconds': args.timeout,
              'manifest_sha256': digest(args.manifest),
              'runner_sha256': digest(__file__)}
    raw = bytearray()
    fd = None
    try:
        for name, path in [('image', args.image), ('elf', args.elf)]:
            result[name + '_sha256'] = digest(path)
            if result[name + '_sha256'] != manifest[name + '_sha256']:
                raise ValueError(name + '-digest-mismatch')
        expected = ''.join(line + '\n' for line in manifest['expected_lines']).encode('ascii')
        fd = os.open(args.device, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
        tty.setraw(fd, termios.TCSANOW)
        attrs = termios.tcgetattr(fd)
        attrs[0] &= ~(termios.IXON | termios.IXOFF | termios.IXANY)
        attrs[2] &= ~(termios.PARENB | termios.CSTOPB | termios.CSIZE | termios.CRTSCTS)
        attrs[2] |= termios.CS8 | termios.CLOCAL | termios.CREAD
        attrs[4] = attrs[5] = termios.B38400
        termios.tcsetattr(fd, termios.TCSANOW, attrs)
        termios.tcflush(fd, termios.TCIFLUSH)
        started = last_byte = time.monotonic()
        print('READY: serial capture armed at 38400 8N1; reboot may proceed.', flush=True)
        with (args.output / 'serial.raw').open('wb') as log, \
                (args.output / 'serial-events.jsonl').open('w') as events:
            while time.monotonic() - started < args.timeout:
                remaining = args.timeout - (time.monotonic() - started)
                if select.select([fd], [], [], max(0, min(1, remaining)))[0]:
                    block = os.read(fd, 65536)
                    if not block:
                        raise OSError('serial-device-disconnected')
                    raw.extend(block)
                    log.write(block)
                    log.flush()
                    last_byte = time.monotonic()
                    events.write(json.dumps({
                        'elapsed_seconds': last_byte - started,
                        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        'offset': len(raw) - len(block), 'length': len(block),
                        'hex': block.hex(),
                    }) + '\n')
                    events.flush()
                    print(repr(block), flush=True)
        result['quiet_seconds'] = time.monotonic() - last_byte
        result['classification'] = classify(bytes(raw), expected, result['quiet_seconds'])
    except ValueError as error:
        result['classification'] = 'artifact-mismatch'
        result['error'] = str(error)
    except OSError as error:
        result['classification'] = 'capture-infrastructure-failure'
        result['error'] = str(error)
    finally:
        if fd is not None:
            os.close(fd)
        (args.output / 'serial.raw').write_bytes(raw)
        (args.output / 'serial.normalized').write_bytes(bytes(raw).replace(b'\r\n', b'\n'))
        result['raw_sha256'] = digest(args.output / 'serial.raw')
        result['bytes_received'] = len(raw)
        result['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (args.output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)
    return 0 if result['classification'] == 'exact-rejection' else 1


if __name__ == '__main__':
    raise SystemExit(main())
