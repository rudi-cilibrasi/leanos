#!/usr/bin/env python3
"""Redact a Qotom lab capture before it is committed (issue #572).

A WiFi capture's serial stream can contain decrypted network payloads: the
driver's diagnostic dumps of decapsulated frame bodies (`WIFI 0e24`,
`WIFI 0e26`), which hold other devices' LAN traffic. This helper reads a
cycle directory written by run-qotom-recovery-lab.py (`events.jsonl`, and
`serial.raw` if present), removes every such line from the bytes and from
the timed events, and writes `events.jsonl`, `serial.raw` and
`redaction.json` to a new directory.

With `--fragment` it also drops the bulky records that the runner's
classifiers do not read (data dumps, PCI observations, `WIFI` value records
other than the rtl8168-arp program's tags 40xx-42xx, IPC
block/send/dispatch and NET fetch records) and joins events that arrive
within one second of each other, so that a capture fragment is small enough
to keep as a test fixture. A fragment still classifies as its
capture does. Its events are stored as `serial.raw` plus `timing.tsv` (one
`elapsed<TAB>bytes` line per event) in place of `events.jsonl`; `load` reads
either layout.

Usage: redact-qotom-capture.py CYCLE_DIR OUTPUT_DIR [--fragment]
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

# Lines that carry decrypted payload bytes: LeanOS.Wifi.Connect's Tag.body
# and Tag.dump records.
PAYLOAD = re.compile(rb'\r*WIFI 0e2[46] ')
# Records the classifiers never read. The rtl8168-arp program's value
# records (tags 40xx-42xx, issue #595) are read, so a fragment keeps them.
BULKY = re.compile(
    rb'\r*(?:WIFI (?!4[0-2])[0-9a-f]{4} 0x[0-9a-f]{8}\r?\n'
    rb'|LEANOS-LAB/1 [A-Z0-9-]+ [^\n]* hex=[0-9a-f]*\r?\n'
    rb'|LEANOS-LAB/1 (?:PCI-CAPS?|PCI-AF|PCIE-DEVICE) '
    rb'|LEANOS/[0-9]+ PCI-HEADER '
    rb'|LEANOS/[0-9]+ IPC event=(?:block|send|dispatch) '
    rb'|LEANOS-LAB/1 NET event=fetch )')
JOIN_SECONDS = 1.0


def lines(data):
    """Byte ranges of the stream's lines, each with its newline."""
    start = 0
    while start < len(data):
        end = data.find(b'\n', start)
        end = len(data) if end < 0 else end + 1
        yield start, end
        start = end


def redact(events, fragment=False):
    chunks = [bytes.fromhex(e['hex']) for e in events]
    data = b''.join(chunks)
    keep = bytearray(b'\x01' * len(data))
    removed = {'payload': 0, 'fragment': 0}
    for start, end in lines(data):
        line = data[start:end]
        kind = ('payload' if PAYLOAD.match(line) else
                'fragment' if fragment and BULKY.match(line) else None)
        if kind:
            removed[kind] += 1
            keep[start:end] = bytes(end - start)
    out, offset = [], 0
    for event, chunk in zip(events, chunks):
        kept = bytes(b for b, k in zip(chunk, keep[offset:offset + len(chunk)]) if k)
        offset += len(chunk)
        if not kept:
            continue
        if (fragment and out and
                event['elapsed'] - out[-1]['first'] < JOIN_SECONDS):
            out[-1]['bytes'] += kept
        else:
            out.append({'first': event['elapsed'], 'utc': event.get('utc'), 'bytes': kept})
    result = []
    for item in out:
        event = {'elapsed': item['first'], 'hex': item['bytes'].hex()}
        if item['utc'] is not None:
            event['utc'] = item['utc']
        result.append(event)
    redacted = b''.join(item['bytes'] for item in out)
    if any(PAYLOAD.match(redacted[s:e]) for s, e in lines(redacted)):
        raise ValueError('payload line survived redaction')
    return result, redacted, removed


def load(directory):
    """The timed events of a capture or a fragment directory."""
    directory = Path(directory)
    if (directory / 'timing.tsv').exists():
        raw = (directory / 'serial.raw').read_bytes()
        events, offset = [], 0
        for line in (directory / 'timing.tsv').read_text().splitlines():
            elapsed, length = line.split('\t')
            events.append({'elapsed': float(elapsed),
                           'hex': raw[offset:offset + int(length)].hex()})
            offset += int(length)
        if offset != len(raw):
            raise ValueError('timing.tsv does not cover serial.raw')
        return events
    return [json.loads(line) for line in (directory / 'events.jsonl').read_text().splitlines()]


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('cycle', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--fragment', action='store_true')
    args = parser.parse_args()
    source = (args.cycle / 'events.jsonl').read_bytes()
    events = [json.loads(line) for line in source.decode().splitlines()]
    raw = b''.join(bytes.fromhex(e['hex']) for e in events)
    if (args.cycle / 'serial.raw').exists() and (args.cycle / 'serial.raw').read_bytes() != raw:
        raise SystemExit('serial.raw differs from events.jsonl')
    redacted_events, redacted, removed = redact(events, args.fragment)
    args.output.mkdir(parents=True, exist_ok=False)
    if args.fragment:
        name = 'timing.tsv'
        text = ''.join('%.3f\t%d\n' % (e['elapsed'], len(e['hex']) // 2) for e in redacted_events)
    else:
        name = 'events.jsonl'
        text = ''.join(json.dumps(e) + '\n' for e in redacted_events)
    (args.output / name).write_text(text)
    (args.output / 'serial.raw').write_bytes(redacted)
    summary = {'source_events_sha256': hashlib.sha256(source).hexdigest(),
               'source_raw_sha256': hashlib.sha256(raw).hexdigest(),
               'fragment': args.fragment, 'removed_lines': removed,
               name.replace('.', '_') + '_sha256': hashlib.sha256(text.encode()).hexdigest(),
               'raw_sha256': hashlib.sha256(redacted).hexdigest()}
    (args.output / 'redaction.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
