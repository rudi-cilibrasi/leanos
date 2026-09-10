#!/usr/bin/env python3
"""Retain FreeBSD PCI headers for review; this is not a DMA admission check."""
import argparse
import datetime
import hashlib
import json
import platform
from pathlib import Path
import re
import subprocess

MAX_FUNCTIONS = 64
SELECTOR = re.compile(r'[^\s@]+@(pci(\d+):(\d+):(\d+):(\d+)):')


def selectors(listing):
    result = []
    for line in listing.splitlines():
        match = SELECTOR.match(line)
        if not match:
            raise ValueError('malformed PCI listing')
        domain, bus, device, function = map(int, match.groups()[1:])
        if not (domain < 65536 and bus < 256 and device < 32 and function < 8):
            raise ValueError('PCI selector out of range')
        result.append(match[1])
    if not result or len(result) > MAX_FUNCTIONS or len(set(result)) != len(result):
        raise ValueError('empty, oversized or duplicate PCI inventory')
    return result


def decode(raw):
    words = raw.split()
    if len(words) != 16 or any(not re.fullmatch(r'(?:0x)?[0-9a-fA-F]{8}', x) for x in words):
        raise ValueError('expected sixteen 32-bit PCI header words')
    words = [int(x, 16) for x in words]
    if words[0] & 0xffff == 0xffff:
        raise ValueError('PCI function disappeared')
    header = (words[3] >> 16) & 0xff
    result = dict(words=words, vendor=words[0] & 0xffff, device=words[0] >> 16,
                  command=words[1] & 0xffff, status=words[1] >> 16,
                  revision=words[2] & 0xff, class_code=words[2] >> 8,
                  header=header, multifunction=bool(header & 0x80))
    if header & 0x7f == 1:
        result['bridge'] = dict(primary=words[6] & 0xff,
                                secondary=(words[6] >> 8) & 0xff,
                                subordinate=(words[6] >> 16) & 0xff,
                                control=words[15] >> 16)
    return result


def read_command(argv):
    return subprocess.run(argv, check=True, capture_output=True, text=True,
                          encoding='ascii', timeout=15).stdout


def collect(out, run=read_command):
    out.mkdir(parents=True, exist_ok=False)
    commands = []

    def capture(name, argv):
        raw = run(argv)
        if len(raw) > 262144:
            raise ValueError('PCI command output exceeds bound')
        data = raw.encode('ascii')
        (out / name).write_bytes(data)
        commands.append(dict(argv=argv, file=name, sha256=hashlib.sha256(data).hexdigest()))
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        return raw

    before = capture('listing-before.txt', ['/usr/sbin/pciconf', '-l'])
    functions = []
    for selector in selectors(before):
        name = selector.replace(':', '-') + '.txt'
        raw = capture(name, ['/usr/sbin/pciconf', '-r', selector, '0x0:0x3c'])
        functions.append(dict(selector=selector, **decode(raw)))
    after = capture('listing-after.txt', ['/usr/sbin/pciconf', '-l'])
    if before != after:
        raise ValueError('PCI listing changed during capture')
    report = dict(schema='leanos-freebsd-pci-headers-v1',
                  collected_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  collector_system=platform.system(), collector_release=platform.release(),
                  functions=functions, commands=commands,
                  platform_admitted=False, dma_containment_established=False,
                  scope='FreeBSD enumerated functions; sequential live-OS reads, not an atomic boot snapshot')
    (out / 'inventory.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new capture directory')
    args = parser.parse_args()
    if platform.system() != 'FreeBSD':
        parser.exit(1, 'error: run this collector locally on FreeBSD\n')
    try:
        report = collect(args.output)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f'error: {error}; partial raw evidence may remain\n')
    print(f"Captured {len(report['functions'])} PCI headers; no admission claim")


if __name__ == '__main__':
    main()
