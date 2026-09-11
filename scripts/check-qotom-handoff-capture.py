#!/usr/bin/env python3
"""Decode a bounded lab transport without granting handoff or display authority."""
import hashlib
import re
import struct

MAX_TRANSPORT = 196608
DECIMAL = rb'(?:0|[1-9][0-9]{0,9})'


def describe_tags(raw):
    """Report raw tag metadata; malformed content is retained, never repaired."""
    report = {'tag_chain_valid': False, 'tags': []}
    if len(raw) < 16 or struct.unpack_from('<II', raw) != (len(raw), 0):
        return report
    offset = 8
    while offset <= len(raw) - 8:
        kind, size = struct.unpack_from('<II', raw, offset)
        if size < 8 or size > len(raw) - offset:
            return report
        advance = (size + 7) & ~7
        if advance > len(raw) - offset:
            return report
        tag = {'offset': offset, 'type': kind, 'size': size}
        if kind == 8 and size >= 32:
            address, pitch, width, height, bits, mode = struct.unpack_from('<QIIIBB', raw, offset + 8)
            tag['framebuffer'] = dict(address=address, pitch=pitch, width=width,
                                      height=height, bits=bits, kind=mode)
        if kind == 6 and size >= 16:
            tag['memory_map_entry_size'], tag['memory_map_entry_version'] = struct.unpack_from('<II', raw, offset + 8)
        report['tags'].append(tag)
        if kind == 0:
            report['tag_chain_valid'] = size == 8 and offset + advance == len(raw)
            return report
        offset += advance
    return report


def parse_prefix(data):
    names = ('status', 'magic', 'address', 'length', 'apic')
    pattern = rb'LEANOS-LAB/1 HANDOFF' + b''.join(
        b' ' + name.encode() + b'=(' + DECIMAL + b')' for name in names) + b'\n'
    header = re.match(pattern, data[:256])
    if header is None:
        raise ValueError('missing or malformed handoff header')
    report = dict(zip(names, map(int, header.groups())))
    if any(report[name] > 0xffffffff for name in names) or report['status'] > 1 or report['apic'] > 255:
        raise ValueError('handoff field width')
    length = report['length']
    address = report['address']
    if report['status']:
        if length:
            raise ValueError('rejected handoff publishes bytes')
    elif (report['magic'] != 0x36d76289 or address < 4096 or address % 8
          or not 16 <= length <= 65536 or length % 8 or address + length > 0x1000000):
        raise ValueError('accepted handoff extent')
    position = header.end()
    raw = bytearray()
    while len(raw) < length:
        count = min(64, length - len(raw))
        line = re.match(rb'LEANOS-LAB/1 HANDOFF-DATA offset=' + str(len(raw)).encode()
                        + rb' hex=([0-9a-f]{' + str(count * 2).encode() + rb'})\n',
                        data[position:position + 192])
        if line is None:
            raise ValueError('missing, unordered, or malformed handoff chunk')
        raw.extend(bytes.fromhex(line[1].decode('ascii')))
        position += line.end()
    end = b'LEANOS-LAB/1 HANDOFF-END\n'
    if not data.startswith(end, position):
        raise ValueError('missing handoff terminator')
    position += len(end)
    if position > MAX_TRANSPORT:
        raise ValueError('handoff transport exceeds bound')
    if length and struct.unpack_from('<I', raw)[0] != length:
        raise ValueError('handoff size changed during observation')
    report.update(schema='leanos-raw-multiboot2-lab-v1',
                  raw_sha256=hashlib.sha256(raw).hexdigest(),
                  platform_admitted=False, display_authorized=False,
                  **describe_tags(raw))
    return position, bytes(raw), report
