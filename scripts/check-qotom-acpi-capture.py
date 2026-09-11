"""Reconstruct a complete root-selected lab ACPI capture without admission."""
import hashlib
import re
import runpy
import struct
from pathlib import Path

HANDOFF = runpy.run_path(str(Path(__file__).with_name('check-qotom-handoff-capture.py')))
D = HANDOFF['DECIMAL']
BEGIN = b'LEANOS-LAB/1 ACPI-BEGIN '


def selected_root(info):
    tags = HANDOFF['describe_tags'](info)
    if not tags['tag_chain_valid']:
        raise ValueError('ACPI capture requires valid handoff tag chain')
    modern = [t for t in tags['tags'] if t['type'] == 15]
    legacy = [t for t in tags['tags'] if t['type'] == 14]
    if len(modern) > 1 or len(legacy) > 1 or not modern + legacy:
        raise ValueError('ambiguous or absent RSDP')
    tag = (modern or legacy)[0]
    rsdp = info[tag['offset'] + 8:tag['offset'] + tag['size']]
    if len(rsdp) < 20 or rsdp[:8] != b'RSD PTR ' or sum(rsdp[:20]) % 256:
        raise ValueError('RSDP legacy checksum or signature')
    if modern:
        if len(rsdp) < 36 or rsdp[15] < 2 or struct.unpack_from('<I', rsdp, 20)[0] != len(rsdp) or sum(rsdp) % 256:
            raise ValueError('RSDP extended envelope')
        address = struct.unpack_from('<Q', rsdp, 24)[0]
        if address:
            return 2, address
    return 1, struct.unpack_from('<I', rsdp, 16)[0]


def fadt_dsdt_address(raw):
    if (len(raw) < 116 or len(raw) > 65536 or raw[:4] != b'FACP' or
            struct.unpack_from('<I', raw, 4)[0] != len(raw) or
            (raw[8] != 1 and raw[8] < 3)):
        raise ValueError('unsupported FADT envelope/revision')
    address = struct.unpack_from('<I', raw, 40)[0]
    if raw[8] >= 3:
        if len(raw) < 148:
            raise ValueError('truncated extended FADT')
        address = struct.unpack_from('<Q', raw, 140)[0] or address
    if not 0 < address <= 2**32 - 36:
        raise ValueError('unsupported DSDT address')
    return address


def extract(data, handoff, dsdt=False):
    start = data.find(BEGIN)
    if start < 0:
        if b'FINAL status=FAIL reason=qotom-platform-pending\n' in data:
            raise ValueError('successful diagnostic lacks requested ACPI capture')
        return data, None, {}
    if data.count(BEGIN) != 1:
        raise ValueError('repeated ACPI capture')
    block = data[start:]
    match = re.match(rb'LEANOS-LAB/1 ACPI-BEGIN root-kind=([12]) root-address=(' + D + rb') tables=(' + D + rb')'
                     + (b' dsdt=1' if dsdt else b'') + b'\n', block)
    if match is None:
        raise ValueError('invalid ACPI header')
    kind, address, count = map(int, match.groups())
    if not 1 <= count <= 256 or (kind, address) != selected_root(handoff):
        raise ValueError('ACPI root selection or count mismatch')
    position = match.end()
    files, tables, addresses = {}, [], []
    budget = 65536 - len(handoff)
    for index in range(count + 1 + int(dsdt)):
        header = re.match(rb'LEANOS-LAB/1 ACPI-TABLE index=' + str(index).encode()
                          + rb' address=(' + D + rb') length=(' + D + rb')\n', block[position:position + 128])
        if header is None:
            raise ValueError('missing or unordered ACPI table')
        physical, length = map(int, header.groups())
        if not 0 < physical < 2**32 or not 36 <= length <= budget or physical + length > 2**32 or physical in addresses:
            raise ValueError('ACPI table extent, budget, or duplicate')
        budget -= length
        addresses.append(physical)
        position += header.end()
        raw = bytearray()
        while len(raw) < length:
            chunk = min(64, length - len(raw))
            line = re.match(rb'LEANOS-LAB/1 ACPI-DATA offset=' + str(len(raw)).encode()
                            + rb' hex=([0-9a-f]{' + str(chunk * 2).encode() + rb'})\n', block[position:position + 192])
            if line is None:
                raise ValueError('missing or malformed ACPI chunk')
            raw.extend(bytes.fromhex(line[1].decode()))
            position += line.end()
        raw = bytes(raw)
        if struct.unpack_from('<I', raw, 4)[0] != length or sum(raw) % 256:
            raise ValueError('ACPI table length or checksum')
        files[f'{physical:016x}.bin'] = raw
        tables.append({'index': index, 'address': physical, 'length': length,
                       'signature_hex': raw[:4].hex(), 'sha256': hashlib.sha256(raw).hexdigest()})
    end = b'LEANOS-LAB/1 ACPI-END\n'
    if not block.startswith(end, position):
        raise ValueError('missing ACPI end')
    position += len(end)
    root = files[f'{addresses[0]:016x}.bin']
    width = 4 if kind == 1 else 8
    if addresses[0] != address or root[:4] != (b'RSDT' if kind == 1 else b'XSDT') or len(root) != 36 + count * width:
        raise ValueError('ACPI root shape or address')
    expected = [int.from_bytes(root[i:i + width], 'little') for i in range(36, len(root), width)]
    if addresses[1:count + 1] != expected:
        raise ValueError('ACPI children differ from complete ordered root list')
    if dsdt:
        fadts = [t for t in tables[1:count + 1] if t['signature_hex'] == b'FACP'.hex()]
        if len(fadts) != 1:
            raise ValueError('DSDT requires unique root-selected FADT')
        parent = fadts[0]['address']
        selected = fadt_dsdt_address(files[f'{parent:016x}.bin'])
        child = tables[-1]
        if child['address'] != selected or child['signature_hex'] != b'DSDT'.hex():
            raise ValueError('DSDT differs from FADT selection')
        if any(child['address'] < t['address'] + t['length'] and
               t['address'] < child['address'] + child['length'] for t in tables[:-1]):
            raise ValueError('DSDT overlaps root-selected table')
    report = {'schema': 'leanos-native-acpi-lab-v1', 'root_kind': kind,
              'root_address': address, 'tables': tables, 'platform_admitted': False,
              'handoff_sha256': hashlib.sha256(handoff).hexdigest()}
    if dsdt:
        report.update(schema='leanos-native-acpi-dsdt-lab-v1', dsdt_fadt_address=parent,
                      dsdt_address=selected, aml_executed=False)
    return data[:start] + block[position:], report, files
