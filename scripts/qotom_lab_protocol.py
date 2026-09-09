"""Resolve historical lab expectations through the pinned generated vocabulary."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
manifest = json.loads((ROOT / 'hardware/manifest.json').read_text())
rows = [row for row in manifest['rows'] if row['id'] == 'qotom-j1900-clbtm210-v1']
if len(rows) != 1:
    raise ValueError('missing or ambiguous historical Qotom profile')
ROW = rows[0]
protocol = (ROOT / 'hardware/observations/qotom-20260909/protocol.tsv').read_bytes()
if hashlib.sha256(protocol).hexdigest() != ROW['artifacts']['protocol']:
    raise ValueError('historical generated protocol digest mismatch')
lines = protocol.decode('ascii').splitlines()
if lines[:2] != ['leanos-serial-protocol\t1', 'source-revision\t' + ROW['source_revision']]:
    raise ValueError('historical generated protocol source mismatch')
records = {}
for line in lines[2:]:
    fields = line.split('\t')
    if fields[0] == 'record':
        key = (int(fields[1]), fields[2])
        if key in records:
            raise ValueError('duplicate generated protocol record')
        records[key] = fields[4].encode('ascii')


def record(family, name):
    return records[(family, name)]


EXPECTED_KERNEL = ('\n'.join(ROW['expected_lines']) + '\n').encode('ascii')
for line in ROW['expected_lines']:
    if ' '.join(line.split(' ')[:2]).encode('ascii') not in records.values():
        raise ValueError('historical expectation is outside generated vocabulary')
