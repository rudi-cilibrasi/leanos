#!/usr/bin/env python3
"""Decode reset-related header fields from a retained native observation."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = root / 'hardware/lab/observations/qotom-native-capabilities-20260911'
manifest_bytes = (source / 'manifest.json').read_bytes()
manifest = json.loads(manifest_bytes)
raw = (source / 'cycle-1/result.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != manifest['files']['cycle-1/result.json']:
    raise SystemExit('native capability capture hash mismatch')
r = json.loads(raw)
if r['diagnostic']['native_kernel_inventory'] != {'status': 0, 'index': 0, 'count': 16}:
    raise SystemExit('native inventory not accepted')
functions = r['pci_capabilities']['functions']
headers = r['diagnostic']['pci_headers']
if len(functions) != 16 or len(headers) != 16:
    raise SystemExit('incomplete capability capture')
rows = []
for i, (function, header) in enumerate(zip(functions, headers)):
    if function['index'] != i or function['address'] != header[:3] or function['status']:
        raise SystemExit('capability identity or status mismatch')
    entries = function['headers']
    af = [entry for entry in entries if entry['raw'] & 255 == 0x13]
    pcie = [entry for entry in entries if entry['raw'] & 255 == 0x10]
    if len(af) > 1 or len(pcie) > 1:
        raise SystemExit('ambiguous reset-related capability')
    row = {'bdf': '%02x:%02x.%x' % tuple(header[:3]),
           'vendor_device': '%04x:%04x' % (header[3] & 65535, header[3] >> 16),
           'af': None, 'pcie': None}
    if af:
        entry = af[0]
        length = (entry['raw'] >> 16) & 255
        bits = entry['raw'] >> 24
        row['af'] = {'offset': entry['offset'], 'raw_header': entry['raw'],
            'length': length, 'tp_advertised': bool(bits & 1),
            'flr_advertised': bool(bits & 2), 'reserved_capability_bits': bits & ~3,
            'standard_six_byte_shape': length == 6 and entry['offset'] + 6 <= 256,
            'control_offset': entry['offset'] + 4,
            'status_offset': entry['offset'] + 5,
            'control_observed': False, 'pending_status_observed': False}
    if pcie:
        entry = pcie[0]
        flags = entry['raw'] >> 16
        row['pcie'] = {'offset': entry['offset'], 'raw_header': entry['raw'],
            'version': flags & 15, 'device_type': (flags >> 4) & 15,
            'device_capabilities_observed': False, 'flr_advertised': None}
    rows.append(row)
print(json.dumps({'schema': 'leanos-qotom-reset-header-observation-v1',
    'source': str((source / 'cycle-1/result.json').relative_to(root)),
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'source_manifest_sha256': hashlib.sha256(manifest_bytes).hexdigest(),
    'reset_performed': False, 'dma_quarantine_established': False,
    'functions': rows}, indent=2))
