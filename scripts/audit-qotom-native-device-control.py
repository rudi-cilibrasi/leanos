#!/usr/bin/env python3
"""Summarize observed Command bits; never infer containment or authorize writes."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = root / 'hardware/lab/observations/qotom-native-inventory-20260911'
manifest_bytes = (source / 'manifest.json').read_bytes()
manifest = json.loads(manifest_bytes)
name = 'cycle-1/result.json'
raw = (source / name).read_bytes()
if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
    raise SystemExit('native capture hash mismatch')
result = json.loads(raw)
diagnostic = result['diagnostic']
if diagnostic['native_kernel_inventory'] != {'status': 0, 'index': 0, 'count': 16}:
    raise SystemExit('capture does not report a complete native inventory match')
headers = diagnostic['pci_headers']
if len(headers) != 16:
    raise SystemExit('unexpected inventory size')
functions = []
for header in headers:
    bus, device, fn, *words = header
    command = words[1] & 0xffff
    layout = (words[3] >> 16) & 0x7f
    if len(words) != 16 or layout not in (0, 1):
        raise SystemExit('unsupported header shape')
    functions.append({'bdf': f'{bus:02x}:{device:02x}.{fn}',
        'vendor_device': f'{words[0] & 0xffff:04x}:{words[0] >> 16:04x}',
        'class_code': f'{words[2] >> 8:06x}', 'command': f'{command:04x}',
        'status': f'{words[1] >> 16:04x}', 'io_decode': bool(command & 1),
        'memory_decode': bool(command & 2), 'bus_master_enable': bool(command & 4),
        'layout': 'bridge' if layout else 'endpoint',
        'raw_bar_dwords': [f'{w:08x}' for w in words[4:6 if layout else 10]]})
fixed = {'00:00.0': '8086:0f00', '00:1f.0': '8086:0f1c'}
for bdf, identity in fixed.items():
    if not any(f['bdf'] == bdf and f['vendor_device'] == identity and
               f['command'] == '0007' for f in functions):
        raise SystemExit('fixed-command observation differs from audited hardware')
print(json.dumps({'schema': 'leanos-native-device-control-audit-v1',
    'source': str((source / name).relative_to(root)),
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'source_manifest_sha256': hashlib.sha256(manifest_bytes).hexdigest(),
    'bme_set': [f['bdf'] for f in functions if f['bus_master_enable']],
    'bme_clear': [f['bdf'] for f in functions if not f['bus_master_enable']],
    'fixed_command_bme': list(fixed),
    'other_bme_set': [f['bdf'] for f in functions if f['bus_master_enable'] and f['bdf'] not in fixed],
    'containment_established': False, 'writes_authorized': False,
    'functions': functions}, indent=2))
