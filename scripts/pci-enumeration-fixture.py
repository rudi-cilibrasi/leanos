#!/usr/bin/env python3
"""Emit C input only after verifying the retained raw PCI capture."""
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('capture', ROOT / 'scripts/test-pci-header-capture.py')
capture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(capture)
capture.replay_source()  # Hashes, complete selector list and raw/projection equality.
inventory = json.loads((capture.CAPTURE / 'inventory.json').read_text())
rows = []
for function in inventory['functions']:
    domain, bus, device, slot = map(int, function['selector'].removeprefix('pci').split(':'))
    assert domain == 0 and len(function['words']) == 16
    rows.append('  {' + ', '.join(map(str, (bus, device, slot))) + ', {' +
                ', '.join(f'UINT32_C({word})' for word in function['words']) + '}},')
Path(sys.argv[1]).write_text('#define CAPTURE_COUNT ' + str(len(rows)) + '\n' +
    'static const struct pci_enumeration_header capture[CAPTURE_COUNT] = {\n' +
    '\n'.join(rows) + '\n};\n')
