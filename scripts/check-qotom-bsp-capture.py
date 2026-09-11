"""Replay the native BSP record against the same boot's root-selected MADT."""
import hashlib
import re
import subprocess
import tempfile
from pathlib import Path

PREFIX = b'LEANOS-LAB/1 NATIVE-BSP '
ARM = b'LEANOS-LAB/1 ECAM-ARM firmware=exact root=checked access=read32\n'
NAMES = ('madt', 'length', 'executing', 'cpuid-edx', 'available', 'apic-base',
         'sample-id', 'status', 'detail', 'offset', 'admitted-id', 'count', 'bound-base')
PATTERN = (PREFIX + b'profile=qotom-bsp-v1' + b''.join(
    b' ' + name.encode() + rb'=(0|[1-9][0-9]*)' for name in NAMES) + b' platform-admitted=0\n')


def extract(raw, protocol, metadata, tables, replay):
    """After ACPI extraction, before ECAM extraction; removes only this record."""
    lines = raw.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(PREFIX)]
    arms = [i for i, line in enumerate(lines) if line.startswith(b'LEANOS-LAB/1 ECAM-ARM ')]
    rejected = lines and lines[-1] == protocol['FINAL'].encode() + b' status=FAIL reason=qotom-native-bsp\n'
    if not arms:
        if indices or rejected:
            raise ValueError('BSP candidate without firmware gate')
        return raw, None  # Existing CPU/ECAM replay must validate the earlier failure.
    if arms != [5] or lines[5] != ARM or indices != [6] or len(lines[6]) > 512:
        raise ValueError('missing, repeated or misplaced BSP record')
    match = re.fullmatch(PATTERN, lines[6])
    if match is None:
        raise ValueError('malformed BSP record')
    values = dict(zip(NAMES, map(int, match.groups())))
    if any(v > 2**64-1 for v in values.values()):
        raise ValueError('BSP scalar overflow')
    if metadata is None:
        raise ValueError('BSP record requires complete ACPI capture')
    # The preceding ACPI decoder binds this ordered list to the selected root.
    # Exclude the independently selected DSDT (which cannot be a MADT).
    madts = [t for t in metadata['tables'][1:] if t['signature_hex'] == b'APIC'.hex()]
    if len(madts) != 1:
        raise ValueError('BSP record requires unique root-selected MADT')
    table = madts[0]
    name = f"{table['address']:016x}.bin"
    data = tables[name]
    if (values['madt'] != table['address'] or values['length'] != table['length'] or
            len(data) != table['length'] or hashlib.sha256(data).hexdigest() != table['sha256']):
        raise ValueError('BSP record disagrees with selected MADT')
    identity = subprocess.run([str(replay), '--identity'], capture_output=True, check=True, timeout=30)
    if identity.stdout != b'LeanOS native BSP replay v1\n':
        raise ValueError('BSP replay identity')
    with tempfile.TemporaryDirectory(prefix='qotom-bsp-replay-') as temp:
        source = Path(temp) / 'madt.bin'
        source.write_bytes(data)
        checked = subprocess.run([str(replay), str(source)] + [str(values[n]) for n in
            ('executing','cpuid-edx','available','apic-base','sample-id')],
            capture_output=True, check=True, timeout=30)
    expected = (' '.join(str(values[n]) for n in
        ('status','detail','offset','admitted-id','count','bound-base')) + '\n').encode()
    if checked.stdout != expected:
        raise ValueError('BSP native result disagrees with generated replay')
    if values['status']:
        if not rejected or len(lines) != 8:
            raise ValueError('BSP rejection followed by unrelated records')
    elif rejected:
        raise ValueError('matching BSP candidate has rejection terminal')
    del lines[6]
    return b''.join(lines), {'schema': 'leanos-native-bsp-capture-v1',
        'observation': values, 'madt_sha256': table['sha256'],
        'platform_admitted': False, 'ap_dormancy_established': False}
