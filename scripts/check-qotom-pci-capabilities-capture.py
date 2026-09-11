"""Validate bounded conventional capability records; never grant admission.

Call after removing earlier firmware/CPU extension records. The returned
projection MUST still pass the native PCI inventory replay. A failure status
is retained as a device observation: absent raw failed reads cannot be replayed.
"""
import hashlib
import re

SUMMARY = b'LEANOS-LAB/1 PCI-CAPS '
ENTRY = b'LEANOS-LAB/1 PCI-CAP '
NATIVE = b'LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 status=0 index=0 count=16\n'
DECIMAL = rb'(0|[1-9][0-9]{0,9})'


def extract(raw, protocol):
    if len(raw) > 131072 or not raw.endswith(b'\n'):
        raise ValueError('capability capture bounds')
    lines = raw.splitlines(keepends=True)
    candidates = [i for i, line in enumerate(lines) if line.startswith((SUMMARY, ENTRY))]
    accepted = [i for i, line in enumerate(lines) if line == NATIVE]
    failure = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-pci-capabilities\n'
    pending = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
    if not accepted:
        if candidates or lines[-1] == failure:
            raise ValueError('capabilities without accepted native inventory')
        return raw, None  # The caller validates the earlier rejection.
    if len(accepted) != 1 or not candidates or candidates[0] != accepted[0] + 1:
        raise ValueError('missing or misplaced capability records')
    start = accepted[0]
    header_pattern = (re.escape(protocol['PCI-HEADER'].encode()) +
        rb' codec=1 index=' + DECIMAL + rb' width=19 words=(' +
        rb'(?:0|[1-9][0-9]{0,9})(?:,(?:0|[1-9][0-9]{0,9})){18})\n')
    headers = []
    for line in lines[:start]:
        if line.startswith(protocol['PCI-HEADER'].encode()):
            match = re.fullmatch(header_pattern, line)
            if not match or int(match[1]) != len(headers):
                raise ValueError('capability source header order or framing')
            words = list(map(int, match[2].split(b',')))
            if any(x > limit for x, limit in zip(words, [255,31,7] + [0xffffffff]*16)):
                raise ValueError('capability source header width')
            headers.append(words)
    if len(headers) != 16:
        raise ValueError('capability source inventory count')
    cursor = start + 1
    functions = []
    rejected = False
    for index, words in enumerate(headers):
        if cursor >= len(lines):
            raise ValueError('truncated capability summary')
        pattern = (SUMMARY + rb'profile=conventional-v1 index=' + str(index).encode() +
                   rb' status=' + DECIMAL + rb' offset=' + DECIMAL + rb' count=' + DECIMAL + rb'\n')
        match = re.fullmatch(pattern, lines[cursor])
        if not match:
            raise ValueError('capability summary order or framing')
        status, offset, count = map(int, match.groups())
        cursor += 1
        if status > 6 or count > 48 or offset > 255:
            raise ValueError('capability summary bounds')
        entries = []
        expected = words[16] & 255 if words[4] & 0x100000 else 0
        seen = set()
        if status:
            # ARGUMENT is impossible following the accepted native inventory.
            # No partial list is published, so traversal failure details are
            # observations only, not independently replayable hardware reads.
            if status == 1 or count:
                raise ValueError('invalid capability failure publication')
            if status == 3 and offset not in (0,4,12,52):
                raise ValueError('invalid initial drift offset')
            if status == 2 and offset not in (0,4,12,52) and not (64 <= offset <= 252 and offset % 4 == 0):
                raise ValueError('invalid read failure offset')
            if status == 4 and (offset == 0 or (offset >= 64 and offset % 4 == 0)):
                raise ValueError('invalid pointer failure offset')
            if status in (5,6) and not (64 <= offset <= 252 and offset % 4 == 0):
                raise ValueError('invalid traversal failure offset')
            rejected = True
        else:
            if offset:
                raise ValueError('successful list has failure offset')
            for slot in range(count):
                if cursor >= len(lines):
                    raise ValueError('truncated capability list')
                pattern = (ENTRY + rb'index=' + str(index).encode() + rb' slot=' + str(slot).encode() +
                           rb' offset=' + DECIMAL + rb' raw=' + DECIMAL + rb'\n')
                match = re.fullmatch(pattern, lines[cursor])
                if not match:
                    raise ValueError('capability entry order or framing')
                address, value = map(int, match.groups())
                if (address != expected or address < 64 or address > 252 or address % 4 or
                        address in seen or value > 0xffffffff or value & 255 == 255):
                    raise ValueError('capability link, bounds, cycle or absent ID')
                seen.add(address)
                entries.append({'offset': address, 'raw': value})
                expected = (value >> 8) & 255
                cursor += 1
            if expected:
                raise ValueError('unterminated capability list')
        functions.append({'index': index, 'address': words[:3], 'status': status,
                          'offset': offset, 'headers': entries})
        if rejected:
            break
    if cursor != len(lines) - 1 or lines[cursor] != (failure if rejected else pending):
        raise ValueError('capability terminal or trailing records')
    projection = b''.join(lines[:start+1]) + pending
    return projection, {'schema': 'leanos-pci-capability-capture-v1',
        'capture_sha256': hashlib.sha256(raw).hexdigest(), 'functions': functions,
        'terminal_reason': 'qotom-pci-capabilities' if rejected else 'qotom-platform-pending',
        'failed_reads_replayed': False, 'platform_admitted': False,
        'dma_quarantine_established': False}
