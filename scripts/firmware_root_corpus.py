"""Root-stage normalization for firmware-corpus.py (no firmware repair)."""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import struct


@dataclass(frozen=True)
class RootReplay:
    info: bytes
    root: bytes
    root_address: int
    tables: tuple[tuple[int, bytes], ...]
    executing_override: int | None = None
    magic: int = 0x36d76289
    info_address: int = 0x1000

    def digest(self):
        # Content-only encoding: output paths never affect normalized identity.
        content = {
            'info': self.info.hex(), 'root': self.root.hex(),
            'root_address': self.root_address,
            'tables': [[address, data.hex()] for address, data in self.tables],
        }
        if (self.magic, self.info_address) != (0x36d76289, 0x1000):
            content.update(magic=self.magic, info_address=self.info_address)
        if self.executing_override is not None:
            content['executing_override'] = self.executing_override
        return hashlib.sha256(json.dumps(content, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

    def write(self, target: Path):
        target.mkdir(parents=True, exist_ok=True)
        info = target / 'info.bin'
        root = target / 'root.bin'
        info.write_bytes(self.info)
        root.write_bytes(self.root)
        header = f'{self.root_address}\t{info}\t{root}'
        if (self.magic, self.info_address) != (0x36d76289, 0x1000):
            header += f'\t{self.magic}\t{self.info_address}'
        lines = [header]
        for index, (address, data) in enumerate(self.tables):
            table = target / f'table-{index}.bin'
            table.write_bytes(data)
            lines.append(f'{address}\t{table}')
        bundle = target / 'bundle.tsv'
        bundle.write_text('\n'.join(lines) + '\n')
        return bundle


def capture_files(directory: Path):
    """Exact supported inventory; never allow manifest paths to escape a case."""
    if directory.is_symlink() or (directory / 'acpi').is_symlink():
        raise ValueError('capture directories must not be symlinks')
    freebsd = (directory / 'acpi/addresses.json').exists()
    files = {'memmap.tsv', 'acpi/APIC.bin', 'executing-apic-id.txt',
             'provenance.json', 'acpi/RSDP.bin'}
    if freebsd:
        files.update({'acpi/addresses.json', 'efi-map.bin', 'cpu0-sample.txt', 'acpi-root-address.txt'})
    else:
        files.add('acpi/addresses.txt')
    for kind in ('RSDT', 'XSDT'):
        if (directory / f'acpi/{kind}.bin').exists():
            files.add(f'acpi/{kind}.bin')
    table_dir = directory / 'acpi/root-tables'
    if not table_dir.is_dir() or table_dir.is_symlink():
        raise ValueError('root-tables must be a real directory')
    for path in table_dir.iterdir():
        if not re.fullmatch(r'[0-9a-f]{16}\.bin', path.name) or not path.is_file() or path.is_symlink():
            raise ValueError('unsupported physical table file')
        files.add(f'acpi/root-tables/{path.name}')
    if len(files) > 520:
        raise ValueError('too many physical table files')
    for name in files:
        path = directory / name
        if not path.is_file() or path.is_symlink():
            raise ValueError(f'missing or symlinked capture file {name}')
    actual = {str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() or p.is_symlink()}
    if actual != files:
        raise ValueError('capture contains unaccounted files')
    return files


def validate_freebsd_projection(directory: Path):
    """Bind derived TSV/CPU identity to exact retained FreeBSD source bytes."""
    import importlib.util
    source = Path(__file__).resolve().parents[1] / 'hardware/lab/project-freebsd-efi-map.py'
    spec = importlib.util.spec_from_file_location('freebsd_efi_projection', source)
    projection = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(projection)
    with (directory / 'efi-map.bin').open('rb') as stream:
        raw = stream.read(projection.MAX_BYTES + 33)
    if (directory / 'memmap.tsv').read_text() != projection.render(projection.project(raw)):
        raise ValueError('FreeBSD EFI projection differs from retained raw map')
    sample = (directory / 'cpu0-sample.txt').read_text().splitlines()
    producer = source.with_name('capture-cpuid.c')
    if not sample or sample[0] != hashlib.sha256(producer.read_bytes()).hexdigest():
        raise ValueError('FreeBSD CPU sample producer digest differs')
    leaf1 = [line.split() for line in sample if line.startswith('00000001\t00000000\t')]
    if len(leaf1) != 1 or len(leaf1[0]) != 6 or not all(re.fullmatch('[0-9a-f]{8}', word) for word in leaf1[0]):
        raise ValueError('FreeBSD CPU sample lacks one complete leaf 1')
    executing = int((directory / 'executing-apic-id.txt').read_text())
    if int(leaf1[0][3], 16) >> 24 != executing:
        raise ValueError('FreeBSD executing identity differs from CPU0 sample')
    addresses = json.loads((directory / 'acpi/addresses.json').read_text())
    if not isinstance(addresses, dict) or set(addresses) != {'RSDP', 'RSDT', 'XSDT', 'APIC'} or any(
            type(value) is not int or not 0 < value < 2**64 for value in addresses.values()):
        raise ValueError('malformed FreeBSD physical address inventory')
    apic = addresses.get('APIC')
    if type(apic) is not int or not 0 < apic < 2**64:
        raise ValueError('FreeBSD APIC address is invalid')
    if (directory / 'acpi/APIC.bin').read_bytes() != (directory / f'acpi/root-tables/{apic:016x}.bin').read_bytes():
        raise ValueError('FreeBSD MADT differs from addressed physical copy')
    if addresses.get('RSDP') != int((directory / 'acpi-root-address.txt').read_text(), 0):
        raise ValueError('FreeBSD RSDP address differs from sysctl sample')


def from_capture(directory: Path, memory_info: bytes):
    """Wrap exactly one observed RSDP and retain every selected table copy.

    Each supported capture observes one RSDP, so the converter emits one matching
    Multiboot2 ACPI tag. It never invents a second old/new root, changes a
    checksum, or treats a summary's prose as a replacement for table bytes.
    """
    def read(name, bound=65536):
        path = directory / name
        if path.stat().st_size > bound:
            raise ValueError(f'{name} exceeds capture bounds')
        return path.read_bytes()

    capture_files(directory)
    rsdp = read('acpi/RSDP.bin', 36)
    if len(rsdp) < 20:
        raise ValueError('RSDP too short to select a root kind')
    revision = rsdp[15]
    if revision == 0:
        kind, width, tag_type = 'RSDT', 4, 14
        advertised = int.from_bytes(rsdp[16:20], 'little')
    elif revision >= 2 and len(rsdp) >= 32:
        kind, width, tag_type = 'XSDT', 8, 15
        advertised = int.from_bytes(rsdp[24:32], 'little')
    else:
        raise ValueError('unsupported captured RSDP revision/length')
    # Retain the address inventory separately from the table bytes. ACPICA
    # supplies an independent summary; FreeBSD records the sysctl RSDP and
    # the physical addresses followed by the bounded capture procedure.
    if (directory / 'acpi/addresses.json').exists():
        addresses = json.loads(read('acpi/addresses.json').decode('ascii'))
        if not isinstance(addresses, dict) or set(addresses) != {'RSDP', 'RSDT', 'XSDT', 'APIC'} or any(
                type(value) is not int or not 0 < value < 2**64 for value in addresses.values()):
            raise ValueError('malformed FreeBSD physical address inventory')
    else:
        addresses = {}
        for line in read('acpi/addresses.txt').decode('ascii').splitlines():
            match = re.fullmatch(r'ACPI: (RSDP|RSDT|XSDT|APIC) (0x[0-9A-Fa-f]+) [0-9A-Fa-f]+ \(.*\)', line)
            if not match or match[1] in addresses:
                raise ValueError('malformed or duplicate physical address summary')
            addresses[match[1]] = int(match[2], 16)
    if kind not in addresses or not 0 < addresses[kind] < 2**64:
        raise ValueError('selected root physical address is unavailable')
    if advertised == 0:
        raise ValueError('RSDP advertises a zero root address')
    root = read(f'acpi/{kind}.bin')
    if len(root) < 36 or (len(root)-36) % width or (len(root)-36)//width > 256:
        raise ValueError('unsupported root vector capture bounds')
    tables = []
    seen = set()
    for offset in range(36, len(root), width):
        address = int.from_bytes(root[offset:offset+width], 'little')
        if address in seen:
            continue  # Keep the root vector unchanged; elide duplicate copies.
        seen.add(address)
        tables.append((address, read(f'acpi/root-tables/{address:016x}.bin')))
    if len(root) + sum(len(data) for _, data in tables) > 1048576:
        raise ValueError('aggregate root copies exceed one MiB')
    if len(memory_info) < 16 or memory_info[-8:] != struct.pack('<II', 0, 8):
        raise ValueError('memory handoff lacks its terminal end tag')
    tag = struct.pack('<II', tag_type, 8+len(rsdp)) + rsdp
    tag += bytes(-len(tag) % 8)
    info = memory_info[:-8] + tag + memory_info[-8:]
    if len(info) > 65536:
        raise ValueError('root handoff exceeds 64 KiB')
    info = struct.pack('<I', len(info)) + info[4:]
    return RootReplay(info, root, addresses[kind], tuple(tables))


def lean_query(replay, executing):
    if replay.executing_override is not None:
        executing = replay.executing_override
    def array(data):
        return '⟨#[' + ', '.join(map(str, data)) + ']⟩'
    addresses = '#[' + ', '.join(str(a) for a, _ in replay.tables) + ']'
    tables = '#[' + ', '.join(array(b) for _, b in replay.tables) + ']'
    return (f'BootMemoryMapDecoderABI.capturedRootQuery {replay.magic} {replay.info_address} '
            f'{array(replay.info)} {array(replay.root)} {replay.root_address} '
            f'{addresses} {tables} {executing}')


def mutations(replay):
    """Derived adversarial inputs; checksum repairs here isolate the named fault.
    Captured inputs and the base normalization path are never repaired.
    """
    from dataclasses import replace

    def changed(data, offset):
        b = bytearray(data); b[offset] ^= 1; return bytes(b)

    def sdt(data):
        b = bytearray(data)
        struct.pack_into('<I', b, 4, len(b))
        b[9] = 0; b[9] = -sum(b) % 256
        return bytes(b)

    def info(data):
        return struct.pack('<I', len(data)) + data[4:]

    offset = 8
    while offset < len(replay.info):
        kind, size = struct.unpack_from('<II', replay.info, offset)
        if kind in (14, 15): break
        if size < 8: raise ValueError('malformed normalized tag')
        offset += (size+7)//8*8
    else: raise ValueError('normalized handoff has no ACPI tag')
    tag_end = offset + (size+7)//8*8
    payload = offset + 8
    madt_index = next(i for i, (_, b) in enumerate(replay.tables) if b[:4] == b'APIC')
    madt_address, madt = replay.tables[madt_index]

    def table(data):
        tables = list(replay.tables); tables[madt_index] = (madt_address, data)
        return replace(replay, tables=tuple(tables))

    bad_length = bytearray(replay.root)
    struct.pack_into('<I', bad_length, 4, len(bad_length)+1)
    width = 4 if replay.root[:4] == b'RSDT' else 8
    result = {
        'root-rsdp-signature': replace(replay, info=changed(replay.info, payload)),
        'root-rsdp-legacy-checksum': replace(replay, info=changed(replay.info, payload+8)),
        'root-missing-rsdp': replace(replay, info=info(replay.info[:offset]+replay.info[tag_end:])),
        'root-duplicate-rsdp': replace(replay, info=info(replay.info[:tag_end]+replay.info[offset:tag_end]+replay.info[tag_end:])),
        'root-checksum': replace(replay, root=changed(replay.root, 9)),
        'root-declared-length': replace(replay, root=bytes(bad_length)),
        'root-truncated': replace(replay, root=replay.root[:-1]),
        'root-wrong-address': replace(replay, root_address=0),
        'root-missing-copy': replace(replay, tables=replay.tables[1:]),
        'root-duplicate-copy': replace(replay, tables=replay.tables+(replay.tables[0],)),
        'root-zero-entry': replace(replay, root=sdt(replay.root[:36]+bytes(width)+replay.root[36+width:])),
        'root-missing-madt': table(sdt(b'XXXX'+madt[4:])),
        'root-duplicate-madt': replace(replay, root=sdt(replay.root+madt_address.to_bytes(width,'little'))),
        'root-madt-checksum': table(changed(madt,9)),
        'root-madt-truncated': table(madt[:-1]),
        'root-madt-unknown-record': table(sdt(madt+bytes([9,16])+bytes(14))),
    }
    single = bytearray(madt)
    cursor, enabled = 44, False
    processor_records, other_records = [], []
    while cursor < len(single):
        record_kind, record_size = single[cursor:cursor+2]
        if record_size < 2 or cursor+record_size > len(single):
            raise ValueError('invalid captured MADT record bounds')
        if record_kind == 0:
            if record_size != 8:
                raise ValueError('invalid captured MADT processor record length')
            processor_records.append(madt[cursor:cursor+record_size])
            struct.pack_into('<I', single, cursor+4, 0 if enabled else 1)
            enabled = True
        else:
            other_records.append(madt[cursor:cursor+record_size])
        cursor += record_size
    if not processor_records:
        raise ValueError('captured MADT has no processor record to mutate')
    # Preserve every non-CPU record. Repair only these derived SDTs so that
    # topology admission, rather than the checksum gate, sees the defect.
    result['root-duplicate-cpu'] = table(sdt(madt + processor_records[0]))
    result['root-missing-cpus'] = table(sdt(madt[:44] + b''.join(other_records)))
    result['root-bsp-mismatch'] = replace(table(sdt(single)), executing_override=255)
    result['root-executing-overflow'] = replace(replay, executing_override=2**32)
    # Introduce a second, independently checksummed tag with a conflicting
    # legacy OEM identity. This fabricated tag exists only in the mutation.
    opposite = bytearray(replay.info[payload:payload+20])
    opposite[9] ^= 1
    opposite[15] = 0 if kind == 15 else 2
    opposite[8] = 0; opposite[8] = -sum(opposite) % 256
    opposite_kind = 14 if kind == 15 else 15
    if opposite_kind == 15:
        opposite += struct.pack('<IQ',36,replay.root_address) + bytes(4)
        opposite[32] = -sum(opposite) % 256
    opposite_tag = struct.pack('<II',opposite_kind,8+len(opposite)) + opposite
    opposite_tag += bytes(-len(opposite_tag) % 8)
    result['root-conflicting-rsdps'] = replace(replay, info=info(replay.info[:-8]+opposite_tag+replay.info[-8:]))
    if kind == 15:
        result['root-rsdp-extended-checksum'] = replace(replay, info=changed(replay.info,payload+32))
    return result


def rejection_name(words):
    """Names mirror BootTopology and AcpiRootDecoder constructors, including detail."""
    names = {
        20:'rsdp.missingRoot',21:'rsdp.duplicateOldRoot',22:'rsdp.duplicateNewRoot',23:'rsdp.conflictingRoots',
        24:'selectedRootAddressMismatch',26:'madtSelection.untranslatedRootEntry',
        27:'madtSelection.duplicateTranslation',28:'madtSelection.missingMadt',29:'madtSelection.duplicateMadt',
        100:'truncatedTag',101:'malformedTagSize',102:'tagOutOfBounds',103:'missingEndTag',
        104:'misplacedEndTag',105:'tooManyTags',106:'invalidSignature',107:'unsupportedRevision',
        108:'invalidRsdpLength',109:'invalidLegacyChecksum',110:'invalidExtendedChecksum',
        201:'handoff.badMagic',202:'handoff.unalignedInfo',
        300:'copyCountExceeded',301:'copyCountMismatch',302:'copyBytesExceeded',
        303:'tableBytesExceeded',304:'executingApicIdOverflow',305:'handoffBytesExceeded',
    }
    complete = ['entry.truncatedHeader','entry.truncatedRecord','entry.invalidRecordLength',
                'entry.unsupportedRecordKind','entry.processorOverflow','truncatedMadtHeader',
                'sdt.truncatedHeader','sdt.invalidSignature','sdt.invalidLength','sdt.tableTooLarge',
                'sdt.invalidChecksum','sdt.invalidRootPayloadAlignment','sdt.rootEntryOverflow']
    names.update({33+i:'completeMadt.'+name for i,name in enumerate(complete)})
    if len(words) != 5 or words[0] != 1 or words[1] != 2:
        raise ValueError('root rejection needs the five-word decoder projection')
    if words[2] == 25:
        sdt = ['truncatedHeader','invalidSignature','invalidLength','tableTooLarge',
               'invalidChecksum','invalidRootPayloadAlignment','rootEntryOverflow']
        if not 1 <= words[3] <= len(sdt): raise ValueError('unknown root SDT detail')
        return 'decoder-rejected:madtSelection.root.'+sdt[words[3]-1]
    if words[2] not in names: raise ValueError(f'unknown root rejection code {words[2]}')
    return 'decoder-rejected:'+names[words[2]]


def lean_bounds():
    """Synthetic adapter limits, independent of captured firmware rows."""
    lines = ['def rootBoundBytes (n : Nat) : ByteArray := ⟨(List.replicate n (0 : UInt8)).toArray⟩']
    # code, info bytes, root bytes, address count, table count, table bytes, APIC
    fixtures = [(300,0,0,257,0,0,0), (301,0,0,1,0,0,0),
                (302,0,65536,16,16,65536,0), (303,0,65537,0,0,0,0),
                (304,0,0,0,0,0,2**32), (305,65537,0,0,0,0,0)]
    for code, info, root, addresses, tables, size, executing in fixtures:
        query = (f'BootMemoryMapDecoderABI.capturedRootQuery 0x36d76289 0x1000 '
                 f'(rootBoundBytes {info}) (rootBoundBytes {root}) 0 '
                 f'(Array.replicate {addresses} (0 : UInt64)) '
                 f'(Array.replicate {tables} (rootBoundBytes {size})) {executing}')
        lines += [f'example : (List.range 5).map (fun word => {query} (UInt64.ofNat word)) = [1, 2, {code}, 0, 0] := by',
                  '  native_decide']
    return lines


def lean_definitions(replay, executing, prefix):
    """Name large captured byte arrays before constructing the query closure."""
    def array(data):
        return '⟨#[' + ', '.join(map(str, data)) + ']⟩'
    lines = [f'def {prefix}Info : ByteArray := {array(replay.info)}',
             f'def {prefix}Root : ByteArray := {array(replay.root)}']
    for i, (_, data) in enumerate(replay.tables):
        lines.append(f'def {prefix}Table{i} : ByteArray := {array(data)}')
    lines.append(f'def {prefix}Addresses : Array UInt64 := #[' +
                 ', '.join(str(address) for address, _ in replay.tables) + ']')
    lines.append(f'def {prefix}Tables : Array ByteArray := #[' +
                 ', '.join(f'{prefix}Table{i}' for i in range(len(replay.tables))) + ']')
    if replay.executing_override is not None:
        executing = replay.executing_override
    query = (f'BootMemoryMapDecoderABI.capturedRootQuery {replay.magic} {replay.info_address} '
             f'{prefix}Info {prefix}Root {replay.root_address} {prefix}Addresses {prefix}Tables {executing}')
    return lines, query
