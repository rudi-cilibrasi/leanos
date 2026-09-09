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

    def digest(self):
        # Content-only encoding: output paths never affect normalized identity.
        return hashlib.sha256(json.dumps({
            'info': self.info.hex(), 'root': self.root.hex(),
            'root_address': self.root_address,
            'tables': [[address, data.hex()] for address, data in self.tables],
        }, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

    def write(self, target: Path):
        target.mkdir(parents=True, exist_ok=True)
        info = target / 'info.bin'
        root = target / 'root.bin'
        info.write_bytes(self.info)
        root.write_bytes(self.root)
        lines = [f'{self.root_address}\t{info}\t{root}']
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
    files = {'memmap.tsv', 'acpi/APIC.bin', 'executing-apic-id.txt',
             'provenance.json', 'acpi/RSDP.bin', 'acpi/addresses.txt'}
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


def from_capture(directory: Path, memory_info: bytes):
    """Wrap exactly one observed RSDP and retain every selected table copy.

    The Linux capture observes one RSDP, so the converter emits one matching
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
    # Preserve addresses from the physical acpidump summary independently of
    # addresses advertised by the RSDP, so disagreement is observable.
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
    def array(data):
        return '⟨#[' + ', '.join(map(str, data)) + ']⟩'
    addresses = '#[' + ', '.join(str(a) for a, _ in replay.tables) + ']'
    tables = '#[' + ', '.join(array(b) for _, b in replay.tables) + ']'
    return (f'BootMemoryMapDecoderABI.capturedRootQuery 0x36d76289 0x1000 '
            f'{array(replay.info)} {array(replay.root)} {replay.root_address} '
            f'{addresses} {tables} {executing}')
