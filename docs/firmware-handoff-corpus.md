# Firmware handoff corpus

The firmware handoff corpus (`firmware-corpus/`) replays real-firmware E820
memory maps and ACPI MADTs through the boot decoders that admit a platform
before CPL3: the bounded Multiboot2 byte decoder
(`LeanOS.BootMemoryMapDecoder`, [boot memory map](boot-memory-map.md)) and
the single-core topology admission of `LeanOS.BootTopology`. Every row is a
capture from a named machine or firmware, converted deterministically into the
exact immutable bytes the decoders consume, with the expected decode or typed
rejection pinned in the manifest and checked by both the Lean definitions and
the generated C. It is decoder and integration evidence for issue #292: the
corpus proves what the existing decoders do with messy firmware shapes, not
that LeanOS booted or admitted any of the source machines.

## Layout

`firmware-corpus/manifest.json` (schema `leanos-firmware-corpus-v1`) lists the
cases. Each case owns `firmware-corpus/<case id>/` holding the raw capture:

| File | Content |
| --- | --- |
| `memmap.tsv` | The firmware-provided E820 map as Linux exposes it in `/sys/firmware/memmap`: one row per entry in sysfs index order with hexadecimal start, inclusive end, and Linux's type name. |
| `acpi/APIC.bin` | The raw MADT copied from `/sys/firmware/acpi/tables/APIC`, complete with its SDT header and checksum. |
| `executing-apic-id.txt` | The APIC identity of Linux processor 0, the bootstrap processor the kernel booted on, from `/proc/cpuinfo`. |
| `provenance.json` | Capture tool identity and digest, kernel, sources, processor count, vendor/model/firmware strings, and the SHA-256 of every other file. Guest captures add a `guest` object naming the emulator, firmware, and package pins. |

The manifest entry records the machine profile, how and when the capture was
taken, who permitted it, what was redacted and why it cannot affect the
result, the SHA-256 of each raw file, the BSP and executing APIC identities
handed to admission, the expected result of each stage, and the typed
rejection each derived mutation must produce. `root_tables` is
`unavailable` for captures without physical root bytes. Rows marked `acpidump`
also retain the RSDP, root tables, physical address summary, and an exact copy
of each referenced table. Their `root_replay` expectation pins all five result
words and the content digest of the normalized root replay.

The corpus includes five virtual-firmware captures and two physical-machine captures:

| Case | Firmware | Memory map | Topology |
| --- | --- | --- | --- |
| `hyperv-wsl2-24cpu` | Microsoft Hyper-V UEFI (WSL2 utility VM) | 5 entries, decoded | 24 enabled processors, rejected `multipleEnabledProcessors` |
| `qemu-seabios-q35-1cpu` | SeaBIOS on QEMU q35 | 9 entries, decoded | 1 processor, admitted |
| `qemu-ovmf-q35-4cpu` | OVMF (EDK II) on QEMU q35, booted through the EFI stub | 19 interleaved RAM/NVS/reserved entries, decoded | 4 enabled processors, rejected `multipleEnabledProcessors` |
| `intel-nuc10-fncml0053` | Intel NUC10i7FNH, FNCML357.0053 firmware | 18 interleaved RAM/NVS/reserved entries, decoded | 12 enabled processors, rejected `multipleEnabledProcessors` |
| `qemu-seabios-q35-roots-1cpu` | SeaBIOS physical root capture | 9 entries, decoded | RSDP/RSDT and 5 referenced tables; topology admitted |
| `qemu-ovmf-q35-roots-4cpu` | OVMF physical root capture | 19 entries, decoded | RSDP/XSDT and 6 referenced tables; rejected `multipleEnabledProcessors` |
| `qotom-j1900-freebsd-uefi` | Qotom J1900 / AMI CLBTM210, FreeBSD UEFI | 30 EFI descriptors conservatively projected, decoded | Exact RSDP/XSDT and referenced tables; rejected `multipleEnabledProcessors` |

The QEMU rows are real firmware captured through the same Linux
procedure as a physical machine, not repository-constructed fixtures; the
Hyper-V row is a physical host's virtualization firmware. The NUC row was
collected directly on the physical development host (mgnuc), using that same
procedure. Its MADT retains the firmware OEM table identifier `NUC9i5FN` even
though DMI identifies the machine as NUC10i7FNH; neither value is repaired.
This is a Linux-observed firmware replay, not a LeanOS boot capture. The NUC
root-table bytes could not be read, so it adds no root-selection evidence.

## FreeBSD Qotom source contract

The Qotom row uses `root_tables: freebsd-physical`. Its raw EFI map and ACPI
bytes were captured during a FreeBSD UEFI boot, not a legacy GRUB boot. The
[conservative EFI projection](../hardware/lab/FREEBSD-FIRMWARE.md) preserves
descriptor order and bounds, admits only conventional memory as usable, and
reserves loader, boot-services and runtime regions. The corpus gate recomputes
`memmap.tsv` from the retained `efi-map.bin`; it never relabels the raw map as
Linux E820. The projection is a hosted input reconstruction, not a live
allocation policy or an assertion about GRUB's actual memory map.

Physical root addresses are recorded in `acpi/addresses.json`. The RSDP
address is bound to the retained `machdep.acpi_root` sysctl output. RSDT/XSDT
addresses follow the exact RSDP, and table addresses follow the exact root
vectors. The full source observation retains commands, header/full/repeat
reads and before/after boot identity. The per-case MADT must match its
addressed physical copy. CPU0's sampled CPUID leaf 1 binds the hosted executing
identity, but is not evidence that LeanOS runs on the BSP or leaves APs dormant.

The UEFI MADT's four Local APIC NMI routing records contain unusual LINT bytes
247, 166, 206 and 39. An earlier decoded Qotom inventory printed zero for all
four fields. No bytes are repaired. The current topology decoder validates
these records' kind and length but skips routing fields, so the topology
result establishes no safety property about that routing. The ACPI tables
also reside outside LeanOS's initial 16 MiB identity mapping. The existing
`copy_acpi_physical_bytes` path already copies through a temporary
supervisor-only NX mapping and accepts physical ranges below 4 GiB; the
captured table ranges fit that limit. Their location does not establish a
missing copy mechanism. Actual legacy handoff and physical validation of that
existing path, BSP-only admission and execution remain required by issue #331.

## Capture procedure

`scripts/capture-firmware-handoff.sh <directory>` runs on the source machine
from a Linux live environment as root or with passwordless sudo. It copies
the sysfs memory map and the raw MADT, records processor 0's APIC identity,
and writes `provenance.json`. It reads only vendor, model, and firmware
version strings from DMI; it never reads serial numbers, UUIDs, or network
addresses, and it never reorders, merges, or repairs what it copies. When
`acpidump` is available it attempts physical-memory mode (`-c off`) and
records the RSDP, RSDT, and XSDT for root-stage replay. The default sysfs mode
does not provide these roots or their physical addresses. When roots are
available, `capture-acpi-root-tables.sh` reads each distinct referenced physical
address separately and names the exact returned table bytes
`acpi/root-tables/<16-digit hexadecimal address>.bin`. It preserves the root
vectors unchanged and refuses ambiguous responses, unsupported addresses,
tables over 64 KiB, or aggregate copies over 1 MiB. It also requires the
physical MADT to match the sysfs copy. Root and table input hashes, the helper
hash, and the acpidump binary hash enter the capture provenance.

The two checked root captures used ACPICA acpidump version `20230628`.
The version was verified with `acpidump -v` on the identical SHA-256 binary
recorded in both provenance files.

The QEMU capture accepts `--acpidump <binary>` to stage that optional tool and
its libraries in the minimal guest. Merely having acpidump installed on the
host does not put it in the guest. Both capture scripts support x86_64 Linux;
the root helper interprets the little-endian address vectors on that host.
The two QEMU root-capture rows replay those files through both Lean and generated C.

`scripts/capture-firmware-handoff-qemu.sh` produces the same capture from a
Linux guest under QEMU: it builds a minimal initramfs (static busybox, bash
and its libraries, and the capture script), boots a stock kernel with SeaBIOS
or an OVMF firmware image, reads the capture back over the serial console,
and adds the `guest` provenance object.

The two QEMU rows were produced with
the Ubuntu `linux-image-6.8.0-139-generic`, `busybox-static
1:1.36.1-6ubuntu3.1`, and `ovmf 2024.02-2ubuntu0.9` packages named, with
their digests, in each row's provenance.

Adding a capture:

1. Run the capture procedure, review the files for identifying strings, and
   copy the directory to `firmware-corpus/<case id>/`.
2. Add the manifest entry with the profile, provenance, permission, and
   redaction text, the input digests, the APIC identities, and the result
   you expect physically for each stage by name (`accepted`,
   `decoder-rejected:<reason>`, `normalizer-rejected:<reason>`, or
   `admission-rejected:<reason>`; the reasons are the constructor names of the
   model's error types).
3. Run `python3 scripts/firmware-corpus.py evaluate --out <dir>` and
   `lake env lean <dir>/Evaluate.lean > <log>`; the log prints the words the
   model computes for every stage and mutation.
4. Run `python3 scripts/firmware-corpus.py pin --evaluation <log>`. It fills
   the exact words, normalized digests, and mutation results only when the
   model's result agrees with the name you declared; a disagreement is a
   diagnostic to resolve, not something the tool papers over.
5. Run `./scripts/check-firmware-corpus.sh` and
   `./scripts/check-firmware-corpus-host.sh`.

## Conversion contract

`scripts/firmware-corpus.py normalize` derives the decoder inputs; the
manifest records their SHA-256 and the gate verifies conversion is
deterministic.

The memory map becomes a Multiboot2 information structure: the 8-byte
`total_size`/reserved header, one memory-map tag (type 6, entry size 24, entry
version 0) whose entries are the captured rows in captured order with the
inclusive sysfs end converted to a length, and the end tag, padded to 8 bytes
exactly as the specification requires. Linux's type names map to the E820
type numbers Linux assigned them (`System RAM` 1, `Reserved` 2, `ACPI Tables`
3, `ACPI Non-volatile Storage` 4, `Unusable memory` 5, `Persistent Memory`
7, `Persistent Memory (legacy)` 12, `Soft Reserved` 0xefffffff); Multiboot2
numbers types 1 to 5 identically and the decoder classifies every other value
as reserved without altering it. An unknown type name rejects rather than
mapping to anything. Entries are never sorted, merged, split, or dropped. The
information structure's physical address is not a captured value; the
converter passes the fixed page-aligned `0x1000` that the decoder's fixtures
use, together with the Multiboot2 magic.

The MADT is passed through byte for byte, SDT header and checksum included,
so the complete-table path (`decodeAndAdmitCompleteMadt`) validates the
envelope, decodes the entry stream, and admits or rejects it. The BSP and
executing identities come from the manifest; the executing identity must
equal the captured processor 0 APIC ID, and the manifest declares the BSP
identity explicitly.

## Expectations and mutations

Each stage's `words` are the boundary's stable result words: word 0 is the
ABI version, word 1 the status (accepted, decoder rejection, or
normalizer/admission rejection), word 2 the accepted projection or the typed
reason code, and the remaining words the accepted projection (entry and
region triples for the memory map, the admitted processor's flags for the
MADT). The manifest pins the words up to the last nonzero one; every replay
reads three more and requires them to be zero, as the boundary defines
out-of-range words.

Every case also derives fourteen controlled mutations from its own bytes, each
pinned to a typed rejection: a truncated or mis-sized information structure,
a nonzero reserved header word, a missing end tag, a nonzero entry reserved
word, a zero-length entry, an entry whose range overflows the address space,
an unsupported entry version; a corrupted MADT checksum, a wrong signature, a
declared length longer than the table, a table shorter than its declared
length, an unknown MADT record kind (an x2APIC record), and a table cut inside
its fixed header. Corpus hash drift, duplicate ids, unknown reasons, words
that disagree with the named result, a mutation that is accepted, and a
missing capture file are validator negatives.

## Replay and gates

`scripts/check-firmware-corpus.sh` (in `check.sh`) validates the manifest,
normalizes every case twice and requires byte-identical outputs, requires at
least three cases including a decoded memory map, an admitted topology, and a
rejected multi-processor topology, compiles the generated
`build/firmware-corpus/Corpus.lean`, whose `native_decide` checks evaluate the
Lean definitions on the same bytes against the same words, and runs the
validator negatives on private copies of the corpus.

The `firmware-corpus` row of `scripts/hosted-generated-boundaries.tsv` runs
`tests/firmware-corpus-host.c` through the shared lake-ir hosted-boundary
runner in both the ordinary and the ASan/UBSan-sanitized modes. The harness
reads `build/firmware-corpus/replay.tsv` and drives every input through the
exported `leanos_boot_handoff_query` and `leanos_boot_complete_topology_query`
boundaries, the same generated C the boot path links, comparing every word.
The complete-table export exists for this replay; production reaches the
same definition through its byte-copy adapters.

## Non-claims

The corpus does not claim that Linux's view reproduces GRUB's or the
firmware's handoff at boot time, that the Hyper-V or QEMU rows stand for
physical firmware, or that a decoded row would be admitted by the platform
manifest: the DMA-quarantine inventory, VT-d construction, and serial
contract are outside these two stages. A row that decodes and then rejects
is a correct corpus outcome, and the q35 boot, malformed-handoff, topology
rejection, TCG, and KVM evidence are unchanged by it.

## Root replay representation

The converter appends the one observed RSDP to the normalized memory handoff as
Multiboot2 tag 14 (revision 0) or tag 15 (revision 2 or later), preserving every
RSDP byte and adding only the specified tag header/alignment and information
length. It never synthesizes a second old/new root. The root address comes
independently from the physical address summary, and the root vector is not
sorted or deduplicated. Each distinct referenced address has one complete
byte copy; the root model detects duplicate entries and missing translations.

The normalized content digest covers the handoff bytes, root bytes, root
address, and ordered address/table pairs using canonical JSON with hex byte
strings. A separate `bundle.tsv` points the hosted harness at these binary
files; filesystem paths do not enter the digest. The harness constructs Lean
byte arrays and calls `leanos_boot_captured_root_query`, which reuses
`AcpiRootDecoder.decode` and `decodeAndAdmitAuthoritativeAcpiTopology`.

The five-word projection retains the topology ABI/status/result. On rejection,
words 3/4 preserve a root SDT reason, an offending physical address, or the
expected/actual root address. RSDP byte errors occupy codes 100–110, wrapped
handoff errors use 200 plus the existing decoder code, and adapter bounds use
300–305. The adapter rejects copy-count mismatch, oversized copies, aggregate
size overflow, and an executing APIC identity outside UInt32 before conversion.
The root-derived mutation rows cover RSDP signatures and checksums,
missing/duplicate/conflicting roots, root checksums/lengths/addresses, missing/duplicate
translations and MADTs, malformed MADTs, duplicate CPU identities, missing
CPU records, BSP mismatch, and executing-ID
overflow. Every row pins all five model words, including rejection details,
and replays through generated C with ASan/UBSan. The BSP-mismatch mutation
explicitly disables other processors in a derived MADT and overrides the
executing identity; this override is part of the normalized content digest.
The unchanged captures retain their observed processor counts and identities.
The duplicate-CPU mutation appends an exact copy of the first local APIC
record. The missing-CPU mutation removes all local APIC records while
preserving every non-CPU record. Both repair only the derived MADT length and
checksum so the decoder reaches topology admission. These negatives test the
existing admission policy; they do not establish a BSP-only Qotom policy or
prove dormant application processors remain stopped.

Each capture also has two `handoff_variants`: reversing all entries and moving
the second entry into the first entry's range. Both preserve entry count and
retain full decoded and normalized projections in the manifest. These are
intentional derived variants; they do not alter the raw capture. All captured
reversed maps retain their original normalized regions. The overlapping maps
remain accepted and pin their changed region projections. Independent drift
tests change source entry count/order and update the raw hashes, then require
the unchanged normalized expectation to reject the alteration.

## Native Qotom GRUB handoff

The separately pinned `firmware-corpus/qotom-native-handoff.json` adds the
actual 2026-09-11 legacy GRUB information block to the shared Lean/generated-C
memory replay. The converter verifies the retained capture hashes and emits
the original 2,680 bytes unchanged, with the captured magic and physical
information address (2,728,208). It does not reconstruct a memory-only block
or replace that address with the conventional corpus address.

The accepted projection preserves all 19 memory entries and four normalized
regions in the existing 16 MiB allocation domain. All 74 result words plus an
out-of-range zero query are pinned. This is memory decode/normalization only;
it neither admits the four-core topology nor certifies memory outside that
existing allocation domain. The externally referenced ACPI tables remain a
separate native capture requirement.

Eight explicitly synthetic mutations exercise wrong magic, unaligned pointer,
truncation, nonzero header reservation, unsupported entry version, zero-length
and overflowing entries, and a duplicate memory-map tag. Both the native row
and these mutations use the same ordinary/sanitized generated-C corpus harness
and Lean query checks as the reconstructed firmware rows. Native capture bytes
are never changed to produce the accepted result.
