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
`unavailable` for every current row: Linux does not expose the RSDP, RSDT, or
XSDT in sysfs, so the root-selection stage of `BootTopology` is not replayed
yet, and the manifest refuses any other value until that stage lands.

Three firmware families are in the corpus today:

| Case | Firmware | Memory map | Topology |
| --- | --- | --- | --- |
| `hyperv-wsl2-24cpu` | Microsoft Hyper-V UEFI (WSL2 utility VM) | 5 entries, decoded | 24 enabled processors, rejected `multipleEnabledProcessors` |
| `qemu-seabios-q35-1cpu` | SeaBIOS on QEMU q35 | 9 entries, decoded | 1 processor, admitted |
| `qemu-ovmf-q35-4cpu` | OVMF (EDK II) on QEMU q35, booted through the EFI stub | 19 interleaved RAM/NVS/reserved entries, decoded | 4 enabled processors, rejected `multipleEnabledProcessors` |

The two QEMU rows are real firmware captured through the same Linux
procedure as a physical machine, not repository-constructed fixtures; the
Hyper-V row is a physical host's virtualization firmware. Physical-machine
captures from the bare-metal work (#290) join the corpus through the same
procedure.

## Capture procedure

`scripts/capture-firmware-handoff.sh <directory>` runs on the source machine
from a Linux live environment as root or with passwordless sudo. It copies
the sysfs memory map and the raw MADT, records processor 0's APIC identity,
and writes `provenance.json`. It reads only vendor, model, and firmware
version strings from DMI; it never reads serial numbers, UUIDs, or network
addresses, and it never reorders, merges, or repairs what it copies. When
`acpidump` is available it also records the RSDP, RSDT, and XSDT for a future
root-stage replay.

`scripts/capture-firmware-handoff-qemu.sh` produces the same capture from a
Linux guest under QEMU: it builds a minimal initramfs (static busybox, bash
and its libraries, and the capture script), boots a stock kernel with SeaBIOS
or an OVMF firmware image, reads the capture back over the serial console,
and adds the `guest` provenance object. The two QEMU rows were produced with
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
