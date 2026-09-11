# Qotom ECAM reader candidate

`boot/qotom-ecam-read.h` calculates aligned conventional configuration dword
addresses only for the captured allocation: segment 0, base 0xe0000000, buses
0–255. It rejects other allocation values, bus/device/function overflow,
extended-space offsets, misalignment and null outputs without changing output.
The largest allowed address is 0xeffff0fc. Arithmetic uses bounded 64-bit fields.

`qotom_ecam_read` adapts a caller-provided dword access callback to the existing
segment enumerator. It invokes that callback only for a checked address, keeps
the sample private until success, and preserves the existing all-ones vendor
absence semantics. This component exposes no mapping or configuration-write
operation. A rejected callback cannot publish a partial inventory through the
existing enumerator.

The MCFG base is relative to bus zero. Discovery through MCFG is separate from
resource reservation, as described by the [Linux PCI host-bridge documentation](https://www.kernel.org/doc/html/latest/PCI/acpi-info.html).
The positive hosted allocation is decoded from the manifest-pinned native
MCFG at physical 0xb97a6bb0, SHA256
`ea68ade449e37cbd39a4fb891b464229e7739dda4604880dc0606e2129d55538`.
`scripts/qotom-ecam-fixture.py` checks metadata, checksum, length, reserved fields
and both manifest/table hashes. That script is a fixture extractor, not the
production MCFG decoder or a hardware access authorization mechanism.

Before a physical access callback can be used, the caller must establish:

- A unique authoritative validated MCFG and a resource ownership/overlap policy.
- A dedicated supervisor NX mapping with validated effective uncached type,
  compatible aliases and checked translation invalidation/restoration.
- The actual same-boot PAT/control observation; reset defaults are insufficient.
- One aligned dword MMIO load and terminal fault handling, with final-object
  checks for width and absence of configuration writes or CF8/CFC access.

Intel's [SDM Volume 3A](https://cdrdv2-public.intel.com/819714/253668-sdm-vol-3a.pdf),
sections 12.5.2.2 and 12.12.3, defines effective PAT/MTRR memory types and the
leaf bits selecting the PAT slot. The existing writable byte-oriented ACPI
copy aperture has no such ECAM contract and is not used by this candidate.

Ordinary and pinned ASan/UBSan checks exhaust all 4,194,304 legal address tuples,
exercise malformed inputs and failed-callback output preservation, and run the
actual enumerator through downstream success and a mid-header read failure.
A freestanding wrapper has no unresolved runtime dependencies. Deliberate bus,
device/function shift, alignment and failed-sample publication mutations are
rejected by the tests.

This is an incomplete ECAM implementation. No physical callback, kernel call,
MMIO read, resource-admission witness, device quiescence or DMA containment is
provided. Issue #330 remains open. The candidate is kept separate from q35 and
from the mechanism-1 diagnostic fix.

The lab builder and protected capture runner accept `--ecam-memory-capture`
with `--bootstrap-capture --pci-diagnostic`. The sampler records IA32_PAT only
when CPUID reports both MSR and PAT support, plus CR0, CR3 and CR4. It performs
no register writes or MMIO accesses. The record follows the bootstrap sample
after the CPU/control gate. The decoder binds its CPUID word to the CPU and
bootstrap records, checks widths and ordering, and retains the eight observed
PAT bytes without interpreting them as mapping admission. The runner hashes
the decoder and saves `ecam-memory.json` alongside the capture artifacts.

The hosted tests insert a synthetic memory record into retained serial bytes
and replay CPU, PCI, ACPI, bootstrap and protected recovery together. This tests
transport integration; it is not a physical PAT observation or evidence that
the ECAM mapping preconditions above have been satisfied.

The [retained physical capture](../hardware/lab/observations/qotom-ecam-memory-20260911/README.md)
observes PAT 0x0007040600070406, CR0 0x8001001f, CR3 0x150000 and CR4 0x68
on the Qotom. Its protected recovery returned to FreeBSD with the request
consumed. A manifest-checked regression replays these actual serial events.
The observation supplies the previously missing same-boot register values;
resource provenance, alias/mapping admission and the physical access callback
remain unfinished. The capture's PCI rejection does not establish inventory.

`--dsdt-capture` additionally follows the unique copied FADT to its DSDT.
It requires `--acpi-capture`, preserves the complete ordered root table list,
and appends the DSDT under the same 64 KiB handoff/table transport budget.
The explicit `dsdt=1` header prevents interpreting the extended record set
as the older capture format. Both decoders reject unsupported FADT lengths
or revisions, null/out-of-range pointers, duplicate FADTs, wrong DSDT identity,
table overlap and incomplete transport. Publication occurs after copying and
validating the complete requested set. No AML method is executed.

Pointer selection follows the DSDT and X_DSDT fields in the
[ACPI FADT format](https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html#fixed-acpi-description-table-fadt):
revision 1 uses the legacy field, while supported extended revisions prefer a
nonzero X_DSDT. An extended address beyond the lab's 32-bit physical backend
rejects rather than silently selecting another table. Selecting and copying
the DSDT supplies bytes for a future resource-policy review; it does not itself
prove that a particular AML resource declaration authorizes ECAM access.

The [native DSDT capture](../hardware/lab/observations/qotom-dsdt-20260911/README.md)
retains the FADT-linked 30800-byte DSDT at 0xb979f180 and its offline disassembly.
Its PDRC resource buffer declares the same 256 MiB ECAM region as MCFG. The
regression checks manifest hashes, native C/Python pointer agreement, complete
table transport and protected recovery. This supplies same-boot table bytes
for the resource review; the physical ECAM callback remains unimplemented.
