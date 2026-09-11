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
