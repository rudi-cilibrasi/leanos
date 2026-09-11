# Native ECAM diagnostic result

The [2026-09-11 physical capture](../hardware/lab/observations/qotom-ecam-20260911/README.md)
completed the guarded ECAM scan with 16 functions and recovered to FreeBSD.
The 15-function inventory policy still rejects the observed set; no platform
admission or CPL3 result follows. The original runner rejected the changed
handoff hash after recovery; corrected offline replay now passes, with both
the original failure and reclassification provenance retained. The firmware
gate compares exact table bytes and addresses, while handoff provenance is
validated independently by the ACPI transport decoder. Component descriptions
and their narrower validation scopes follow.

## Qotom ECAM reader candidate

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
for the resource review; physical ECAM access has not yet been validated.

`hardware/lab/qotom-ecam-firmware.h` supplies a lab-only equality gate for the
entire captured twelve-table set, including physical addresses, lengths, order
and every byte. Its generated constants come from manifest-verified files
reconstructed from serial transport and checked against the recorded metadata.
Changing any of the 34751 bytes rejects, as do altered extents, counts and order;
ordinary and pinned ASan/UBSan checks exercise those cases. The freestanding
gate has no allocation or external runtime dependency.

This gate is deliberately tied to the reviewed firmware snapshot, including
its resource declaration. It is not a general AML resource interpreter, does
not admit relocated or revised firmware, and does not prove resource ownership,
AP/firmware exclusion, mapping cache type or DMA containment. The caller must
provide immutable validated copies and establish those remaining access
conditions. The opt-in diagnostic binding below invokes this gate.

`hardware/lab/qotom-ecam-memory.h` checks the local memory-control conditions:
the observed PAT layout, exact selected CR3, PG/WP/PE, active long mode/NXE,
PAE, and absence of CD/NW, PCIDE, LA57, PGE, IF and VM. It constructs a
present supervisor read-only NX leaf with PCD/PWT set and PAT clear, selecting
PAT slot 3 (UC). It changes no register or page table. Ordinary and sanitizer
tests exercise control-bit rejection and all 4194304 supported dword leaves.

These scalar checks are necessary inputs to the future mapping transaction.
They do not establish that supplied observations are fresh, that root/ancestor
tables have the expected shape, that ECAM has no cache aliases, or that no
firmware/AP agent changes state. The transaction must bind actual observations,
check the active boot map, invalidate the aperture translation after each leaf
change, restore the exact saved leaf, and publish only after a completed dword
read. Existing ACPI copying performs byte loads through a writable aperture and
must not be reused unchanged for this operation.

`hardware/lab/qotom-ecam-window.h` implements the transaction over trusted
control-read, invalidation, dword-load and terminal-fault primitives. It checks
the armed context and controls, requires an identity-mapped supervisor RW/NX
saved leaf, installs the read-only UC leaf, invalidates, samples privately,
restores the exact original leaf including Accessed/Dirty bits, and invalidates
again before publication. A failed read publishes nothing. A changed aperture,
failed restoration or invalid post-read controls takes the terminal callback;
it cannot return a usable sample. The transaction does not switch CR3.

Hosted ordinary and sanitizer tests use the actual transaction with controlled
primitives to check ordering, private output, hardware Accessed-bit handling,
read failure cleanup, changed root, aperture interference and restoration
failure. The bindings and arming checks below connect this transaction to the
opt-in image, but it has not executed against physical ECAM. An arbitrary
supplied context is not authority.

`hardware/lab/qotom-ecam-native.S` supplies the three x86-64 SysV primitives
for that future binding: a single 32-bit load into private output, `invlpg`,
and reads of PAT, CR0/CR3/CR4, EFER and entry RFLAGS. The control sampler
preserves RBX and checks CPUID MSR/PAT support before reading MSRs. It writes
neither control registers nor MSRs and performs no port I/O. Native exceptions
remain terminal; these functions do not implement fault recovery.

`scripts/check-qotom-ecam-native.py` checks the complete object instruction
sequences, branch target, absence of unresolved dependencies and C callback
ABI. Twelve mutations cover load width/count, MMIO stores, invalidation,
feature gating, MSR identity, register writes and callee-save preservation.
The hosted test executes the actual load at the end of a read-only page with
an inaccessible following page and checks private output bounds. This tests
ordinary memory access width and output behavior; it does not execute the
privileged primitives or validate UC device access. The root checks, arming
gate and image binding below supply the next layers; successful native
execution against physical ECAM remains unverified.

`hardware/lab/qotom-ecam-root.h` checks a bounded view of the active boot
arrays: one PML4 entry, one PDPT entry, eight page-table pointers and 4096
leaves. Only hardware Accessed bits may vary in present ancestors; all unused
ancestors must be zero. Physical table extents must be aligned, disjoint and
below 16 MiB, and the aperture must not overlap them. Every present leaf is
checked for an existing mapping into the ECAM allocation. The selected aperture
must retain its supervisor RW/NX identity leaf, allowing hardware A/D bits.

The caller must bind these views to the actual compiled arrays and active CR3;
the helper never follows an untrusted page-table pointer. It does not validate
the full generated leaf permission plan, stale translations from other roots,
or concurrent firmware/AP changes. Native binding, firmware validation and
control checks remain required. Hosted tests reject aliases at every leaf
position, unexpected ancestors and huge pages, changed aperture attributes,
root mismatch, overlapping storage and invalid extents. The freestanding
object has no external runtime dependency.

`hardware/lab/qotom-ecam-arm.h` composes the firmware equality gate with
fresh control observations before and after root validation. Success selects
the checked aperture leaf from the supplied boot-array view and arms the
transaction. Every rejected rearm clears the previous arm, leaf, root and
window. Arming itself performs no invalidation, page-table write or device
load. The root view exposes mutable leaf storage explicitly rather than
casting away constness when selecting the aperture.

The composed hosted test exercises successful arming followed by the actual
window transaction, firmware rejection without primitive calls, revocation
after a previous success, both control-observation failures, an existing ECAM
alias and a missing callback. Ordinary and pinned ASan/UBSan checks pass.
The caller still owns binding array views to compiled physical addresses,
private context storage, immutable firmware copies and exclusion assumptions;
the diagnostic image binding below supplies those local inputs.

The opt-in builder now supports `--ecam-read`, requiring DSDT and memory
capture and rejecting combination with the mechanism-1 PCI trace. Its native
binding retains descriptors of the validated firmware copies, uses the actual
compiled identity addresses for the boot-array view, and selects a dedicated
aligned aperture. The diagnostic arms after firmware capture, invokes the real
PCI collector through the ECAM callback, and disarms after the scan. Firmware
count mismatch retains the complete capture before the arm gate rejects it.
The native object is included in both prelink and final diagnostic links; its
source, object, generated firmware header and helper inputs are manifest-pinned.

The integrated image passes the prelink/final page-plan equality and Multiboot2
checks. `scripts/test-qotom-ecam-image.py --elf <lab ELF> --output <directory>`
boots it with the accepted CPU fixture and foreign q35 firmware, requires the
exact ECAM arm failure with no PCI scan, and verifies captured ACPI bytes against
independent QMP physical-memory reads. This negative boot passed. It does not
execute the privileged primitives on the accepted firmware path or establish
physical ECAM access. Capture decoder/runner integration and protected
physical testing remain required; the isolated privileged tests below cover
the native primitives separately. Completion reset
still uses mechanism-1 host identification outside the ECAM read callback.

`scripts/test-qotom-ecam-native-qemu.py` executes the actual native assembly
in an isolated single-CPU fixture. Its control/MSR outputs match independent
reads. It replaces a huge RAM mapping with equivalent 4 KiB leaves, remaps a
reserved aperture between two RAM pages, and verifies that invalidation makes
the second page's value visible. The aperture cannot overlap the linked image.
A second boot disables CPUID PAT support and requires rejection with every
output field unchanged. Both pinned QEMU cases pass and are registered in the
aggregate check script. These tests validate privileged primitive execution
and RAM translation changes; they do not bypass the diagnostic firmware gate,
exercise UC ECAM device transactions or establish physical resource ownership.

`scripts/check-qotom-ecam-capture.py` checks the ECAM transport after ACPI
extraction and before the existing bootstrap/memory decoders and diagnostic
replay. An armed record requires matching ordered firmware metadata and every
captured table byte against the manifest-pinned native snapshot. Missing,
repeated, misplaced or modified records reject. The decoder distinguishes a
rejected arm from a terminal transaction fault after arming. Its metadata does
not grant platform admission; CPU/MSR observations and PCI payload validation
remain the responsibility of the subsequent existing decoders/replay.

Five synthetic boundary tests pass, including one-byte changes in each firmware
table. The actual foreign-firmware QEMU boot also passes this decoder and the
independent ACPI memory comparison. Protected-runner integration remains pending;
synthetic successful-arm records are not physical ECAM evidence.

The protected runner now accepts `--ecam-read` with DSDT/memory capture and
without mechanism-1 tracing. It decodes the arm before the bootstrap/memory
records and retains `ecam.json`. Decoder and firmware-manifest hashes are
included in the input-stability check. Exact ECAM arm/transaction failures may
retain completed CPU/MSR observations without a PCI scan; their CPU/MSR replay
keeps the original terminal reason and explicitly reports its limited scope.
The default decoders still reject those extended terminal paths unless the
ECAM option is enabled. No PCI scan is synthesized for an early failure.

Three composed regression tests cover synthetic completed scans, both early
failure paths, CPU/MSR disagreement, malformed records and option conflicts.
The retained DSDT/bootstrap/memory and recovery tests continue to pass. An
actual QEMU rejection capture also passes classification with a synthetic
recovery envelope. These are classifier tests; the new runner path has not yet
completed a physical protected cycle.
