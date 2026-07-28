# PCI DMA quarantine model

`LeanOS.DMAQuarantine` is the Phase 2 deny-all PCI DMA policy. It validates one
finite snapshot against the repository's selected QEMU 8.2.2 q35 topology
version (`0x0008_0002_0002`). The manifest names the host bridge, VGA function,
ICH9 ISA bridge, SATA controller, SMBus controller, and the optional network
slot suppressed by `-nic none`. Bus/device/function identity is explicit, so
bridges, multifunction functions, duplicates, and identity drift cannot be
discarded by a first-match scan.

Acceptance requires the exact snapshot and topology versions, no duplicate or
unknown BDF, one record for every manifest entry, readable identity for every
present function, the canonical 11-bit defined Command-register range, no assignment, and
the bus-master bit clear. Required functions cannot be absent. Optional absent
functions retain an explicit canonical record. Missing, unreadable, stale,
unexpected, assigned, or bus-master-enabled records produce typed rejection.

## Typed serialization boundary

`encodeSnapshot` emits exactly 210 64-bit words: snapshot and topology version,
then sixteen 13-word slots. Each occupied slot contains an occupancy tag, BDF,
vendor/device/class identity, read-status tag, full Command word, assignment
tag, assignment-owner word, bridge bit, and multifunction bit. Keeping the tag
separate prevents the maximum owner identifier from wrapping into the
unassigned encoding. Empty tail slots are all zero. More
than sixteen records reject instead of truncating. `accepted_encoding_fixed_width`
proves the length of every successful snapshot encoding.
`encodeValidationResult` supplies the paired canonical one-word result: zero
means accepted and stable tags 1 through 8 identify each typed rejection.
`encodeValidationResult_length` proves that result width. These are the
quarantine-owned inputs for issue #105's later composite-state codec; they are
not a validator, decoder, or second runtime dispatcher. In particular,
`encodeSnapshot` serializes any bounded typed `Snapshot`, including stale or
otherwise invalid values. `validate` separately decides semantic acceptance.
`stale_snapshot_serializes_but_rejects` makes that distinction executable.
Issue #105 remains responsible for canonical byte-level decoding, rejection of
noncanonical wire representations, and the global composite-state ABI.

`LeanOS.DMAQuarantineCorpus` makes the issue-local control boundary executable
without importing or approximating #104's composite state. Each of its six
version-one records contains the complete 421-word accepted/latest-snapshot
and fatal-latch pre-state, the complete 211-word public operation, the complete
post-state, and a one-word typed result. Two traces cover ordinary continuity,
exact re-observation, a valid but changed Command bit, an invalid bus-master
bit, and post-fatal absorption. Lean proves every field width, both result
sequences, and adjacent-state continuity; the repository gate emits the corpus
twice, checks deterministic byte equality, and independently checks its schema
and chaining. This is a DMA control-projection corpus, not #105's future global
runtime ABI or a serialization of the model's unbounded memory projection.

## Proved claim

`AcceptedSnapshot` carries canonical accounting and a nonempty quarantine
invariant. `accepted_accounts_every_manifest_entry` exposes exact accounting,
`accepted_present_known_exactly_once` shows that each accepted present function
has a manifest BDF occurring exactly once, and
`accepted_unassigned_busMaster_disabled` proves the deny-all control fact for
every present function.

`DeviceContract` is the explicit integrity-only boundary assumption: if a modeled
device-originated step changes memory, the named function is present and has
bus mastering enabled. Assignment is kernel policy rather than a hardware
precondition for DMA. From an accepted snapshot, which separately establishes
that every present function is unassigned with bus mastering disabled, and a
named present function, `unowned_device_preserves_complete_projection` proves equality of the
entire physical-memory, allocator-ownership, page-table-frame,
kernel-owned-frame, kernel-state, and per-subject-visible-byte projections.
`q35Snapshot` is an executable accepted nonempty witness, so this result cannot
be satisfied by assuming an empty inventory.

This is memory-mutation integrity, not device-read confidentiality. The
contract has no device-read premise or conclusion and does not prevent a device
from observing physical bytes, retaining previously observed data, or leaking
data through timing, MMIO, interrupts, or another channel.
`device_contract_allows_distinct_reads` formally witnesses that the same
contracted memory stutter is compatible with distinct device-read observations.
The required-to-fail `DMADeviceReadConfidentiality` fixture prevents the
integrity theorem from being advertised as read confidentiality.

The runtime control model makes re-observation explicit. Ordinary public
operations contain no BDF, assignment, or Command word. Every continued step
preserves quarantine. A bit flip, otherwise valid changed snapshot, or invalid
snapshot becomes typed fatal state, and the halted state absorbs every suffix;
it is not relabeled as a contained user fault or an ordinary rejection.
`valid_changed_control_exact_fatal` fixes the complete outcome of a valid but
different observation, while `invalid_control_exact_fatal` fixes the complete
outcome of any validation rejection. Both retain the observed snapshot for
diagnosis and latch distinct fatal reasons. `halted_suffix_absorbing` extends
the one-step result to every finite public-operation suffix: the state remains
identical and each result repeats the original typed `alreadyHalted` reason.
The `DMAInvalidControlContinuation` negative fixture is required to fail for a
concrete bus-master-enabled observation.

`UnownedDeviceStep` makes each modeled device attempt name a present function
and carry the explicit `DeviceContract`; the accepted snapshot separately
supplies unassigned ownership and a cleared bus-master bit. `QuarantineStep`
then combines those attempts with only the continuing cases of `runtimeGate`.
The finite `QuarantineTrace` theorem proves that every such mixed trace is a
stutter on the complete issue-local runtime projection: the live control
invariant, quarantine predicate, physical memory, allocator ownership,
page-table frames, kernel-owned frames, kernel state, and all subject-visible
bytes remain unchanged. The stable `SC-DMA-QUARANTINE-TRACE` wrapper advertises
that finite-trace result separately from the original single-device-step claim.
This trace is intentionally not the global composite runtime owned by issue #104
and does not pre-empt that issue's state design.

## Trusted boundary and dependency

The proofs start after a complete hardware snapshot and assume direct physical
DMA is disabled by the observed bus-master control. There is no modeled IOMMU,
DMA remapping table, interrupt remapping, translated device address space, or
device-assignment refinement. PCI configuration reads,
enumeration completeness, firmware initialization, architectural meaning and
read-back behavior of the Command register, QEMU/device obedience, generated C,
assembly, compiler/linker behavior, and the final binary are not proved. QEMU
inventory and boot tests are integration evidence only.

`scripts/q35-platform.sh` owns the emulator construction used by every
mandatory runner. It selects q35/TCG with `-nodefaults`, pins the VGA function
at `00:01.0`, explicitly attaches the boot ISO to the machine-integrated AHCI
controller through `ide.0`, disables networking, and adds only the ISA
debug-exit device. q35 still creates the manifest's host bridge, ISA bridge,
AHCI, and SMBus functions as machine-integrated devices. The shared builder
does not make those QEMU semantics proved; it makes the repository's requested
construction explicit and keeps runner topology from drifting independently.
Its positive and controlled-negative gate rejects omitted `-nodefaults`, an
extra PCI device, an unpinned VGA BDF, or a mandatory runner that bypasses the
builder.

`scripts/check-q35-edu-dma.py` supplies the distinct DMA-sensitive oracle. It
uses QEMU's pinned `edu` function at `00:02.0`, assigns and reads back its BAR,
loads its internal DMA buffer from guest physical memory, and then requests the
same device-to-guest transfer in two isolated runs. The protected physical
record contains the canary, its fixture-owned physical-frame identity, and an
allocator-owner identity. With PCI Command bus mastering clear, that complete
record remains byte-for-byte unchanged. With bus mastering deliberately
enabled, the device replaces the complete record with the known payload. The
versioned TSV records the canary and both identity fields before and after each
case, and CI retains it, so observing only a clear Command bit or a non-crashing
guest cannot satisfy this fixture. These identity words are a finite QEMU
mutation oracle, not evidence that the QTest fixture reconstructs the kernel's
authoritative allocator state or refines the Lean projection. This controlled
extra function is never admitted to the production topology or its manifest.

`scripts/run-dma-unknown-device.sh` supplies the first guest-level controlled
negative after that canary oracle. It reuses the normal production image and
the shared q35 construction, then adds exactly one pinned `edu` function at
`00:02.0`. The post-firmware guest enumeration must emit the typed
`dma-inventory` fatal result and the debug-exit value for that failure before
any DMA-quarantine PASS or CPL3 entry. The runner rejects a missing, duplicate,
or different fatal result, any apparent CPL3 entry or success record, reset,
unrelated guest failure, and timeout. CI executes the real QEMU negative after
building the image and retains its serial transcript. This finite adversarial
boot is tested behavior, not proof of enumeration completeness or device
semantics.

`scripts/check-q35-pci-construction.py` supplies a narrower integration
checkpoint against the pinned QEMU 8.2.2 binary. It pauses the same explicit
q35/TCG, CPU, memory, vCPU, network, VGA, and debug-exit construction used by
the image runners before their boot media is attached, then exhaustively reads
all 256 functions on manifest bus 0 through qtest's
PCI configuration mechanism #1 interface, and rejects identity/class/header
drift, duplicate BDF observations, missing or extra functions, or a set
bus-master bit. Focused negative regressions exercise each rejection class so
dictionary construction cannot silently collapse a duplicate topology record.
Its versioned TSV is a construction-time QEMU observation before firmware runs.

The guest now supplies the distinct post-firmware checkpoint. Immediately
after its first serial boot record and before any CPL3 return, `boot/kernel.c`
exhaustively reads all 256 functions on bus 0. It rejects any present BDF not
in the same manifest, identity/class/header drift, or a missing required
function. It writes the PCI Command register of every present function to the
canonical deny-all value zero, then performs a separate read-back and rejects
any remaining Command bit. This makes the retained live observation equal
issue #135's exact `q35Snapshot`, rather than merely satisfying its broader
quarantine predicate. The exact
`LEANOS/15 DMA` record is mandatory in `scripts/run-image.sh`; missing and
forged records are negative runner fixtures. Thus the pinned emulator logs
show five present functions, one absent optional network function, five writes,
and five successful exact Command-word read-backs before CPL3. The guest
compares each read-back with the complete zero word it wrote, not merely with a
cleared bus-master mask. Independent runner negatives mutate the topology
version, final bus-master state, read-back count, and exact-read-back marker;
each must be rejected as a serial-protocol failure. Although the construction-time
probe sees every Command bus-master bit clear, pinned SeaBIOS enables the
recognized ICH9 SATA function at `00:1f.2` while booting the CD-ROM. Every
mandatory accepted-boot record therefore requires one initially enabled bus
master and manifest mask 16, followed by final disabled state. Removing or
misaddressing `pci_config_command` leaves that SATA bit set and fails the guest
read-back.

The accepted post-quarantine Command words remain kernel-owned state. Every
later outbound CPL3 gate exhaustively re-enumerates bus 0, rechecks each
identity/class/header tuple and required function, and requires the complete
live Command word to equal that same canonical boot observation with bus
mastering still clear. The guest packs every canonical identity, status,
Command, assignment, bridge, and multifunction field from that observation
and passes the result to the allocation-free generated
`leanos_validate_q35_dma_snapshot` boundary. The generated boundary accepts
only the exact production `q35Snapshot` projection and returns the stable
typed rejection tags for version, topology, inventory, control, or bus-master
drift. Its result is retained in the canonical live PCI snapshot; there is no
unrelated composite transition standing in for DMA acceptance. The
`dma-bus-master-reenable` controlled image sets the SATA
bus-master bit after boot acceptance and immediately before the production
return validator; the same validator must emit typed `dma-live-command`
failure before `iretq` or any CPL3 record.

This adapter intentionally treats an all-ones vendor read as architectural
absence. A missing required function is fatal; for the optional network slot,
distinguishing genuine absence from an underlying read transport failure is a
trusted configuration-mechanism/QEMU assumption. The exhaustive bus-0 bound,
no-hotplug runner, firmware behavior, write effect, read-back freshness, and
device obedience remain tested assumptions. The C manifest and the final
binary are not proved to refine `q35Manifest`, so the boot checkpoint does not
upgrade the Lean theorem into a hardware claim.

Every accepted image runner also validates six ordered `DMA-FUNCTION` records
independently of the aggregate PASS line and writes
`dma-quarantine-snapshot-<scenario>.tsv`. The fixed-schema artifact binds the
QEMU version, q35/TCG construction, snapshot/topology/manifest versions, full
source revision, every admitted or explicitly absent BDF and identity, Command
word before and after quarantine, assignment/bridge/multifunction fields, and
the typed `accepted:0` policy result. Missing, duplicate, reordered, drifted,
noncanonical, or inexact function records reject the runner even when the
aggregate line remains intact. Required host fixtures independently corrupt a
BDF, identity, class, presence status, absent-function control state, initial
bus-master state, modeled Command bits, read-back, bridge flag, and
multifunction flag; every corruption must stop snapshot retention with the
typed `dma-snapshot` runner failure. The shared evidence report hashes each
boot scenario's snapshot, CI and tagged-release diagnostics retain all of them,
and the normal blocking-IPC snapshot is included in the checksummed release
bundle.

Issue #104's authoritative `FailStop.CompositeState` now embeds the
proof-carrying accepted snapshot and latest control observation directly;
`RuntimeWellFormed` includes their exact `DMAQuarantined` agreement, and
`AuthoritativeRuntimeWellFormed` exposes that same conjunct.
Every authoritative ordinary, blocking, and deferred-drain constructor retains
the accepted and observed PCI authority fields literally. Consequently an
arbitrary finite successor trace preserves the nonempty deny-all quarantine
without #104's stronger, still-partial dormant-cancellation compatibility
certificate. The already-derived exact-projection compatibility laws for
return-authority selection, user-return completion, and restart are also
consumed directly: each constructor preserves the complete authoritative
invariant and therefore its DMA conjunct, without importing compatibility
premises for unfinished constructors. Under an explicit caller-supplied
`DeviceContract` assumption over the authoritative live observation, a named
present unowned-device attempt preserves the complete physical-memory
projection. Neither `DMAQuarantined` nor `AuthoritativeRuntimeWellFormed`
proves or discharges that trusted hardware contract; they supply the accepted
observation and its deny-all control facts. This remains an IOMMU-independent
model result, not a proof of hardware obedience to the PCI Command register.
Trusted
`observeDMAControl` revalidates a live hardware snapshot: an exact observation
continues atomically, while an invalid or valid-but-changed observation
publishes the diagnostic snapshot, latches a typed DMA fatal record, and is
absorbed by every later authoritative successor operation. This integration
does not fork `DMAQuarantine.RuntimeState` or its parallel memory projection
into the composite runtime.

Issue #105 remains the owner of canonical decoding and the global fixed-width
composite encoding. The finite q35 scalar transport is only the allocation-free
generated boot boundary for the already canonical live PCI projection; it is
not a composite-state codec or a generated-C refinement theorem.
Issue #129's final-ELF inventory now classifies the fixed `0xcf8`/`0xcfc`
mechanism accesses as `DMAQuarantine.pci-config`. The exact `out16`,
`out32`, and `in32` wrapper sites are reviewed exceptions, while the source
contract fixes their arguments to the PCI configuration address/data constants.
The final-ELF call graph pins the wrappers to the two PCI helpers, the helpers
to the boot checkpoint and read-only outbound validator, and the boot
checkpoint before the first CPL3 return. Only the named controlled-negative
image may call the Command writer from its injection helper. These sites are
not members of the ordinary direct-port authority manifest.
