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

## Canonical corpus encoding

`encodeSnapshot` emits exactly 194 64-bit words: snapshot and topology version,
then sixteen 12-word slots. Each occupied slot contains an occupancy tag, BDF,
vendor/device/class identity, read-status tag, full Command word, assignment
tag, bridge bit, and multifunction bit. Empty tail slots are all zero. More
than sixteen records reject instead of truncating. `accepted_encoding_fixed_width`
proves the length of every successful snapshot encoding.
`encodeValidationResult` supplies the paired canonical one-word result: zero
means accepted and stable tags 1 through 8 identify each typed rejection.
`encodeValidationResult_length` proves that result width. These are the
quarantine-owned inputs for issue #105's later composite-state codec; they are
not a second runtime dispatcher.

## Proved claim

`AcceptedSnapshot` carries canonical accounting and a nonempty quarantine
invariant. `accepted_accounts_every_manifest_entry` exposes exact accounting,
`accepted_present_known_exactly_once` shows that each accepted present function
has a manifest BDF occurring exactly once, and
`accepted_unassigned_busMaster_disabled` proves the deny-all control fact for
every present function.

`DeviceContract` is the explicit boundary assumption: if a modeled
device-originated step changes memory, the named function is present, assigned,
and has bus mastering enabled. From an accepted snapshot and a named present
function, `unowned_device_preserves_complete_projection` proves equality of the
entire physical-memory, allocator-ownership, page-table-frame,
kernel-owned-frame, kernel-state, and per-subject-visible-byte projections.
`q35Snapshot` is an executable accepted nonempty witness, so this result cannot
be satisfied by assuming an empty inventory.

The runtime control model makes re-observation explicit. Ordinary public
operations contain no BDF, assignment, or Command word. Every continued step
preserves quarantine. A bit flip, otherwise valid changed snapshot, or invalid
snapshot becomes typed fatal state, and the halted state absorbs every suffix;
it is not relabeled as a contained user fault or an ordinary rejection.

## Trusted boundary and dependency

The proofs start after a complete hardware snapshot. PCI configuration reads,
enumeration completeness, firmware initialization, architectural meaning and
read-back behavior of the Command register, QEMU/device obedience, generated C,
assembly, compiler/linker behavior, and the final binary are not proved. QEMU
inventory or future boot tests are integration evidence only.

Issue #104's authoritative composite invariant remains on its separate,
unmerged dependency lane. Once that state lands, its exact `RuntimeWellFormed`
and typed gate should embed `AcceptedSnapshot` and the unchanged control
snapshot; this model intentionally does not fork a competing composite state.
Issue #129's future boot-only PCI configuration access must likewise use its
reviewed kernel port-purpose vocabulary.
