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
not a second runtime dispatcher.

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

`DeviceContract` is the explicit boundary assumption: if a modeled
device-originated step changes memory, the named function is present and has
bus mastering enabled. Assignment is kernel policy rather than a hardware
precondition for DMA. From an accepted snapshot, which separately establishes
that every present function is unassigned with bus mastering disabled, and a
named present function, `unowned_device_preserves_complete_projection` proves equality of the
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
inventory and boot tests are integration evidence only.

`scripts/check-q35-pci-construction.py` supplies a narrower integration
checkpoint against the pinned QEMU 8.2.2 binary. It pauses the same q35/TCG,
CPU, memory, vCPU, network, and debug-exit construction used by the image
runner, exhaustively reads all 256 functions on manifest bus 0 through qtest's
PCI configuration mechanism #1 interface, and rejects identity/class/header
drift, duplicate BDF observations, missing or extra functions, or a set
bus-master bit. Focused negative regressions exercise each rejection class so
dictionary construction cannot silently collapse a duplicate topology record.
Its versioned TSV is a construction-time QEMU observation before firmware runs.

The guest now supplies the distinct post-firmware checkpoint. Immediately
after its first serial boot record and before any CPL3 return, `boot/kernel.c`
exhaustively reads all 256 functions on bus 0. It rejects any present BDF not
in the same manifest, identity/class/header drift, or a missing required
function. It writes the PCI Command register of every present function with
bus mastering clear, then performs a separate read-back and rejects a set
bus-master bit or any Command bit outside the model's 11-bit range. The exact
`LEANOS/15 DMA` record is mandatory in `scripts/run-image.sh`; missing and
forged records are negative runner fixtures. Thus the pinned emulator logs
show five present functions, one absent optional network function, five writes,
and five successful read-backs before CPL3. Although the construction-time
probe sees every Command bus-master bit clear, pinned SeaBIOS enables the
recognized ICH9 SATA function at `00:1f.2` while booting the CD-ROM. Every
mandatory accepted-boot record therefore requires one initially enabled bus
master and manifest mask 16, followed by final disabled state. Removing or
misaddressing `pci_config_command` leaves that SATA bit set and fails the guest
read-back.

This adapter intentionally treats an all-ones vendor read as architectural
absence. A missing required function is fatal; for the optional network slot,
distinguishing genuine absence from an underlying read transport failure is a
trusted configuration-mechanism/QEMU assumption. The exhaustive bus-0 bound,
no-hotplug runner, firmware behavior, write effect, read-back freshness, and
device obedience remain tested assumptions. The C manifest and the final
binary are not proved to refine `q35Manifest`, so the boot checkpoint does not
upgrade the Lean theorem into a hardware claim.

Issue #104's authoritative composite invariant remains on its separate,
unmerged dependency lane. Once that state lands, its exact `RuntimeWellFormed`
and typed gate should embed `AcceptedSnapshot` and the unchanged control
snapshot; this model intentionally does not fork a competing composite state.
Issue #129 remains a separate direct-user-I/O policy lane and explicitly lists
PCI configuration as a non-goal. When its final-ELF port inventory lands, it
must classify this checkpoint's boot-only `0xcf8`/`0xcfc` mechanism accesses as
one reviewed kernel purpose rather than treating them as ambient authority.
