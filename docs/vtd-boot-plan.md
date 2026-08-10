# Deterministic VT-d boot plan

`LeanOS.VTdBootPlan` is a finite, bounded model of the DMA-remapping tables that
a future boot slice will install for the pinned q35 `intel-iommu` unit before
translation is enabled. It is a Lean model plus a host-only generator. It does
not yet program Intel VT-d, map the unit's MMIO window, write remapping tables,
invalidate an IOTLB, enable an assigned device, or establish correspondence to
generated C, boot assembly, QEMU, firmware, PCIe, or physical hardware.

This is the second issue in the IOMMU/device-assignment set. It consumes the
static device-domain model `LeanOS.IOMMU` (see
[iommu-confinement.md](iommu-confinement.md)) and produces a checked, still
deny-all remapping base. Enabling an assigned device and dynamic revocation
remain later issues.

## Pinned unit configuration

The reviewed QEMU 8.2.2 `intel-iommu` configuration is
`intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,
dma-translation=on,snoop-control=off`. The shared q35 builder
(`scripts/q35-platform.sh`) now constructs exactly this unit as the first
device of every mandatory emulator run — QEMU requires the remapping unit to
exist before any translated PCI function — and its validator rejects an
omitted, duplicated, drifted, or reordered unit. This construction revision is
topology version `0x0001_0008_0002_0002`. The unit is inert for the existing
guest: it is not a PCI function, so the bus 0 inventory, DMA quarantine, and
serial evidence are unchanged apart from the topology version, and translation
stays disabled at reset (global status reads zero) until a later slice enables
it in the documented order. Its architectural register values are
pinned as constants: the version register (`0x10`), the capability register,
and the extended-capability register.

## Mapped window and quiescent-unit validation

The generated CPU page plan now carries the unit's MMIO window as the one
reviewed non-identity leaf: a dedicated linker-owned virtual page
(`__vtd_mmio_window_start`) maps physical `0xFED90000` as present, writable,
supervisor-only, and no-execute in both address spaces, and the sacrificed
backing RAM frame stays inside the image reservation. The remapping-table
frames (`vtd_root_table`, `vtd_context_table`) are identity-mapped
`remappingTables` leaves proved reserved and disjoint from the CPU page-table
block. The live walker validates the window leaf exactly like every other
leaf, and two live-mutation fixtures (`mmio-wrong-frame`, `mmio-flip-user`)
prove an aliased or user-visible window is rejected.

Before CPL3 the guest reads the unit through two reviewed `noinline`/`noipa`
volatile accessors and requires the exact pinned version, capability, and
extended-capability words, zero global status (translation disabled), zero
fault status, and a zero root-table pointer, then checks the generated tables
are the deny-all shape (one present root entry naming the context-table frame,
no present context entries) and that the generated frames equal the linked
symbols. The evidence is the two `LEANOS/21` serial lines, validated
structurally by every boot runner. The page is mapped write-back under the
pinned TCG emulator, which models no cache; the supported leaf encoding has no
cache-disable bit, and qualifying real hardware (where the window must be
uncacheable) remains out of scope. Passthrough support (ECAP bit 6),
caching mode (CAP bit 7), and device-IOTLB support are visibly absent from the
pinned words, so an option drift that turned any of them on is observable in
decoded hardware state rather than only on a command line.

## Canonical entry codec

A root entry is one present bit plus a 4 KiB-aligned context-table pointer; a
context entry is one present bit, a translation type, a second-level pointer, a
domain identifier, and an address-width encoding. Each occupies two 64-bit
words. The supported subset keeps every architecturally reserved bit zero.

`decodeRootEntry` and `decodeContextEntry` are total decoders that name a typed
reason for each rejected word pair. The round-trip lemmas `decode_encode_root`
and `decode_encode_context` prove encoding then decoding is exact;
`encode_decode_root` and `encode_decode_context` prove every accepted word pair
is the canonical encoding of the decoded entry, so acceptance is exactly the
image of the encoder rather than a finite set of examples. Injectivity
(`root_entry_encoding_injective`, `context_entry_encoding_injective`) shows one
accepted word pair cannot encode two entries.

## Plan compilation and the accepted domain projection

`VTdBootPlan.compile` is the only constructor of `Plan`; every field, including
the deny-all and reservation proofs, is private, so an accepted plan cannot be
reconstructed with substituted tables. The v1 subset installs the deny-all boot
tables: one present root entry for bus 0 selecting the reserved context table,
and 256 absent context entries. This is exactly the projection of an accepted
static device-domain `IOMMU.State` that carries no live assignment or mapping:
`accepted_state_deny_all` requires the model state itself to be deny-all, and
`accepted_agrees_with_domain_projection` shows no source and generation resolves
to a live assignment in that state. `accepted_maps_no_frame` shows no physical
frame is reachable through an accepted plan, and `accepted_requesters_bound_once`
fixes the 256-entry context table indexed by requester. A device-domain state
that carries a live assignment is rejected until the assigned-device issue
reviews it.

The remapping-table frames are identity-mapped and covered by the same
validated boot-reservation overlay that excludes CPU page tables from
allocation (`reservedFrame`), are distinct from each other, and are disjoint
from the CPU page-table frames. `X86PageTable.PolicyRegion` gains two reviewed
supervisor classes, `mmioWindow` and `remappingTables`;
`BootPageTablePlan.mmioFramesOutsideRam` proves the one non-identity class (the
device window) never aliases boot RAM and every RAM class stays inside the
identity window, and `remappingFramesReserved` proves the remapping-table frames
are identity-mapped and reserved.

## Fail-closed activation order

The documented activation order is: validate unit capabilities and status,
scrub the table frames, construct the tables, publish the root pointer,
invalidate the context cache, invalidate the IOTLB, enable translation, and
verify live status with an empty fault state. `canonicalJournal` fixes that
order as little-endian 4-bit step tags in one 32-bit constant
(`canonicalJournalWord`). The generated scalar boundary
`leanos_validate_vtd_activation` returns zero only when the plan version,
platform topology, pinned registers, enabled global status, empty fault status,
aligned root-table pointer, and canonical journal all agree; each nonzero tag
names the first failed check, so a reordered, omitted, or repeated activation
step, a nonempty fault, disabled translation, or an unexpected register value
rejects boot before an assigned device could be enabled.

## Generator

`leanos-vtd-plan` is a host-only executable. It receives the final-ELF
remapping-table symbol addresses and the CPU page-table layout, builds the same
finite `VTdBootPlan.Input` over the accepted deny-all device-domain state,
requires `compile` to accept it, and emits the canonical root/context table
words and pinned register constants as a C header. If the linked plan is
rejected it fails rather than emitting tables.

## Assumptions, TCB, and exclusions

Proved: everything decided in Lean above — the codec round-trip and injectivity,
the deny-all projection agreement with `IOMMU.validateCore`, the table-frame
reservation and disjointness, the MMIO/RAM separation of the page-table policy,
and the activation-order encoding.

No axiom, `unsafe`, `@[extern]`, `@[implemented_by]`, or FFI is added, and the
trusted computing base inventory is unchanged.

Trusted and out of scope for this issue: the ACPI DMAR firmware description and
its correspondence to the pinned unit, PCIe requester-ID delivery, VT-d MMIO
register semantics and table walks, IOTLB and context-cache invalidation
behavior, the boot assembly and C that will map the MMIO window and write the
tables, the linker and generated header, QEMU's VT-d implementation, and any
claim that the final binary refines this model. Enabling a bus master,
performing a real assigned-device transfer, dynamic map/unmap, interrupt
remapping, PASID, ATS, device IOTLB, SR-IOV, hotplug, SMP, and timing or covert
channels are all excluded. The deny-all PCI quarantine of
[dma-quarantine.md](dma-quarantine.md) is preserved unchanged.
