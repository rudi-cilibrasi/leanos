# Deterministic VT-d boot plan

`LeanOS.VTdBootPlan` is a finite, bounded model of the DMA-remapping tables
that the boot image installs for the pinned q35 `intel-iommu` unit before
translation is enabled. It is a Lean model, a host-only generator, and a
generated scalar activation boundary linked into every image. The boot image
maps the unit's MMIO window, constructs the generated deny-all tables from
scrubbed reserved frames, and enables translation in a fixed fail-closed
order before CPL3; it does not enable an assigned device, and it establishes
no refinement correspondence to generated C, boot assembly, QEMU, firmware,
PCIe, or physical hardware.

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

Before CPL3 the guest reads the unit through four reviewed `noinline`/`noipa`
volatile accessors and requires the exact pinned version, capability, and
extended-capability words, zero global status (translation disabled), zero
fault status, and a zero root-table pointer, then checks the generated tables
are the deny-all shape (one present root entry naming the context-table frame,
no present context entries) and that the generated frames equal the linked
symbols. The page is mapped write-back under the pinned TCG emulator, which
models no cache; the supported leaf encoding has no cache-disable bit, and
qualifying real hardware (where the window must be uncacheable) remains out
of scope.

## Fail-closed activation

After the quiescent validation the boot image executes the fixed activation
order: scrub both table frames (write-then-verify), construct the live tables
from the generated arrays with a read-back comparison, publish the root
pointer and set it in the global command register, globally invalidate the
context cache and then the IOTLB (bounded polls; exhaustion is a typed
failure), enable translation, and verify the exact enabled global status with
an empty fault status. Each completed step appends its nibble to the
activation journal, and the final decoded state plus journal must satisfy the
generated `leanos_validate_vtd_activation` boundary — the same scalar
`validateActivation` proved deterministic and exercised tag-by-tag in Lean —
before the boot continues. The evidence is four `LEANOS/21` serial lines
(quiescent unit, deny-all plan, table construction, activation), validated
structurally with frame-adjacency and root-pointer cross-checks by every boot
runner and retained per scenario as
`build/boot/vtd-activation-snapshot-<scenario>.tsv`.

Every outbound CPL3 gate re-observes the enabled status, empty fault state,
published root pointer, and the complete live tables against the generated
plan, so a post-validation mutation cannot reach user code silently: the
`vtd-translation-disable` machine negative (return-corruption mode 26)
disables translation at the gate and must terminate with the typed
`vtd-live-status` rejection. `scripts/check-vtd-mmio-policy.sh` confines
window-pointer derivation to the four accessors, pins the source and
final-ELF write order (root pointer, set-root command, context-cache
invalidation, IOTLB invalidation, translation enable, then the generated
validation call), and rejects any unreviewed MMIO write caller in the final
ELF; `scripts/test-vtd-mmio-policy.sh` proves mutated sources are rejected.
All PCI bus masters remain command-disabled, so the enabled deny-all tables
translate no DMA and the fault status stays empty. Passthrough support (ECAP bit 6),
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

`VTdBootPlan.compile` is the only constructor of `Plan` and the single authority
for every VT-d table word any q35 image installs. A `Plan` is a privately
constructed checked `Input`; every table (root, context, and the three
second-level levels) is a function of that checked input, so an accepted plan
cannot be reconstructed with substituted tables. Every accepted plan has one
present root entry for bus 0 selecting the reserved context table.

- **Deny-all.** Without a grant binding the plan has 256 absent context
  entries. This is exactly the projection of an accepted static device-domain
  `IOMMU.State` that carries no live assignment or mapping:
  `accepted_state_deny_all` requires the model state itself to be deny-all,
  `accepted_agrees_with_domain_projection` shows no source and generation
  resolves to a live assignment in that state, and `accepted_maps_no_frame`
  and `accepted_unbound_translates_nothing` show no frame is reachable.
- **One assignment.** A state with exactly one live assignment is accepted
  only together with a reviewed `GrantBinding`: the requester the assigned
  function answers as, the three linked second-level table frames, and the
  hardware frame holding model page 0 of each granted model frame. The binding
  carries no authority of its own; which IOVA pages are mapped, with which
  permission, and at which model frame offset still comes only from the
  accepted `IOMMU.State`. The bound requester's context entry selects a
  three-level second-level table whose top and directory levels each hold one
  read/write entry at slot 0, and whose leaf maps each granted model page to
  one 4 KiB hardware page with the granted permission.

`compile` rejects, with a typed reason: a missing reservation, more than one
live assignment, a mapping without its assignment, an assignment without a
binding or a binding without an assignment, an out-of-range domain or
requester, duplicate, CPU-aliasing, out-of-range, or unreserved table frames, a
mapping whose model frame the binding does not place, an empty permission, a
grant beyond the single leaf table, a granted frame out of range, and
(`grantOverlapsReservedFrame`) a granted frame that overlaps a kernel
reservation other than the loaded image, a CPU page-table frame, or any VT-d
table frame.

The general theorem `accepted_translation_exact` states that for every
requester and every IOVA page, walking the encoded root, context, and
second-level words of an accepted plan (`Plan.translate`) yields exactly
`grantedTranslation`: the granted hardware frame and permission for the bound
requester's granted pages, and nothing anywhere else.
`accepted_translation_from_grant` ties each translation back to one model
mapping, `accepted_grant_translates` shows no granted page is dropped, and
`accepted_translation_avoids_protected` shows no translation reaches a
protected frame. `accepted_requesters_bound_once` fixes the 256-entry context
table indexed by requester. These are statements about the encoded tables, not
about the IOMMU's table walk, which remains a trusted hardware boundary. The
assigned-EDU and device-service tables are instances: the per-scenario facts
that remain (`deviceServiceState_shape`, `deviceServiceTransfer_window`) are
about the model state and its transfer admission, and the executable vectors
in `VTdBootPlan` check the translation of both scenarios over the sample
layout.

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
remapping-table symbol addresses and the CPU page-table layout and builds the
finite `VTdBootPlan.Input` values those symbols represent: the deny-all state,
the assigned-EDU state bound to requester 16 and the linked read/write
buffers, and, for a device-service image, the device-service state bound to the
start of the executor scratch. It requires `compile` to accept every one and
emits only compiled table words (`leanos_vtd_root_table`,
`leanos_vtd_context_table`, the `leanos_vtd_assigned_*` context and
second-level arrays, and `leanos_vtd_service_second_level_table`) plus pinned
register constants as a C header. If any plan is rejected it fails rather than
emitting tables. Moving the assigned and service tables onto `compile` left
every generated header byte-identical.

The activation order is unchanged and stays fail-closed: the image writes the
tables, reads them back and compares them with the generated words, enables
translation, and rechecks the live tables before every CPL3 entry; any mismatch
stops before CPL3.

## Assumptions, TCB, and exclusions

Proved: everything decided in Lean above — the codec round-trip and injectivity,
the deny-all projection agreement with `IOMMU.validateCore`, the exact
translation of the encoded tables for every requester and IOVA page, the
table-frame reservation and disjointness, the separation of granted frames
from protected frames, the MMIO/RAM separation of the page-table policy,
and the activation-order encoding.

No axiom, `unsafe`, `@[extern]`, `@[implemented_by]`, or FFI is added, and the
trusted computing base inventory is unchanged.

Trusted and out of scope for this issue: the ACPI DMAR firmware description and
its correspondence to the pinned unit, PCIe requester-ID delivery, VT-d MMIO
register semantics and table walks, IOTLB and context-cache invalidation
behavior, the boot assembly and C that will map the MMIO window and write the
tables, the linker and generated header, QEMU's VT-d implementation, the
platform binding of a model device to a PCI requester and of a model frame to
linked memory, and any claim that the final binary refines this model or that
the hardware walk agrees with `Plan.translate`. Dynamic map/unmap, more than
one assigned device, interrupt
remapping, PASID, ATS, device IOTLB, SR-IOV, hotplug, SMP, and timing or covert
channels are all excluded. The deny-all PCI quarantine of
[dma-quarantine.md](dma-quarantine.md) is preserved unchanged.
