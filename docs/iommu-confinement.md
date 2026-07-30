# Static IOMMU device-domain confinement

`LeanOS.IOMMU` is the first finite assigned-device authority model. It is a
Lean model only. It does not program Intel VT-d, construct remapping tables,
invalidate an IOTLB, enable EDU DMA, or establish correspondence to generated
C, QEMU, firmware, PCIe, or physical hardware.

## Authority and bounded identities

The model has finite bounds for owners, platform device slots, requester/source
identities, domains, frames, capability slots, mapping slots, IOVAs, and
transfers. Assignment, domain, and mapping identities pair a bounded slot with
a nonzero generation. Their kernel-owned counters stop before the reserved
all-ones terminal generation; the issuance rule never wraps, decrements, or
reuses a generation.

An assignment request names only a bounded platform device slot. The kernel's
fixed `deviceTable` selects its requester/source identity; the current
authoritative owner and the next assignment/domain generations select every
other privileged field. A grant request can name generation-checked
assignment and existing `CapabilityHandle.Handle` values, an aligned IOVA,
bounded offsets and length, and an attenuated direction set. It cannot name an
owner, requester/source identity, domain, or physical frame. The capability
resolver supplies a live generation-checked frame and its range.

The finite `validateCore` predicate checks registry bounds and uniqueness,
source and domain bindings, strictly older live generations, live frame
lifetimes, owner agreement, exclusion of kernel/page-table/allocator-metadata
frames, canonical alignment, complete-range containment, permission
nonemptiness, and pairwise IOVA disjointness. Because physical memory is keyed
by `FrameId`, it also requires every simultaneously live frame record to have
a distinct physical frame ID; generations distinguish reused lifetimes only
after the prior lifetime is no longer live. Each local frame-capability entry
must resolve through the reused generation-bound `CapabilityHandle` in an
existing well-formed `LeanOS.Capability.State`, agree on memory-object identity
and provenance identity, resolve through the kernel-selected `frameAuthority`
binding to the exact frame handle/lifetime, and attenuate its read/write
rights. Same-owner equality alone is not object authority. `State` carries
both successful finite validation and that capability/frame-authority
well-formedness as proofs. Every accepted control transition returns another
such state. A rejected `Outcome` has no post-state constructor, so its state
projection is definitionally the complete input state.

## Control operations and lifecycle

The total deterministic gate supports assignment, capability-derived grant,
range/direction attenuation, unmap, assignment teardown, checked frame release,
and current-owner termination.

- Attenuation can only remove read/write directions and narrow a mapping's
  IOVA/backing-frame range. It retains the original assignment, domain, owner,
  frame lifetime, and mapping generation.
- Teardown removes the assignment and every mapping that names it atomically.
- Frame release rejects while any DMA mapping still reaches the exact frame
  generation. After mappings are removed it retires the frame and clears its
  local capability references.
- Current-owner termination removes all owned assignments, their mappings and
  capabilities, then retires ordinary owned frames while retaining
  kernel/page-table/allocator metadata.
- Old transfer requests carry the retired assignment generation and therefore
  reject after teardown and reassignment of the same device slot/source.

`AuthoritativeExtension.Coherent` relates the projections: the IOMMU current
owner is the kernel-selected subject, its capability-provenance state is the
kernel capability state, and every retained assignment, mapping, capability,
and ordinary live frame belongs to a live kernel subject. Every local
capability's object-to-frame binding must equal the kernel memory binding, and
every mapping must remain range- and permission-attenuated from one such
capability. Kernel and IOMMU updates commit atomically.
Scheduler/current-subject changes synchronize the owner. A changed lifecycle
or capability projection revokes DMA mappings and cached capability records,
removes dead-owner assignments, and retires their ordinary frames; if
reconciliation cannot validate, the complete extension stutters. Thus
capability copy/revoke, CPU mapping, lifecycle, scheduler, blocking, and
deferred-cancellation operations cannot publish a kernel post-state paired
with detached authority. `gatedByKernel` accepts the complete
`AuthoritativeExtension` together with its invariant, not separately supplied
kernel and IOMMU projections. Its accepted result carries the coherent
complete extension and its preserved invariant; a locally valid detached
projection cannot invoke the public grant path. The gate admits IOMMU control
only while the global execution latch is running; a busy handler or fatal
latch rejects without a post-state, and every finite post-fatal suffix is
absorbed.

The existing `DMAQuarantine` projection is unchanged. `QuarantineExtension`
composes an IOMMU state with that deny-all baseline. With no assignments or
mappings, the earlier nonempty q35 quarantine theorem still makes every
contracted unowned-device attempt a complete memory stutter. Assigned-device
authority is not smuggled into the old q35 snapshot or its generated scalar
validator.

## Device observations and transitions

CPU virtual addresses and IOVAs are distinct types and registries. A device
transfer supplies only a requester/source identity, assignment generation,
IOVA, and complete length. Translation requires:

1. an exact live source/generation assignment;
2. its kernel-bound domain and owner;
3. one mapping containing the complete transfer;
4. sufficient read or write permission;
5. the exact live backing-frame generation and same owner;
6. exclusion of kernel, page-table, and allocator-metadata frames; and
7. containment of the complete translated range in the frame lifetime.

Every successful `Translation` carries the exact successful assignment,
mapping, and frame lookup equations from the authoritative state. Reads return
byte-list observations and do not change state. `AuthorizedReadView` carries
the exact successful `deviceRead` equation and observed bytes, so its finite
confidentiality theorem begins with actual model observations rather than
caller-constructed records. The one-step and finite-view results show that
changing every byte outside the authorized readable backing ranges cannot
change those observations.

Writes are state transitions. The one-step integrity theorem leaves all
assignment, domain, mapping, frame-ownership, capability, issuer, and current
owner projections equal and changes only the exact authorized backing range.
The live-physical-frame uniqueness theorem upgrades translation's record-level
owner equality to the `FrameId` key used by memory, and
`write_integrity_other_owner_frame` therefore preserves every byte of a live
frame owned by another subject. The trace-level protected, physically
unassigned, and other-owner lemmas derive no-touch inductively while device
steps preserve the frame, mapping, and ownership projections. The stable
finite-trace theorem accepts one of those frame classifications, rather than
assuming no-touch directly, and preserves every byte of the classified frame.

## Assumptions, TCB, and exclusions

`DeviceSemantics` records the deliberately small platform assumption that the
hardware boundary faithfully supplies the modeled requester/source identity
and transfer range, and that trusted software attaches the active assignment
generation before lookup. PCIe does not carry that software generation. The
assumption does not grant authority or assume correct translation or
confinement; those are decided and proved in the Lean model.

No axiom, constant, `unsafe`, `extern`, FFI declaration, or other trusted Lean
declaration is added. The TCB inventory is unchanged. Interpreting this static
model as a real-machine claim would additionally require unproved
correspondence for ACPI DMAR discovery, PCIe requester IDs, VT-d programming
and table-walk semantics, cache/IOTLB invalidation, device obedience, memory
ordering, interrupt remapping, generated code, handwritten C/assembly,
compiler/linker output, firmware, QEMU, and the final binary. Those are not
claimed here.

Also excluded are stale IOTLB mechanics, PASID, SR-IOV, ATS, interrupt
remapping, MSI/MSI-X, hotplug, SMP/concurrency, user-space drivers, arbitrary
scatter/gather, shared-page accounting, malicious-device protocol correctness,
denial-of-service freedom, timing/covert channels, and hardware qualification.
