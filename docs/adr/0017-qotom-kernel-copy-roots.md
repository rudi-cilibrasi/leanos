# ADR 0017: Qotom kernel page tables and bounded copy windows

## Status

Proposed for review under [#329](https://github.com/rudi-cilibrasi/leanos/issues/329).
This is a design gate for #291 and #332. The page-table projection has initial
Lean proofs; the complete transition model and runtime mechanism are not yet
implemented. This record does not authorize CPL3 on Qotom.

## Required protection and alternatives

The first Qotom scenario should retain architectural denial of ordinary kernel
access to user-owned memory outside a validated copy. Its J1900 has SMEP and NX
but no SMAP. [ADR 0006](0006-smap-user-copy-window.md) relies on SMAP to enforce
that denial while AC is clear. The same instructions and claim cannot be reused
on this CPU.

Removing STAC/CLAC and keeping only software bounds checks would preserve the
modeled explicit-copy policy, but ordinary supervisor loads could still reach
mapped user memory. That weaker lab claim is possible under the issue's scope,
but it does not meet the protection selected here. Merely changing a user leaf
to supervisor is also insufficient: supervisor code can still access it.

Use separate page-table roots instead. The closed kernel root omits every
virtual alias of each user-owned physical frame, including supervisor aliases
in the identity map. A bounded copy root adds only dedicated supervisor, NX
aliases for pages covered by a validated copy. Subject roots remain distinct.
This design requires auditing physical aliases, not only virtual U/S bits.

## Proposed transition contract

1. Before CPL3, publish the complete live user-frame inventory and construct a
   closed root with those frames absent at every virtual address. Use only 4 KiB
   leaves; reject large-page mappings rather than leaving an unexamined alias. Keep kernel
   code, entry stacks, TSS, IDT, page tables and required device mappings available
   in each root where they are used. Reject any overlap between protected frames
   and indispensable kernel frames.
2. Every entry from a subject switches to the closed root before calling C or
   dereferencing a subject-supplied pointer. The short transition uses only
   fixed trusted operands and shared entry mappings. Entry cleanup verifies the
   selected root. No no-SMAP entry path executes STAC or CLAC.
3. Validate the entire caller-owned buffer with the existing `UserCopy.validate`
   contract: at most 16 bytes, canonical and nonoverflowing bounds, current
   address-space/lifetime authority, and direction-appropriate permissions.
   Preserve its cross-page case, which needs at most two copy aliases. Validation
   happens under the closed root; a rejected request changes no memory.
4. Hold the validated mappings and frame lifetimes stable. The initial mechanism
   is BSP-only, with maskable interrupts disabled during the transaction and DMA
   quarantined by the selected platform policy. No allocation, callback, subject
   switch or mapping mutation may run while the window is open.
5. Publish the bounded aliases and select the copy root. The transfer stub uses
   the validated byte count and offsets, not the original user virtual pointer.
   It may read source pages or write destination pages according to the admitted
   direction; it cannot execute those aliases. The kernel buffer remains a typed
   bounded object. Restore and verify the closed root before ordinary C resumes.
6. For the first implementation, an interrupt or fault during the transfer aborts
   the transaction and terminates the scenario. Entry first attempts the fixed
   closed-root transition. A failed cleanup enters an assembly terminal path;
   it must not return to C or CPL3 with an unverified copy root. Do not claim that
   a fault rolls back bytes already copied: the model must bound any partial
   effects to the validated prefix and preserve all other memory.
7. A subject return selects only that subject's validated root in the final
   assembly return sequence. No arbitrary kernel work may occur between that
   switch and IRET. Nested exception paths must obey the same closed-root rule.

Require PCID and global-page translations disabled for this initial strategy,
with checked control readback and the required translation invalidation at each
root transition. Do not infer effective cleanup from a CR3 address comparison
alone. The trusted page-table construction and invalidation operations must
establish which translations can actually remain usable.

## Architecture basis and claim delta

Intel's [System Programming Guide, Volume 3A](https://cdrdv2-public.intel.com/819714/253668-sdm-vol-3a.pdf),
sections 4.6 and 4.10.4, supplies the architectural access-right and invalidation
rules on which this proposal depends. Absent translations deny access; clearing
U/S does not deny supervisor access. CR3 invalidation behavior depends on PCID
and global-page controls, so those controls are part of the strategy rather
than an assumed side effect. These rules motivate the proposed construction;
they do not verify our page tables, assembler, compiler or processor.

The proposed Qotom claim is denial through missing translations under a closed
kernel root, with bounded temporary aliases for explicit copies. It is not a
claim that SMAP is enabled, that AC controls access, or that a q35 SMAP fault probe
passed. This is an architectural access claim, not a speculative-execution or
covert-channel claim. Existing q35 SMAP evidence keeps its original meaning.

`KernelUserRoot.close` models the first projection. Given a complete protected
frame inventory, it removes all aliases of those frames and preserves retained
leaves. Its access-denial theorem uses `X86PageTable.classify` without assuming
SMAP or AC. The inventory's completeness, actual root installation, TLB state,
copy aliases, byte transfer, exceptional cleanup and return ordering are outside
that initial theorem. Those obligations remain before any runtime admission.

## Evidence required before enabling CPL3

The remaining model must connect validated copy authority to the selected root,
alias permissions, byte progress, interrupted/faulted copies and cleanup results.
It must prove nonamplification, exact or bounded-prefix footprints, preservation
outside that footprint, closed-root restoration and terminal behavior after
cleanup failure. The current atomic SMAP model does not establish these new
exceptional-path properties.

Lean and generated C must agree on the complete strategy selection. Execution
fixtures without SMAP must cover permitted and forbidden buffers, zero/maximum
lengths, page boundaries, overflow, stale authority, injected interruption/fault,
cleanup failure and attempted access through an omitted supervisor alias.
Final-object checks must cover all reachable entry, copy and return paths,
including NMI and double-fault handling, and reject unsupported STAC/CLAC or
CR4.SMAP writes on the selected path. Records must name the new strategy and
report SMAP as absent. Physical Qotom evidence remains required. Until these
obligations are discharged, retain a typed pre-CPL3 rejection.
