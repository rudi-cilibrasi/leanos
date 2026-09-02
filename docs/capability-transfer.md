# Sealed capability transfer

`LeanOS.CapabilityTransfer` is a finite, sequential reference model for passing
at most one capability with a capacity-one endpoint message. Data-only IPC
remains available through `LeanOS.EndpointIPC`; an authority-bearing offer uses
the same inert two-word payload but resolves both its endpoint and source from
the trusted caller's live slots.

## Semantics

An accepted `offer` requires endpoint `send`, source `grant`, a nonempty
kind-compatible requested-rights set, and a subset of the source rights. It
allocates a never-reused identity in the authoritative `Capability.State`
derivation graph and puts a `Sealed` record beside the envelope. The identity
is not installed in any subject slot, so it grants no ordinary authority while
in flight. The payload cannot choose the object, kind, identity, parent, or
sender.

Holder-facing callers use `sendDataHandle`, `offerHandles`, `acceptHandle`,
`retireObjectHandle`, `destroyEndpointHandle`, and `revokeSubtreeHandles`.
These bind every authority-consuming endpoint, source, lifecycle, authority,
and lineage-root reference to its installed capability generation. The raw-slot
definitions are internal transition kernels used after those checks; replaying
an old handle after same-slot replacement is rejected as stale.

Userspace entry uses the corresponding canonical word boundaries:
`offerWords`, `acceptWord`, `retireObjectWord`, `destroyEndpointWord`, and
`revokeSubtreeWords`. The last operation resolves both the revocation authority
and lineage root in their trusted subjects' capability spaces before it can
cancel installed or sealed descendants. Acceptance records both exact
resolutions; malformed and stale words preserve the complete composite state.

`accept` derives the receiver from trusted caller context. It first checks
receive authority, endpoint lifetime, the complete envelope, destination slot,
object lifetime and kind, and the exact append-only derivation record. Only
then does one transition install the sealed identity and clear both envelope
and pending record. An occupied or out-of-range slot and every stale/canceled
case preserve the complete pre-state. A second accept sees an empty mailbox.

## Cancellation and lifetime

Cancellation removes both sides of an offer but retains append-only derivation
history. `cancelSenderOffers` cancels offers made by a sender without changing
subject liveness or installed slots. Authoritative sender termination must be
composed with `SubjectLifecycle.terminate`; this model deliberately does not
carry the ownership and scheduling state needed to claim that transition.
There is no preselected receiver to cancel. `retireObject` cancels every offer
of the retired object;
`destroyEndpoint` also clears that endpoint's mailbox. The composed
`revokeSubtree` uses the shared ancestry relation to remove installed and
sealed descendants atomically. Thus a canceled identity cannot later become
usable, even if a numeric slot or object identifier is reused.

The composite runtime publishes the same rule. `publishSubtreeRevocation`
takes the revoked capability store produced by the runtime-safe capability
guard and cancels every sealed descendant of the lineage root
(`descendsFromRoot`) in the same step, so `FailStop.gate`'s
`capabilityRevokeSubtree` operation cannot clear an installed ancestor while
leaving its sealed descendant receivable.
`gate_capabilityRevokeSubtree_accepted_cancels_sealed_descendants` states the
atomic cancellation of envelope and pending record,
`gate_capabilityRevokeSubtree_accepted_authority_monotone` states that no
retained sealed record or installed slot descends from the revoked root,
`gate_capabilityRevokeSubtree_accepted_retains_history` keeps the canceled
identity allocated forever, and
`gate_capabilityRevokeSubtree_accepted_preserves_unrelated` leaves unrelated
lineages, mailboxes, slots, contexts, and mappings exactly as they were. The
composite operation names its authority and lineage root by raw slot index in
the kernel-derived current subject; the generation-bound word forms remain the
`revokeSubtreeWords` boundary of this model.

Address-space authority can be sealed and received, but this composition does
not yet carry `VirtualMapping.State`; therefore it has no atomic
address-space-destruction adapter. Callers must not model address-space
destruction by mutating only the embedded capability store. The corresponding
authoritative lifecycle composition remains deferred rather than proved here.

The explicit observer vocabulary distinguishes offer, receipt, and
cancellation and includes the receiver authority change. Payload contents and
trusted sender provenance remain independently visible.

## Evidence and limits

`WellFormed` states that every pending record has one live compatible object,
an exact derivation entry, an earlier parent whose rights attenuate the offer,
a fresh bounded identity, one mailbox envelope, and no installed slot with the
sealed identity. `pending_rights_conserved` exposes the parent attenuation;
`accepted_installs_exactly_once` proves successful receipt clears the unique
envelope and installs exactly that sealed identity in the trusted receiver's
chosen slot. These are Lean model proofs, not claims about generated code.

Each lookup and slot update is constant time in this functional model.
Transitive revocation follows at most `nextIdentity` parent steps per pending
offer; the concrete slice has one offer per endpoint and a capacity-one
mailbox. Implementations must impose a finite endpoint bound.

The repository proof-integrity check compiles this module with Lean's
no-sorries mode and rejects undocumented `axiom`, `constant`, `unsafe`,
`extern`, and FFI additions across first-party sources. The model adds none of
those trusted escapes.

Concurrency, SMP, blocking, timeouts, fairness, move-only capabilities,
multiple attachments, queues, broadcasts, capability merging, and a stable
general userspace ABI remain excluded. The bounded composite adapter exposes
the canonical accepted receipt's returned handle as result word one and has
generated-C differential tests.

## Bounded boot slice

The `capability-transfer` boot image connects five user operations plus one
kernel scheduling operation to a dedicated canonical trace. Subject A is
formally bound to subject 1 and resolves its own generation-bound `0x20001`
endpoint/source handle before offering a send-only descendant. An explicit
authoritative resumable edge then selects subject 2; only its exact generated
reply authorizes the existing complete-context return path to replace A's
saved register bank and CR3 with the kernel-owned subject-B context. B first
demonstrates that the sealed handle cannot send, accepts into slot 3, retains
the returned `0x60003` word in a register, sends through that exact word, and
receives a state-preserving denial when it tries the nondelegated receive
right. A regression theorem checks the initial caller, source-handle
resolution, sealed record `(sender = 1, parent = 2)`, and post-switch
`(subject, address space) = (2, 2)` binding directly.

C retains one opaque canonical state token. After each generated call it
derives the next token from the generated control word; there is no C pending
table, rights mask, child/parent record, destination installer, capability
lookup, or mailbox policy. The control and value accessors receive the same
six immutable words. In this dedicated image the entry stub carries canonical
argument 3 from saved user RSI; other images retain their saved-RFLAGS entry
contract.

Run the real image with:

```sh
LEANOS_BOOT_SCENARIO=capability-transfer ./scripts/run-image.sh
```

`scripts/check-capability-transfer-machine.sh` inventories the two generated
call sites, the fourth-word entry bridge, the one A and four B CPL3 syscall
sites, and B's full-width returned-handle use in the final ELF.
`scripts/test-run-capability-transfer.sh` checks the exact ordered protocol and
controlled mutations for payload-selected authority, widened rights, early
installation, truncated or replaced return values, stale A context, a
stateless adapter label, trace splicing, missing/reordered records, forged
success, guest error, and timeout.

These checks are machine integration evidence, not a proof that C, assembly,
the compiler, QEMU, or x86 execution refines Lean. The generated boundary,
manual entry/scheduling glue, and diagnostic formatting remain in the trusted
computing base.
