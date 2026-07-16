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

Holder-facing callers use `offerHandles` and `acceptHandle`, which bind the
endpoint and source references to their installed capability generations.
The raw-slot `offer` and `accept` definitions are internal transition kernels
used after that check; replaying an old handle after same-slot replacement is
rejected as stale.

`accept` derives the receiver from trusted caller context. It first checks
receive authority, endpoint lifetime, the complete envelope, destination slot,
object lifetime and kind, and the exact append-only derivation record. Only
then does one transition install the sealed identity and clear both envelope
and pending record. An occupied or out-of-range slot and every stale/canceled
case preserve the complete pre-state. A second accept sees an empty mailbox.

## Cancellation and lifetime

Cancellation removes both sides of an offer but retains append-only derivation
history. `terminateSender` is only the capability-transfer slice of subject
cleanup: it marks the subject dead in the embedded capability store, clears
that holder's slots, and cancels offers made by that sender. It is not the
authoritative `SubjectLifecycle.terminate` transition and does not claim to
clean that model's ownership, mappings, scheduling, or mailbox state. There is no
preselected receiver to cancel: a terminated subject cannot pass trusted
receive lookup. `retireObject` cancels every offer of the retired object;
`destroyEndpoint` also clears that endpoint's mailbox. The composed
`revokeSubtree` uses the shared ancestry relation to remove installed and
sealed descendants atomically. Thus a canceled identity cannot later become
usable, even if a numeric slot or object identifier is reused.

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
multiple attachments, queues, broadcasts, capability merging, and a boot ABI
are excluded. The Lean kernel, compiler, runtime representation, and any
future machine adapter remain in the trusted computing base. Compilation or
QEMU execution would be integration evidence, not verification of this model
in a binary.
