# Endpoint IPC model

`LeanOS.EndpointIPC` is a sequential reference model for capability-authorized
message passing. Each live endpoint has one deterministic, nonblocking mailbox
with capacity one. `send` reports `full` rather than blocking, and `receive`
reports `empty`. A message contains exactly two `UInt64` words and is delivered
in the only possible FIFO order.

Endpoint capabilities use named `send`, `receive`, `grant`, and `revoke`
rights. Memory and address-space capabilities cannot carry IPC rights. Shared
capability copy and revoke operations enforce kind validity and rights-subset
attenuation, so delegation cannot introduce authority absent from its source.
`revokeSubtree` removes an endpoint handle and every transitively delegated
descendant while preserving independent roots. Direct slot revoke remains
available and intentionally has no lineage semantics.

## Identity, provenance, and cleanup

The caller passed to `send` is trusted operation context. The model records
that caller as the envelope sender; payload words cannot select or override
it. Payload words are inert data even when they numerically equal a subject or
object identifier. Messages do not transfer capabilities.

Endpoint object identifiers are never reused. Creation rejects an identifier
that is live or was issued before. Destruction retires the typed object, clears
its mailbox, and removes every installed capability naming it. Consequently a
pending message and stale authority cannot become visible through a later
object incarnation.

## Machine-checked scope

The composite invariant relates capability well-formedness, live endpoint
kind, issued lifetime state, the capacity-one mailbox, and append-only accepted
send history. The Lean theorems establish typed state-preserving rejection,
send and receive authority confinement, trusted-caller recording, delivered
message membership in accepted-send history, delegation non-amplification, and
complete destruction cleanup. Executable traces cover the successful round
trip, full and empty mailboxes, one-way delegation, forged sender data,
wrong-kind handles, revocation, pending-message destruction, repeated destroy,
and stale replay.
The adversarial endpoint trace delegates send authority through an intermediary
and confirms both intermediary and descendant fail after subtree revocation.

Endpoint authority exposed to a holder is represented by the shared
[generation-bound capability handle](capability-handles.md), not an
endpoint-specific token. Clearing, revoking, or destroying an endpoint
capability makes that handle stale even when its bounded slot is later reused.
The current IPC model has no implicit capability transfer; a future sealed
transfer may issue a handle only after atomic receive-side installation.

These are properties of the executable Lean model. There is no claim that the
boot image implements IPC or refines this model. The ghost send history is
proof evidence, not externally observable endpoint storage.

## Exclusions and trusted assumptions

There are no blocking calls, scheduler interactions, concurrency, fairness,
wakeups, variable-size buffers, user pointers, shared memory, or implicit
capability transfer. The model does not prove noninterference or address timing
and covert channels. Trusted modeled caller identity must eventually be
supplied by a separately justified kernel entry boundary. The Lean compiler,
runtime, generated code, boot chain, emulator, and hardware remain outside
these model-level proofs.
