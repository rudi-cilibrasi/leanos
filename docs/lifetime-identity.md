# Bounded lifetime-identity issuance

`LeanOS.LifetimeIssuer` is the one reviewed lifetime-identity abstraction, and
`LeanOS.BoundedLifecycle` makes its two typed issuers the authoritative
creation path for subject and object lifetimes. Freshness is no longer only a
distributed history property: every accepted creation receives exactly the
kernel-owned issuer's next representable identity, and the composite result
returns that identity to the caller instead of accepting one from an untrusted
word.

## Representable range, reserved encodings, and codec

Each identity domain occupies one canonical 64-bit word. The zero word is the
reserved null encoding and the all-ones word (`identityReserved`, value
`0xffff_ffff_ffff_ffff`) is the reserved terminal encoding, so the
representable identities are exactly `1 .. 2^64 - 2`. The `encode`/`decode`
codec is total, round-trips exactly on the representable domain, rejects both
reserved encodings with typed errors, and never truncates or wraps an
out-of-range natural into a word. Subject identities, object identities,
capability identities (with their separate 48-bit generation bound in the
[capability-handle model](capability-handles.md)), slots, frames, and
address-space names remain distinct resources; no counter is shared between
them, and the `Domain`-indexed issuer type keeps the subject issuer and the
object issuer apart even at equal word width.

## Next-value rule and typed exhaustion

An issuer stores only the next counter value; `1` is the first issued identity
of each domain. `issue` is a total function: it either hands out exactly
`next` and advances by exactly one, or returns the typed `exhausted` result
without any successor issuer. Exhaustion is decided fail-closed: the malformed
zero counter and every counter at or past `identityReserved` refuse issuance,
so the terminal encoding can never be issued and wrapping or reuse is never an
issuance policy. Machine-checked issuer theorems cover determinism, the exact
next-value rule, representability and encodability of every issued identity,
strict monotonicity, the counter bound, and issuer-level exhaustion
absorption; executable vectors exercise the first, penultimate, terminal,
past-terminal, malformed-zero, and reserved-encoding boundaries.

## One object-lifetime authority across kinds

`BoundedLifecycle.Runtime` holds both issuers next to the existing
subject-lifecycle state and the object-domain state. The endpoint view is
derived from the one shared object-domain memory state rather than duplicated,
so memory allocation, endpoint creation, and address-space creation all draw
from the single object issuer: an identifier retired under one kind can never
be rebound under another kind. The existing `issued`/`issuedAddressSpace`
histories are preserved as append-only derived views whose union
(`issuedObject`) stays strictly below the counter; they are never independent
allocators.

## Atomicity, confinement, and the runtime invariant

Issuance is atomic with creation: every rejected or exhausted creation
preserves the complete runtime, including both counters and both histories,
and a counter advances exactly once only together with an accepted internal
transition that installs exactly one new live lifetime. Termination, release,
endpoint destruction, address-space destruction, and failed allocation never
read or write an issuer. The untrusted request words of the command adapters
are inert by construction, so no caller word can select the returned identity,
skip the next value, reach the other domain's issuer, or turn an exhaustion
result into success.

The runtime invariant (`BoundedLifecycle.Invariant`) states counter/history
agreement: every issued subject or object identity is representable and
strictly below its domain counter, live lifetimes and kind registrations are
recorded in the single object history, and both counters stay inside the
bounded domain. Under the invariant, subject creation is total and
deterministic — decided exactly by issuer exhaustion — and no composite
creation can be rejected as a replayed or still-live identity.

## Stale-lifetime safety and exhaustion absorption

Along every finite trace of composite operations, machine-checked theorems
establish: invariant preservation; history and counter monotonicity; that a
retired object identity or terminated subject identity can never be made live
again; that an issued identity's kind is immutable — it either keeps its exact
kind or is retired, and once retired never regains any kind; and that an
exhausted issuer remains exhausted under every ordinary transition. The
capability-generation bound remains a separate resource: with a live identity
issuer but an exhausted root-capability generation, creation returns the
precise state-preserving `generationExhausted` denial rather than the
identity-domain `exhausted` result, and executable traces witness both
failures separately. The stable contract wrapper is
`SC-LIFETIME-IDENTITY-NO-REUSE` in the
[security claim index](security-claims.md).

A negative regression (`tests/negative/WrappingIssuerReuse.lean`) replaces the
bounded issuer with a modulo-wrapping counter and shows on a concrete trace
that the recycled counter re-issues a terminated identity — the stale-lifetime
proposition evaluates to false, so the hostile policy cannot type-check
against the model's guarantees.

## Model-to-machine boundary and non-goals

These are model-level results about the Lean issuers and the composed
lifecycle transitions. The subject-domain lifecycle state and the
object-domain capability store remain the existing separate authoritative
shapes; unifying them into one coherent runtime is issue #104, which can
compose through the exported projection, monotonicity, and domain-separation
lemmas without unfolding the lifecycle maps. No public create/destroy syscall
ABI is exposed by this slice, and no machine-word refinement of the issuer
counters, generated C, compiler, boot chain, QEMU, hardware, concurrency,
process-manager policy, fork/exec, persistence, or history
recycling/compaction is claimed. A real kernel that stores the counters in
64-bit words inherits exactly the reviewed reserved encodings and exhaustion
semantics; that correspondence is a trusted implementation obligation, not a
proved refinement.
