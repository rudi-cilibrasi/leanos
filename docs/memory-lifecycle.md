# Capability-safe frame lifetimes

`LeanOS.MemoryLifecycle` is a finite, sequential executable composition of the
capability and physical-frame allocator models. A live memory object has one
bound frame; that frame is allocator-owned by the same object identifier; and
every installed memory capability names such a live binding. Non-memory objects
share the capability registry but are not forced to own frames.

Object identifiers use a monotonic lifetime rule. The `issued` history is set
on first allocation and is never cleared, so an identifier can never designate
a later occupant. Release atomically marks the object dead, removes its binding,
releases its frame, and removes every installed capability naming it. Access
also revalidates the live binding and allocator owner. Permanently consuming
identifiers is simple and makes stale-capability safety explicit; the required
identifier-width bound is now supplied by the
[bounded lifetime-identity issuer](lifetime-identity.md), whose composite
allocation draws the next representable 64-bit object identity from
kernel-owned state and fails closed with a typed exhaustion result instead of
wrapping. `MemoryLifecycle.allocate` remains the internal transition invoked
with exactly that issued identity. Access rejects non-memory kinds before
checking frame state.

## Evidence and scope

Machine-checked theorems establish state-preserving typed rejection, fresh
allocation ownership and exclusion of reserved frames, monotonic identifier
use, complete installed-capability retirement, and that successful access
corresponds to the current live binding and allocator owner. Executable
adversarial examples delegate read authority, release the object, reuse its
frame for a different object and owner, reject the delegated stale slot, and
reject reuse of the retired identifier.

The composition reuses `Capability.install`, `Capability.copy`,
`FrameAllocator.allocate`, and `FrameAllocator.release`; projection theorems
reuse the allocator's ownership proof. These proofs concern the Lean model.
They do not prove generated code, the compiler, runtime, boot chain, kernel
binary, hardware, concurrency, page tables, DMA, information flow, timing, or
identifier-width sufficiency. Firmware truthfulness remains a trusted input as
documented by the allocator model. This slice adds no axiom, proof escape, FFI,
or other trusted-code declaration.
