# Bounded user-memory copies

`LeanOS.UserCopy` is a total, sequential model for copying at most 16 bytes
between one caller's active user address space and a typed kernel buffer. The
caller and active address space come only from `TrustedContext`; neither is
selected by a user address or length. Kernel buffers use `BufferId` and byte
offsets and are not user-addressable pointers.

Before changing either memory domain, `validate` checks the bound, 64-bit
addition, the lower-canonical range, and every byte's current virtual mapping.
It uses `VirtualMapping.translate`, requiring read permission for
`copyFromUser` and write permission for `copyToUser`. Translation rechecks the
live object-to-frame binding and allocator ownership. Consequently an
unmapped or read-only second page, a retired object, or a frame reused after
release rejects the entire operation without a partial update.

Virtual aliases remain valid mappings, but a copy range that traverses two
virtual pages resolving to the same physical frame is rejected. This conservative
policy makes accepted copy-to writes independent of aliasing. Zero-length
copies dereference no address and accept any start value.

Lean proves that successful validation returns exactly the requested number of
locations and that each came from the selected caller-owned address space with
the requested permission. Rejection preserves the complete state. Copy-from
never changes user bytes, copy-to never changes kernel bytes, and a copy-to
helper theorem proves every physical byte outside the validated locations is
unchanged. Together with `VirtualMapping`'s current-frame, authority, stale
lifetime, and cross-subject theorems, these establish the modeled confinement
boundary. Executable traces cover zero and maximum bounds, overflow,
non-canonical input, a page crossing, an unmapped second page, a read-only
destination, alias rejection, stale reuse, and a round trip.

These are model-level proofs, not proofs of assembly loops, page-table hardware,
concurrent mutation, generated code, QEMU, or a kernel binary. The trusted
context must be established by protected entry code. This model adds no axiom,
proof escape, unsafe/extern declaration, FFI, or new TCB implementation.
