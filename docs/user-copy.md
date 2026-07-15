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

Lean proves that successful validation cannot wrap its range, remains within
the modeled canonical bound, returns exactly the requested number of locations,
and resolves each location through the selected caller-owned address space with
the requested permission. Rejection preserves the complete state. Accepted
copies install exactly the prevalidated source values; operation-level footprint
theorems show that copy-from changes no other buffer or out-of-range offset and
copy-to changes no physical byte outside its validated locations. Copy-from
never changes user bytes and copy-to never changes kernel bytes. Explicit
cross-subject rejection theorems connect complete prevalidation to
`VirtualMapping`'s owner confinement. Executable traces cover zero and maximum
bounds, overflow, non-canonical input, exact first and last bytes across a page
boundary, atomic failure on an unmapped second page, a read-only destination,
alias rejection, stale reuse, and a round trip.

These are model-level proofs, not proofs of assembly loops, page-table hardware,
concurrent mutation, generated code, QEMU, or a kernel binary. The trusted
context must be established by protected entry code. This model adds no axiom,
proof escape, unsafe/extern declaration, FFI, or new TCB implementation.
