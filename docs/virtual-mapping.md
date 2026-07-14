# Capability-bounded virtual mappings

`LeanOS.VirtualMapping` is a small executable, sequential virtual-memory model
composed with `LeanOS.MemoryLifecycle`. An address space has one explicitly
modeled subject owner. Only that owner may map, unmap, or translate its pages;
sharing requires a separate mapping in an address space owned by the other
subject.

Mapping takes a capability slot and a nonempty read/write permission set. It
rejects permissions outside that capability, occupied pages, invalid ownership,
kind mismatches, and stale lifetime or allocator state. Only live memory
objects can supply mappings; address-space objects share the registry without
a frame obligation. Translation selects exactly one address
space and virtual page, checks its permission, then revalidates the object's
current binding and physical-frame owner. Rejection is typed and leaves the
complete composite state unchanged.

The release wrapper conservatively invalidates all mappings after a successful
object release. This is stronger than selectively invalidating the retired
object, but deliberately keeps the first policy executable and unambiguous.
Consequently, releasing object 10 and reusing its frame for object 11 cannot
make an old virtual page reach the new occupant. Callers may reconstruct still
authorized mappings after release.

Machine-checked theorems establish mapping, unmapping, and release invariant
preservation, state-preserving rejection, pre-state capability provenance for
accepted map permissions, current-authority and current-frame translation,
selected-address-space confinement, and cross-subject exclusion. Executable
examples cover read-only success, a write request denied by a read-only
capability, occupied pages, cross-address-space mutation and access, unmap, and
an actual release/frame-reuse trace whose stale translation remains unusable.

These are properties of the Lean model, not hardware page tables, a TLB, page
faults, concurrency, generated code, a kernel binary, or full information-flow
noninterference. Compilation and examples are test evidence; only the stated
Lean theorems are proofs. This slice adds no axiom, proof escape, FFI, unsafe
declaration, or trusted-computing-base assumption.
