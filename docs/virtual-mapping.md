# Capability-bounded virtual mappings

`LeanOS.VirtualMapping` is a small executable, sequential virtual-memory model
composed with `LeanOS.MemoryLifecycle`. An address space is a typed kernel
object with one explicitly modeled subject owner. `createAddressSpace` accepts
only a valid subject, empty capability slot, and never-issued identifier. It
atomically records that identifier in the shared monotonic object history,
installs a live address-space object and root grant/revoke capability,
establishes the owner, and clears every page in the new space. The shared
history prevents a retired address-space identifier from later becoming either
another address space or a memory object.

The owner relation is the explicit, nondelegable authority to map, unmap, and
translate. The root capability is separately required to destroy the space;
copying it does not transfer ownership. `destroyAddressSpace` therefore accepts
only the owner presenting a live address-space capability with revoke rights.
It atomically retires the typed object and every capability naming it, removes
the owner, and clears every mapping in that address space. Other address-space
owners and mappings are unchanged. Subject termination, ownership transfer,
and recursive revocation are outside this slice.

Mapping takes a capability slot and a nonempty read/write permission set. It
rejects permissions outside that capability, occupied pages, invalid ownership,
kind mismatches, and stale lifetime or allocator state. Only live memory
objects can supply mappings. Translation selects exactly one address space and
virtual page, checks its permission, then revalidates the object's current
binding and physical-frame owner. Rejection is typed and leaves the complete
composite state unchanged.

The release wrapper selectively invalidates every mapping whose object is the
retired memory object and preserves every mapping naming a different object,
including mappings in unrelated address spaces. Consequently, releasing one
object and reusing its frame cannot make an old virtual page reach the new
occupant, while authorized mappings of other live objects remain unchanged.

Machine-checked theorems establish mapping and unmapping invariant preservation,
state-preserving rejection for every operation, fresh empty creation with root
authority, complete destruction cleanup, preservation of other address spaces,
selective memory-release cleanup, pre-state capability provenance for accepted
map permissions, current-authority and current-frame translation,
selected-address-space confinement, and cross-subject exclusion. Executable
traces cover create/map/destroy, stale identifier reuse, independent spaces,
unauthorized and repeated destroy, selective release, and stale translation
after frame reuse.

These are properties of the Lean model, not hardware page tables, a TLB, page
faults, concurrency, generated code, a kernel binary, or full information-flow
noninterference. Compilation and examples are test evidence; only the stated
Lean theorems are proofs. This slice adds no axiom, proof escape, FFI, unsafe
declaration, or trusted-computing-base assumption.
