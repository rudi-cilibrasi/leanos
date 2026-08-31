# Physical memory lifetimes and access tickets

These theorems cover the model in which the kernel hands out physical memory frames to numbered objects and controls all access through capabilities — unforgeable permission tickets that programs hold in numbered slots. Together they guarantee that an object identifier is used at most once ever, that releasing a memory object cleanly destroys every ticket that could reach it, and that a stale ticket kept from before a release can never touch whatever occupies the same memory frame afterwards.

- `allocate_rejected_unchanged` — Whenever the kernel refuses a memory allocation, for any reason, the whole system state is left exactly as it was.
- `release_rejected_unchanged` — Whenever the kernel refuses a release request, for any reason, the whole system state is left exactly as it was.
- `allocated_binding` — Whenever an allocation succeeds, the newly created object is bound to a real memory frame, and the frame allocator records that frame as owned by exactly that object.
- `allocated_not_reserved` — The memory frame handed to a newly allocated object is never one of the frames the kernel keeps reserved for itself.
- `allocation_requires_unissued` — An allocation can only succeed for an object identifier that has never been issued before.
- `issued_identifier_never_reallocated` — Once an object identifier has been issued, no allocation request can ever succeed with that identifier again.
- `allocated_root_capability` — A successful allocation installs, in exactly the requested slot of the requesting program, a full-power ticket naming exactly the new object and nothing else.
- `allocated_owner_exclusive` — After a successful allocation, the frame bound to the new object has exactly one owner: that object.
- `release_preserves_issued` — Releasing memory never erases the record of which identifiers have been issued; that history only ever grows.
- `release_invalidates` — A successful release wipes the retired object out completely: its frame binding is gone, it is no longer live, and no program anywhere is left holding a ticket that names it.
- `authorized_current_binding` — Whenever the kernel authorizes an access, the ticket used necessarily names the object currently bound to and owning that frame, so a leftover ticket for a frame's past occupant can never authorize access to a later one.
