# Publishing a newly allocated memory object

This section adds the kernel step that publishes one newly allocated memory object to every copy of the kernel state at once: the new capability, the frame's owner, the object's record, and the lifecycle's ownership record. It proves that publishing it keeps the whole kernel rulebook.

- `allocatedCapabilities_subjects` — Allocating memory does not change which subjects are alive.
- `allocatedCapabilities_slotCapacity` — Allocating memory does not change how many capability slots any subject has.
- `allocatedCapabilities_nextIdentity` — Allocating memory uses exactly one new capability number.
- `allocatedCapabilities_objects` — After allocating, the new object is alive and every other object is as alive as before.
- `allocatedCapabilities_kinds` — After allocating, the new object is memory and every other object keeps its kind.
- `allocatedCapabilities_slots` — After allocating, the chosen slot holds the new memory capability and every other slot is unchanged.
- `allocatedCapabilities_derivations` — After allocating, the new capability number is recorded as a fresh root for the new memory, and every other record is unchanged.
- `allocatedCapabilities_objects_mono` — Allocating never kills a live object.
- `allocatedCapabilities_slots_mono` — Allocating into an empty slot keeps every capability that was already held.
- `allocatedCapabilities_authority_mono` — Allocating never takes away any authority a subject already had.
- `allocatedCapabilities_kinds_of_ne` — Allocating does not change the kind of any other object.
- `allocatedCapabilities_objects_of_ne` — Allocating does not change whether any other object is alive.
- `allocatedCapabilities_derivations_of_lt` — Allocating keeps every older capability record.
- `allocatedCapabilities_wellFormed` — Installing the root capability of a dead object into an empty, valid slot of a live subject keeps the capability rulebook.
- `installAllocatedMemory_mode` — Publishing an allocation does not change whether the kernel is running, busy, or halted.
- `installAllocatedMemory_capabilities` — After publishing an allocation, the kernel capability table is the one with the new memory capability.
- `installAllocatedMemory_owned` — After publishing an allocation, the new object is bound to its frame, the frame is owned by the object, the lifecycle records the owner, and the object is recorded as issued.
- `installAllocatedMemory_preserves_runtimeWellFormed` — Publishing an allocation keeps the whole kernel runtime rulebook.
- `installAllocatedMemory_preserves_authoritativeRuntimeWellFormed` — Publishing an allocation keeps the full kernel rulebook, including the blocking, waiting, and invalidation parts.
