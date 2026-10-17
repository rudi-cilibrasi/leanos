# Allocating and releasing memory in the kernel is the allocator's

The parent can allocate a memory object on one of its free frames into slot 2 or 3 and release it again. This file shows that on every kernel state the allocator describes, the kernel's allocation and release return the allocator's status, their results are the allocator's next records, and they leave states the allocator still describes.

- `family_memoryActor` — On these kernel states, the subject that allocates and releases memory is the allocator's parent.
- `family_low_slots` — The parent's slots 0 and 1 are always occupied.
- `family_memory_slot` — The parent's slot 2 or 3 holds something exactly when the allocator records memory there.
- `allocateMemory_status_family` — A memory allocation by the parent on these kernel states returns the allocator's status.
- `releaseMemory_status_family` — A memory release by the parent on these kernel states returns the allocator's status.
- `countP_flip` — A stepping-stone fact: switching one item of a list without repeats from not counted to counted, and nothing else, raises the count by one.
- `allocateMemory_accepted` — An accepted allocation on these kernel states uses the next object identity and the first free frame committed to the parent.
- `allocatedState_fields` — After an allocation, the new object is the parent's on its frame, the object counter advances by one, and nothing else the allocator reads changes.
- `memory_list_update` — The allocator's memory table after one parent memory slot changes is the old table with that one position replaced.
- `allocateMemory_abstraction` — After an accepted allocation, the kernel state's record is the allocator's next record.
- `family_memoryGate_invariants` — Every memory operation on these kernel states keeps the kernel's resource, child-accounting and spawn-tree invariants.
- `allocateMemory_family_preserved` — An accepted allocation leaves a kernel state the allocator still describes.
- `family_frame_member` — Every frame committed to some subject is one of the allocator's frames.
- `family_kind_object_ne` — Two of the parent's capabilities of different kinds name different objects.
- `releaseMemory_accepted` — An accepted release on these kernel states releases exactly the memory object in the named slot and its frame.
- `releasedState_fields` — After a release, the object is retired, its frame is free and unowned, its binding is gone, and nothing else the allocator reads changes.
- `releasedOwnership_sub` — Releasing memory only removes ownership records.
- `releasedOwnership_keep` — Releasing memory keeps the ownership records of other objects on other frames.
- `releaseMemory_abstraction` — After an accepted release, the kernel state's record is the allocator's next record.
- `releaseMemory_family_preserved` — An accepted release leaves a kernel state the allocator still describes.
