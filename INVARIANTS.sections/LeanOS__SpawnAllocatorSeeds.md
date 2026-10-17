# The spawn family's starting states are states the allocator describes

The spawn family starts from fixed kernel states (the main starting state and three variants with one counter used up). This file shows that each of them is a state the allocator describes, so every sequence of commands the allocator decides from there behaves in the kernel exactly as the allocator says. It also writes out the allocator record of each starting state, which does not depend on the boot plan.

- `seed_subjects` — In the starting states, subjects 1 and 2 are the live subjects.
- `seed_objects` — In the starting states, objects 1, 2, 10 and 20 are the live objects.
- `seed_ownedMemory` — In the starting states, only memory object 20 is owned, by subject 2 on frame 4.
- `seed_endpointOwner` — In the starting states, only endpoint 10 is owned, by subject 1.
- `seed_commitment` — In the starting states, only frame 4 is committed, to subject 2.
- `seed_status_four` — In the starting states, frame 4 holds memory object 20.
- `seed_memory_slot` — In the starting states, the parent's slot 2 holds memory object 20 with every right.
- `seed_abstraction_memory` — The starting states' record has memory in slot 2 and none in slot 3.
- `seed_budgetLimit` — In the starting states, the parent may hold one frame.
- `seed_budgetUsage` — In the starting states, the parent's one frame holds memory.
- `familySeed_family` — Every starting state whose counters are in range and whose spawn registry is empty is a state the allocator describes.
- `seedState_family` — The four starting states of the spawn family are states the allocator describes.
- `seed_trace_simulates` — From each starting state, every sequence of commands the allocator decides gives the allocator's replies and ends in a state whose record is the allocator's.
- `abstraction_seedState` — The record of each starting state, written out; it does not depend on the boot plan.
