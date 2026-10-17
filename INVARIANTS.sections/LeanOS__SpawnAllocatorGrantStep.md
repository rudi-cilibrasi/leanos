# Giving frames to a child in the kernel is the allocator's grant

A frame grant moves free frames committed to the parent over to one child. This file shows that on every kernel state the allocator describes, the kernel's grant returns the allocator's status and frame count, its result is the allocator's next record, and it leaves a state the allocator still describes.

- `countP_contains_nodup` — A stepping-stone fact: counting how many items of a list without repeats belong to a smaller list without repeats inside it gives the smaller list's length.
- `grantedFrames_facts` — The frames the kernel picks for a grant are distinct, all free and committed to the parent, and there are as many as asked for, or as many as are free.
- `movedCount_family` — The number of frames the kernel moves is the smaller of the request and the allocator's count of free frames.
- `resolved_entry` — The child a resolved control word names is in the parent's table, is live, and has exactly its charge in frames.
- `grantFrames_status_family` — A frame grant on these kernel states returns the allocator's status and value.
- `grantFrames_accepted` — An accepted grant on these kernel states moves exactly the requested free frames to the named child and charges them to its entry.
- `setChildEntry_children` — Rewriting one entry of a child table changes only that entry.
- `grantFrames_abstraction` — After an accepted grant, the kernel state's record is the allocator's next record.
- `usage_moveFree` — Moving free frames away from the parent does not change how many of its frames hold memory.
- `grantFrames_family_preserved` — An accepted grant leaves a kernel state the allocator still describes.
