# The kernel states the spawn allocator describes

The spawn allocator is a small record; the kernel model is a large composite state. This file names the composite states the spawn family runs on (the parent is the running subject and holds its endpoint, its address space and up to two memory objects, its children sit in a four-slot table, and every counter stays in range) and shows how each reading the allocator makes of its record is the same reading of the kernel state.

- `sum_range_of_zero` — A stepping-stone fact: adding up a table whose entries past some position are all zero gives the same total as adding up only the positions before it.
- `abstraction_children` — The allocator's child table is read straight from the parent's first four child-table slots.
- `abstraction_childAt` — The allocator's child entry in a slot is the kernel's entry for slots inside the four-slot table and nothing past it.
- `childCount_family` — The number of children the kernel counts for the parent is the number the allocator counts.
- `subjectBudget_family` — The parent's subject budget in the kernel is the allocator's budget.
- `abstraction_childAt_lt` — Inside the four-slot table, the allocator's entry is the kernel's entry with only its generation and charge kept.
- `abstraction_childAt_family` — On these kernel states, the allocator's entry in every slot is the kernel's entry with only its generation and charge kept.
- `freeChildSlot_family` — Whenever the allocator finds a free child slot, the kernel finds the same one.
- `resolveControl_family` — Looking up a child by its control word gives the same answer in the kernel and the allocator: the same refusal, or the same slot and the same entry.
- `resolveControl_family_error` — When the allocator refuses a control word, the kernel refuses it for the same reason.
- `resolveControl_family_ok` — When the allocator accepts a control word, the kernel accepts it for the same slot and an entry with the same generation and charge.
- `abstraction_memoryAt` — The allocator's memory slots are the parent's capability slots 2 and 3, read as memory identities.
- `resolveEndpoint_parentSlots` — Looking up the endpoint handle a spawn names gives the parent's endpoint for exactly the handles the allocator accepts, and the same refusal otherwise.
- `family_notReserved` — A frame committed to any subject is never a reserved frame.
- `budgetLimit_committed` — A subject's frame limit is the number of frames committed to it.
- `budgetUsage_committed` — A subject's frame usage is the number of frames committed to it that hold memory.
- `availableFrames_committed` — A subject's available frames are the frames committed to it that are free.
- `availableFrames_length` — The number of free frames the kernel finds for the parent is the allocator's count of free frames.
- `find_isSome_filter` — A stepping-stone fact: a search finds something exactly when the matching items are not empty.
- `frameState_beq_free` — A stepping-stone fact: comparing a frame's state with "free" by equality test agrees with asking whether it is free.
- `firstAvailable_family` — The kernel finds a free frame committed to the parent exactly when the allocator says the parent has one.
- `family_parentSlots` — On these kernel states, the parent's slots are exactly as the allocator reads them, and the endpoint they hold is owned by the other subject.
- `owner_live` — Whoever owns an object on these kernel states is a live subject.
