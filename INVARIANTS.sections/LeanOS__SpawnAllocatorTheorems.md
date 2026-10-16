# What the spawn allocator guarantees for every record

These guarantees hold for every allocator record and every command, not only for a list of example states: frames are neither created nor lost, the representation and its invariants are kept, retired child handles stay retired, a spawn records exactly one child, commands about one child touch only that child, and each exhausted counter is a typed rejection.

- `step_accepted` — Every accepted command is exactly one of the allocator's accepted cases, with everything that case checked.
- `step_cases` — Every command either is rejected with the record unchanged or is one of the accepted cases.
- `spawned_chargeSum` — An accepted spawn charges no frames: the total charged to children is unchanged.
- `granted_chargeSum` — An accepted grant of some frames raises the total charged to children by exactly that many.
- `terminated_chargeSum` — An accepted termination lowers the total charged to children by exactly the ended child's charge.
- `available_le` — The parent's free frames never exceed its frames.
- `step_frames_conserved` — Accounting: no command creates or destroys a frame of the parent's family; a grant moves frames to a child and a termination moves them back.
- `identityExhausted_false` — A subject or object counter that is not exhausted has a successor that still fits in a 64-bit word.
- `capabilityExhausted_false` — A capability counter that is not exhausted is positive and below the reserved generation.
- `controlAvailable_true` — An available control generation is positive and below the reserved generation.
- `generationReserved_lt` — Bookkeeping: the reserved generation plus two still fits in a 64-bit word.
- `mem_set_cases` — A stepping-stone fact: an item of a list with one position replaced was in the old list or is the new item.
- `memoryAt_none_index` — An empty parent memory slot is an empty position of the record's memory table.
- `spawned_valid` — An accepted spawn keeps the allocator's representation and invariants: counters fit, the new generation is valid, the children stay within the budget, and every recorded generation was issued.
- `granted_valid` — An accepted frame grant keeps the allocator's representation and invariants, including the parent's memory within its remaining frames.
- `terminated_valid` — An accepted termination keeps the allocator's representation and invariants.
- `allocated_valid` — An accepted memory allocation keeps the allocator's representation and invariants, including memory within the parent's frames.
- `released_valid` — An accepted memory release keeps the allocator's representation and invariants.
- `step_valid` — Every command, accepted or rejected, keeps the allocator's representation and invariants: the record stays encodable, memory stays within the parent's frames, children stay within the subject budget, and every recorded generation was issued.
- `retired_resolve` — A retired control word names no child.
- `retired_rejected` — Stale handles: giving frames to or ending a child through a retired control word is rejected with the record unchanged.
- `step_controlNext_mono` — The control-generation counter never goes backwards.
- `step_retired_forever` — Stale handles: once a control word is retired it stays retired after any later command, so a reused child slot never accepts an old word.
- `terminate_retires` — Ending a child retires the control word that named it.
- `spawn_exact` — Inheritance exactness at the allocator: an accepted spawn records exactly one new child, in the first free slot, with no frames and the fresh generation, returns its control word, advances the four counters by exactly one, one, two and one, and changes nothing else.
- `step_confined` — Confinement at the allocator: giving frames to or ending a child changes only that child's entry and the parent's frames, and memory and kernel commands change no child entry.
- `spawn_budget_exhausted` — From any record, a spawn by a parent already at its subject budget is rejected as subject-budget exhaustion with nothing changed.
- `spawn_controls_exhausted` — From any record, a spawn when control generations are used up is rejected as such with nothing changed.
- `spawn_subjects_exhausted` — From any record, a spawn when subject identities are used up is rejected as such with nothing changed.
- `spawn_objects_exhausted` — From any record, a spawn when object identities are used up is rejected as address-space exhaustion with nothing changed.
- `spawn_capabilities_exhausted` — From any record, a spawn when capability identities are used up is rejected as such with nothing changed.
- `grant_frames_exhausted` — From any record, a grant of more frames than the parent has free is rejected as frame-budget exhaustion with nothing changed.
- `allocate_capabilities_exhausted` — From any record, a memory allocation when capability identities are used up is rejected as such with nothing changed.
- `allocate_objects_exhausted` — From any record, a memory allocation when object identities are used up is rejected as such with nothing changed.
- `allocate_frames_exhausted` — From any record, a memory allocation when the parent has no free frame is rejected as frame-budget exhaustion with nothing changed.
