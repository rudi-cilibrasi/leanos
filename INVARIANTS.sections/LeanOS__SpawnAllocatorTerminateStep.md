# Ending a child in the kernel is the allocator's termination

Ending a child retires the subject, revokes everything it held or owned, frees its control-table slot and returns its frames to the parent. This file shows that on every kernel state the allocator describes, the kernel's termination returns the allocator's status and returned-frame count, its result is the allocator's next record, and it leaves a state the allocator still describes.

- `terminatedChild_family` — Ending a live child keeps the kernel running with the parent current, retires the child's subject, and leaves the frame commitments, the object counter and the parent's other records as they were.
- `child_not_owner` — A child in the parent's table owns nothing that the parent's slots name.
- `terminated_parentSlots` — The parent's slots are unchanged by ending one of its children.
- `reclaim_noop` — Reclaiming a child's frames changes nothing when every frame committed to it is free.
- `terminateChild_status_family` — Ending a child on these kernel states returns the allocator's status and value.
- `terminate_post` — After ending a child, every part of the kernel state the allocator and its invariant read has the expected value: the child's slot empty, the child dead, its frames returned to the parent, and everything else as before.
- `usage_returned` — Returning a child's free frames to the parent does not change how many of the parent's frames hold memory.
- `terminateChild_accepted` — An accepted termination on these kernel states ends exactly the child the control word names, and the allocator ends the same entry.
- `terminateChild_abstraction` — After an accepted termination, the kernel state's record is the allocator's next record.
- `terminateChild_family_preserved` — An accepted termination leaves a kernel state the allocator still describes.
