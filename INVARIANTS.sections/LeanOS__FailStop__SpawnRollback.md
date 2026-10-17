# Undoing a spawn puts everything back

This section is about what happens when a parent creates a child, gives it some memory frames, and then the child is ended because loading it failed. It shows that ending the child puts back everything the system tracks about authority and resources: who is alive, every permission every subject holds, which subjects can run, who owns what, which frames belong to whom, the memory allocator, the frames' contents, and the parents' child tables. The only things that stay changed are counters that never go backwards, so the child's identity and its control number are never reused.

- `copy_subjects` — Copying a permission never changes which subjects are alive or which objects exist.
- `spawn_lifecycle_records` — Creating a child records only its new address space as owned by it; it changes no memory or endpoint ownership, marks only the child alive, and the new address space was not alive or issued before.
- `spawn_execution` — Creating a child keeps the machine running and keeps the same parent as the current subject.
- `spawn_addressSpace_record` — Creating a child records exactly the child's new address space and changes no other record.
- `terminatedChild_registry` — Ending a child removes exactly the child, its permissions and everything it owned from the permission and ownership records, and stops it from being runnable or current.
- `GrantedFrom.refl` — Right after the child is created, the state has the shape "created, then given frames" with no frames given yet.
- `GrantedFrom.grant` — Giving the child more frames keeps that shape: only the child's table entry and frames taken from the parent's free frames change.
- `GrantedFrom.same` — In that shape, everything except the child's table entry and the frame ownership is exactly as right after creation.
- `GrantedFrom.grantAll` — The shape survives any number of frame gifts with the child's control number.
- `grantAll_preserves` — Any number of frame gifts keeps the system's safety rules and its child bookkeeping rules.
- `spawn_rollback_restores` — Creating a child, giving it frames any number of times, and then ending it with its control number succeeds and puts back every authority and resource record the system had before the child was created; only the never-reused counters have moved on.
- `spawn_grants_child` — After creating a child and giving it frames, the machine is still running, the permission records are exactly those creation left, the safety rules hold, and the child's control number still names that child.
