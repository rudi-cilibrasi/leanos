# Charged spawning, child control handles, and frame slices

This section defines the spawn operations a program would actually use. Spawning a child is charged against a per-parent limit on the number of children, the parent names each child by a control handle, a parent can hand a child part of its own memory allowance, and a parent can end a child. Every refusal is a typed error that leaves the whole kernel state exactly as it was.

- `childSlots_encodable` — Every slot of a parent's child table fits in a handle word.
- `list_sum_update` — Bookkeeping: changing one entry of a list of numbers without repeats changes its total by exactly that entry's change.
- `slotSum_update` — Bookkeeping: changing the value of one child-table slot changes the table's total by exactly that slot's change.
- `slotSum_congr` — Bookkeeping: two per-slot values that agree everywhere have the same total over the child table.
- `freeChildSlot_some` — The slot chosen for a new child is inside the table and empty.
- `decode_controlWord` — A child's control handle decodes back to exactly its slot and generation.
- `resolveControl_ok` — A control handle that is accepted came from a live parent and names exactly the child-table entry with its generation.
- `resolveControl_stale` — A control handle whose slot holds no entry of its generation is refused.
- `spawnCharged_shape` — A charged spawn either refuses and leaves the state unchanged, or creates a child.
- `grantFrames_shape` — A memory grant either refuses and leaves the state unchanged, or moves frames to the child.
- `terminateChild_shape` — Ending a child either refuses and leaves the state unchanged, or ends the child.
- `spawnCharged_rejected_unchanged` — A refused charged spawn leaves the kernel state exactly as it was.
- `grantFrames_rejected_unchanged` — A refused memory grant leaves the kernel state exactly as it was.
- `terminateChild_rejected_unchanged` — A refused child termination leaves the kernel state exactly as it was.
- `grantBudgetedAuthority_rejected_unchanged` — A refused grant of spawn permission leaves the kernel state exactly as it was.
- `spawnCharged_result` — A charged spawn reports either a new child or a typed refusal, nothing else.
- `grantFrames_result` — A memory grant reports either the frames moved or a typed refusal, nothing else.
- `terminateChild_result` — Ending a child reports either the ended child or a typed refusal, nothing else.
- `ChildOperation.apply_rejected_unchanged` — Every refusal by any of these spawn operations leaves the kernel state exactly as it was.
- `childGate_unchanged_of_not_running` — While the kernel is busy or halted, every one of these operations is refused with the state unchanged.
- `spawnCharged_subject_budget_exhausted` — A parent that already has as many children as its limit allows is refused with "subject budget exhausted", and nothing is created.
- `spawnCharged_control_generation_exhausted` — When the supply of control-handle numbers runs out, spawning is refused with a typed error and nothing is created.
- `grantFrames_frame_budget_exhausted` — Asking to give a child more memory frames than the parent has free is refused with "frame budget exhausted", and nothing changes.
- `spawnCharged_spawned` — An accepted charged spawn passed every check, is the ordinary spawn, and records the child in the parent's table under the returned control handle.
- `grantFrames_granted` — An accepted memory grant moved exactly the parent's first free frames to the named live child and raised the parent's recorded charge for that child.
- `terminateChild_terminated` — An accepted child termination ended exactly the named child, returned its frames, and reports how many it had.
