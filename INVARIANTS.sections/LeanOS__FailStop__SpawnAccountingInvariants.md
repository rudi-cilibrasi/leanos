# The spawn accounting rulebook

This section states the accounting rules for parents and children and proves that every step keeps them. Each child-table entry names a real child, children never appear twice, a child's memory plus what it handed to its own children stays within what its parent charged for it, and no parent has more children than its spawn permission allows. Handing memory to a child only moves frames the parent already had; ending a child moves them back.

- `budgetLimit_countP` — Bookkeeping: a subject's memory allowance is the number of frames committed to it.
- `countP_move` — Moving frames from a parent to a child lowers the parent's count and raises the child's by exactly the number moved, and changes nobody else's.
- `countP_return` — Giving all of a child's frames back to its parent raises the parent's count by exactly the child's count, leaves the child with none, and changes nobody else's.
- `childTable_update` — Changing one child-table slot changes that parent's child count and total charge by exactly that slot's change, and no other parent's.
- `childTable_congr` — Two states with the same child tables have the same child counts and charges.
- `slotSum_mono` — Bookkeeping: a per-slot value that is everywhere smaller has a smaller total over the child table.
- `list_sum_zero` — Bookkeeping: adding up zeros gives zero.
- `slotSum_zero` — Bookkeeping: a table of zeros adds up to zero.
- `childAccounting_of_empty` — A kernel with empty child tables satisfies the accounting rules.
- `usage_add_childLimits_le` — A parent's own memory use plus the memory allowances of all its children never exceed the parent's total entitlement.
- `frameBudgets_unsupported` — None of the core kernel rules reads the frame-commitment table.
- `withFrameBudgets_resourceRuntimeWellFormed` — Replacing the frame-commitment table keeps the full rulebook, as long as every committed frame is a real, unreserved frame given to a subject that has existed.
- `spawnAuthorize_live` — A parent allowed to spawn is alive and holds a spawn permission.
- `live_issued` — A live subject has an issued identity.
- `subjectBudget_of_authority` — A parent's child limit is the one carried by the spawn permission it holds.
- `spawn_childTable` — The basic spawn step leaves the child tables, the control-handle counter, and the spawn permissions unchanged.
- `spawn_budgetLimit` — The basic spawn step leaves every subject's memory allowance unchanged.
- `childCharge_empty` — A parent with an empty child table has charged nothing to children.
- `CompositeStep.apply_spawn` — No ordinary kernel step touches the spawn records.
- `childAccounting_of_kept` — A step that leaves the spawn records, frame commitments, and frames alone, and only adds subjects, keeps the accounting rules and every entitlement.
- `CompositeStep.childAccounting` — Every ordinary kernel step keeps the accounting rules and every subject's entitlement.
- `spawnCharged_preserves` — A charged spawn keeps the full rulebook and the accounting rules and changes nobody's entitlement.
- `mem_availableFrames` — A frame offered to a child is a real frame, committed to the parent, and not in use.
- `grantFrames_limits` — Handing frames to a child lowers the parent's allowance and raises the child's by exactly the number moved, and leaves everyone else's alone: no frame is created.
- `grantFrames_preserves` — A memory grant keeps the full rulebook and the accounting rules, and only the receiving child's entitlement can grow.
- `reclaimable_facts` — A frame marked for reclaiming is committed to the child and backs a dead object.
- `not_reclaimable_of_live` — A frame that backs a live object is never reclaimed.
- `reclaimChildFrames_preserves` — Reclaiming an ended child's memory keeps both rulebooks.
- `reclaimChildFrames_reclaims` — Reclaiming frees, unbinds and wipes every frame of the child that backs a dead object, and keeps the commitments and the frame list.
- `releaseChild_limits` — Ending a child gives all its frames back to the parent: the parent's allowance grows by the child's, the child's drops to zero, and nobody else's changes.
- `terminatedChild_facts` — Ending a child through the kernel's normal termination keeps the full rulebook, the identity and frame records, and the spawn records.
- `terminateChild_preserves` — Ending a child keeps the full rulebook and the accounting rules, and no subject other than an existing child gains entitlement.
- `grantBudgetedAuthority_preserves` — Granting spawn permission with a child limit keeps both rulebooks, because the grant is refused when the subject already has more children.
- `revokeSpawnAuthority_preserves` — Withdrawing spawn permission keeps both rulebooks.
- `childGate_preserves` — Every one of the spawn operations keeps the full rulebook and the accounting rules, and only a child receiving memory can gain entitlement.
