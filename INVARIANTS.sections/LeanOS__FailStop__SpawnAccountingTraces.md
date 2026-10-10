# Whole runs of charged spawning

This section extends the whole-run resource result to runs that mix every kernel step with charged spawning, memory grants to children, child termination, and memory allocation and release. Along any such run all three rulebooks hold at the end, no identity is created twice, no memory frame is created, no child has children, no parent exceeds its child limit or its memory entitlement, and a stopped control handle stays stopped.

- `ChildStepKeeps.trans` — Bookkeeping: the guarantees kept by one step and by the next combine into guarantees for both steps together.
- `ChildStepKeeps.refl` — Bookkeeping: a state that does not change keeps every guarantee.
- `ChildStepKeeps.of_children` — A step that changes only spawn permissions keeps every guarantee.
- `CompositeStep.keeps` — Every ordinary kernel step keeps the frames, the commitments, the identity history, the child tables, and every top-level parent's entitlement.
- `spawnCharged_charged` — After a charged spawn, every child in a table was either already there or is the brand-new child.
- `ChildOperation.apply_keeps` — Every spawn operation keeps the frames, never creates a frame commitment, only adds to the identity history, only adds fresh handle numbers, and never raises a top-level parent's entitlement.
- `childGate_keeps` — The same holds through the kernel's gate, including when it is busy or halted.
- `memoryGate_entitlement` — A memory operation never changes anyone's memory entitlement.
- `memoryGate_childAccounting` — Every memory operation keeps the spawn accounting rulebook.
- `memoryGate_childKeeps` — Every memory operation keeps the frame list, the commitments, the identity history, the child tables, and every top-level parent's entitlement.
- `ChildTraceStep.admissible_preserves` — Every step of such a run, under its stated condition, keeps all three rulebooks and all the guarantees.
- `ChildTraceStep.created_fresh` — An identity a step creates, including a spawned child, was not issued before that step and is issued after it.
- `runChildSteps_admissible` — Along a whole run, all three rulebooks hold at the end and all the guarantees hold between the start and the end.
- `createdAlongChild_fresh` — Along a whole run, no identity is created twice, and each created identity was not issued at the start and is issued at the end.
- `child_resource_trace` — Main result: along every run of kernel steps, charged spawn operations, and memory allocation and release, all three rulebooks hold at the end, no identity is reused, no frame is created, every subject's usage fits its budget, no child has children, no parent has more children than allowed, every parent's memory use plus its children's allowances fit its entitlement, a top-level parent never gains memory, and a stopped control handle stays stopped.
- `bootRuntime_childAccounting` — The kernel state right after boot satisfies all three rulebooks, so the whole-run result applies from boot.
- `runChildSteps_composite` — Runs without spawn operations are a special case: they behave exactly as the earlier whole-run result describes.
- `stale_control_after_respawn` — Spawn a child, end it, spawn again into the same slot: the old control handle is refused for both operations and the state is unchanged.
