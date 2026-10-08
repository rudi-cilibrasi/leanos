# Publishing subsystem changes to the whole kernel state

This file defines how each kind of kernel operation publishes its result to every part of the composite state that mirrors it, and the exact state each public operation produces. Its theorems describe the composite scheduler wrappers, which can only admit programs whose saved snapshot is staged, and bookkeeping facts about the publication steps.

- `schedulerDispatch_rejected_unchanged` — A rejected scheduler pick-next leaves the scheduler exactly as it was.
- `schedulerDispatch_accepted_none_unchanged` — A pick-next that finds no one to run is a genuine no-op: the scheduler is unchanged.
- `schedulerDispatch_accepted_is_none` — The bare scheduler pick-next can never actually hand out a program: any accepted result is empty, because switching to a program must go through the path that consumes its saved snapshot.
- `schedulerYield_rejected_unchanged` — A rejected yield leaves the scheduler exactly as it was.
- `schedulerYield_ne_accepted` — The bare yield can never succeed at this boundary: a voluntary yield must carry a saved snapshot and go through the resumable-switch path instead.
- `schedulerTick_rejected_unchanged` — A rejected timer tick leaves the scheduler exactly as it was.
- `schedulerTick_ne_accepted` — The bare timer tick likewise can never succeed here, for the same missing-snapshot reason.
- `schedulerAdmission_rejected_unchanged` — A rejected admission of a program to the ready queue leaves the scheduler exactly as it was.
- `schedulerAdmission_accepted_exact` — An accepted admission proves the program had no undrained cancellation, matches the raw scheduler's own add exactly, and shows a staged snapshot for that program already sat in the bank.
- `schedulerAdmission_eq_add_of_staged` — Whenever a snapshot for the program is already staged and no cancellation is pending, the composite admission behaves exactly like the plain scheduler add.
- `installScheduler_scheduler` — Bookkeeping: installing a scheduler keeps its queue and capacity exactly; only the shared lifecycle records are republished.
- `installScheduler_preemption_scheduler` — Bookkeeping: the legacy preemption view sees the very scheduler that was installed.
- `installScheduler_lifecycle` — Bookkeeping: installation makes the scheduler's program-lifecycle records the single authoritative copy.
- `installScheduler_synchronizes_consumers` — Scheduler publication is one synchronized step: execution, preemption, and snapshot-bank consumers all observe exactly the installed scheduler and its queue.
- `installTerminatedSubject_deferred_self` — Bookkeeping: after publishing a program's termination, no deferred cancellation remains recorded for the dead program.
- `installLifecycle_coherent` — Publishing a lifecycle change leaves every subsystem reading from the same single set of records; dead objects keep no mailboxes and no message from a dead sender survives.
- `installVirtualMemory_preserves_runtimeWellFormed` — A stepping-stone fact used by later theorems: publishing a mapping-only memory change preserves the whole runtime invariant whenever the memory registry and owners are untouched and the translation cache stays coherent.
- `installVirtualMemory_preserves_blockingRuntimeWellFormed` — Mapping publication changes only the mapping table inside the shared records, so the waiting-store invariant carries across the very same step as the memory proof.
- `installLifecycle_clears_retired_mailbox` — After a lifecycle publication, an object that is no longer registered has no mailbox contents.
- `installLifecycle_clears_dead_sender` — After a lifecycle publication, no mailbox can hold a message from a sender who is no longer alive.
- `installLifecycle_releases_retired_memory` — When a lifecycle publication retires a program's memory object, its binding is dropped and its physical memory frame returns to the free pool in the same step.
- `syscallContext_caller` — Spelling out the definition: the identity attached to a system call is the current program per the execution latch, never a caller-supplied value.
- `syscallContext_addressSpace` — Spelling out the definition: the memory space attached to a system call is the active one per the execution latch.
- `ipcContext_caller` — Spelling out the definition: the identity attached to a message operation is the current program per the execution latch.
- `ipcContext_addressSpace` — Spelling out the definition: the memory space attached to a message operation is the active one per the execution latch.
