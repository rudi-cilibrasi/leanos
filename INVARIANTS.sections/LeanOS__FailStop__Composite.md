# One authoritative kernel state and its runtime invariant

Every moving part of the kernel, from programs and scheduling to memory, messages, devices, and saved program snapshots, lives in one composite state under the fail-stop latch. This file names each part of that state for the footprint vocabulary, defines the single global "runtime invariant" that says all of those views agree, and builds the state the kernel starts from at boot.

- `CompositeState.frames_of_eq` — A composite-state step that changes nothing satisfies every typed footprint frame obligation.
- `CompositeState.frames_trans` — Typed composite frame obligations compose across sequential steps without erasing any projection's native state type.
- `blockingIPC_wellFormed_replaceScheduler` — A stepping-stone fact used by later theorems: swapping a new scheduler view under the message-waiting store keeps that store consistent, provided the new scheduler is itself consistent and agrees on every field the waiting checks look at.
- `blockingIPCContext_wellFormed_replaceScheduler` — A stepping-stone fact: the same scheduler swap also keeps the combined waiting-store-plus-saved-snapshots record consistent.
- `selectLiveReturnAuthority_armed_implies_live` — Return permission can end up armed only if the compiled page-table plan actually matches the live memory mappings; a stale plan can never arm it.
- `selectLiveReturnAuthority_eq_execution_update` — Spelling out the definition: live return-policy selection only ever touches the execution portion of the composite state.
- `selectLiveReturnAuthority_core` — Bookkeeping: live return-policy selection leaves the kernel's core interrupt state untouched.
- `selectLiveReturnAuthority_mode` — Bookkeeping: live return-policy selection never changes the running, busy, or halted mode.
- `selectLiveReturnAuthority_execution_returnPlan` — Bookkeeping: live return-policy selection never changes the installed page-table plan.
- `selectLiveReturnAuthority_execution_returnAddressSpace` — Bookkeeping: live return-policy selection never changes the stored program memory views.
- `selectLiveReturnAuthority_returnPlanLive` — Bookkeeping: live return-policy selection never changes whether the plan matches the live mappings.
- `selectLiveReturnAuthority_execution_wellFormed` — Live return-policy selection preserves the kernel's core consistency check whichever way the liveness test goes.
- `CompositeState.DMAQuarantined.quarantine` — Whenever the kernel's current device observation equals the boot-approved snapshot, that snapshot really does pass the quarantine test that keeps every device locked out of memory.
- `RuntimeWellFormed.blockingLifecycle` — Under the global runtime invariant, the message-waiting store sees the very same program-lifecycle records as every other part of the kernel.
- `RuntimeWellFormed.blockingScheduler` — Under the global runtime invariant, the message-waiting store uses the kernel's one authoritative scheduler itself, not a lookalike copy that happens to agree.
- `RuntimeWellFormed.directPortControls` — The global runtime invariant retains the boot-validated rule that user programs are denied all direct access to hardware ports.
- `RuntimeWellFormed.dmaQuarantined` — The global runtime invariant includes the exact boot-approved device-control observation, so device quarantine is part of the one invariant rather than a separate parallel claim.
- `bootRuntime_runtimeWellFormed` — Whenever the boot-time page-table compiler succeeds, the freshly booted kernel satisfies the full global runtime invariant, with no program yet admitted and no return identity yet trusted.
- `createSubject_current` — Bookkeeping: creating a program never changes which program is current.
- `createSubject_objects` — Bookkeeping: creating a program never changes the registry of objects.
- `createSubject_slots` — Bookkeeping: creating a program never changes anyone's permission slots.
- `createSubject_kinds` — Bookkeeping: creating a program never changes the recorded kind of any object.
- `createSubject_runnable` — Bookkeeping: creating a program never changes which programs are marked runnable.
- `createSubject_addressOwner` — Bookkeeping: creating a program never changes who owns which memory space.
- `createSubject_preserves_live` — Creating a new program never revokes the liveness of any program that was already alive.
- `installCreatedSubject_coherent` — Publishing a newly created program keeps every kernel subsystem reading from the same single set of records.
- `installCapabilities_synchronizes_consumers` — Publishing a change to the permission registry updates every consumer, from execution and memory to messaging, scheduling, snapshots, and transfers, to the identical new registry in one step, so no view can keep the old one.
- `installCopiedCapabilities_synchronizes_consumers` — The lighter-weight publication used for permission copies likewise updates every consumer to the identical new registry in one step.
