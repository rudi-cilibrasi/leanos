# What each kernel operation may touch: footprints and the frame rule

Every public kernel operation declares a footprint: the parts of the composite kernel state it may read and the parts it may change. The theorems here prove, once for each publication step and then for every operation, that everything outside an operation's footprint is left exactly as it was. Facts about untouched parts of the state are then derived from this frame rule instead of being re-proved operation by operation, so adding a new part to the kernel state does not force every existing proof to be redone.

- `CompositeState.Frames.mono` — A guarantee that a composite-state step leaves everything outside a narrow footprint unchanged also holds for any wider footprint.
- `selectLiveReturnAuthority_frames` — Choosing the return policy for the next return to a program changes only the execution record; every other part of the kernel state is left exactly as it was.
- `executionUpdate_frames` — Replacing only the execution record of the kernel state leaves every other part of the state exactly as it was.
- `executionResumableUpdate_frames` — Replacing only the execution record and the saved-context bank leaves every other part of the kernel state exactly as it was.
- `installLifecycle_frames` — Publishing a program-lifecycle change touches only the views that share the program and capability registry; device-port controls, device-access authority, the blocking-context bank, deferred cancellations, and pending invalidations are left exactly as they were.
- `installCopiedCapabilities_frames` — Publishing a capability copy or revocation touches only the views that share the capability registry; every other part of the kernel state is left exactly as it was.
- `installCreatedSubject_frames` — Publishing a newly created program touches only the views that share the program registry; every other part of the kernel state is left exactly as it was.
- `installScheduler_frames` — Publishing a scheduler change touches only the views that share the scheduler and program registry; every other part of the kernel state is left exactly as it was.
- `installSchedulerAdmission_frames` — Publishing a program's admission to the ready queue changes only the scheduler, the legacy preemption view, the saved-context bank, and the blocking store's scheduler; everything else is left exactly as it was.
- `installResumable_frames` — Publishing an exact saved-context bank changes only the views derived from it; the sealed-transfer store, blocking-context bank, deferred cancellations, device authority, and pending invalidations are left exactly as they were.
- `installSchedulerRemoval_frames` — Publishing a program's removal from scheduling changes only the execution record, scheduler views, program registry, saved-context bank, and blocking store; memory, messages, capabilities, transfers, and device state are left exactly as they were.
- `installTransfers_frames` — Publishing a sealed capability-transfer change touches only the views that share the capability registry and mailboxes; every other part of the kernel state is left exactly as it was.
- `installRevokedSubtree_frames` — Publishing a transitive capability revocation touches only the views that share the capability registry and mailboxes; every other part of the kernel state is left exactly as it was.
- `installTerminatedSubject_frames` — Publishing a program's termination touches only the shared registry views plus the blocking-context bank and deferred cancellations; device-port controls, device-access authority, and pending invalidations are left exactly as they were.
- `publishInterruptCleanup_frames` — Publishing the cleanup after a contained program fault touches only the shared registry views plus the blocking-context bank and deferred cancellations; device state and pending invalidations are left exactly as they were.
- `installVirtualMemory_frames` — Publishing a mapping-only memory change touches only the memory views and the records that mirror them; capabilities, transfers, blocking contexts, deferred cancellations, and device state are left exactly as they were.
- `installIPC_frames` — Publishing a message-passing change touches only the message store and the sealed-transfer store; every other part of the kernel state is left exactly as it was.
- `dispatchIPC_frames` — Handling a data-only message send or receive, whether accepted, rejected, or blocked by a pending sealed transfer, changes only the message store and the sealed-transfer store.
- `applyOperation_frames` — The frame rule: for every public kernel operation, every part of the composite kernel state outside that operation's declared footprint is exactly the same after the operation as before it.
- `applyOperation_project_untouched` — Any single part of the kernel state that an operation's footprint declares untouched has exactly the same value after the operation.
- `CompositeState.AgreeOn.refl` — Bookkeeping: every kernel state agrees with itself on any chosen set of parts.
- `CompositeState.AgreeOn.symm` — Bookkeeping: agreement between two kernel states on a chosen set of parts holds in either order.
- `CompositeState.AgreeOn.mono` — Two kernel states that agree on a set of parts also agree on every smaller set of parts.
- `CompositeState.AgreeOn.writes_of_reads` — Two kernel states that agree on everything an operation declares it reads also agree on everything it declares it writes, because every declared write is also a declared read.
- `CompositeState.eq_of_agreeOn_all` — Two kernel states that agree on every one of their named parts are the same state.
- `CompositeState.dependsOn_iff_agreeOn` — Spelling out the definition: a property depends only on some parts of the kernel state exactly when it survives any change that keeps those parts the same.
- `applyOperation_preserves_of_dependsOn` — Any property that depends only on parts of the kernel state an operation does not write is automatically preserved by that operation, without a separate proof for the operation.
- `Operation.footprint_untouched_authority` — No public kernel operation declares a write to the device-port controls, the accepted device-access authority, the live device-control observation, or the pending invalidation record.
- `dispatchIPC_directPortIO` — Bookkeeping: message operations never touch the hardware-port controls or the device state.
- `dispatchIPC_dmaAuthority` — Bookkeeping: message operations never touch either device-authority record.
- `installTerminatedSubject_directPortIO` — Bookkeeping: publishing a program's termination never touches the hardware-port controls.
- `applyOperation_directPortIO` — Every public operation leaves the hardware-port controls and device state literally untouched, so no attacker-controlled input can loosen port policy or fabricate a device transition; device changes live only at a separate, purpose-bound kernel boundary.
- `applyOperation_dmaAccepted` — No public operation can ever replace the boot-accepted device-authority record.
- `applyOperation_dmaObserved` — No public operation can ever replace the current device-control observation.
- `applyOperation_invalidationPublication` — No public kernel operation changes the record of pending translation invalidations.
