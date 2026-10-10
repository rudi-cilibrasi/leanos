# Every kernel step reuses no retired capability identity

This section checks every kind of kernel step, including spawning and ending children, and shows each one only keeps old capability identities or hands out brand-new ones. So a handle to a capability removed when a child ends keeps failing after any later step.

- `CapabilityTransfer.offer_identityFrom` — Offering a capability through an endpoint creates a pending transfer with a brand-new identity and changes no capability.
- `CapabilityTransfer.offerWords_identityFrom` — The same holds for the handle-word form of an offer, including every refusal.
- `CapabilityTransfer.accept_identityFrom` — Accepting a transfer installs exactly the identity that was pending, or changes nothing.
- `CapabilityTransfer.acceptWord_identityFrom` — The same holds for the handle-word form of acceptance, including every refusal.
- `Scheduler.selectNext_capabilities` — Picking the next subject to run never changes the capability store.
- `Scheduler.tick_capabilities` — A timer tick never changes the capability store.
- `ResumablePreemption.switch_capabilities` — A preemptive switch between subjects never changes the capability store.
- `SubjectLifecycle.create_capabilities_slots` — Creating a subject changes no capability slot and keeps the identity counter.
- `cleanup_slots_sub` — Cleaning up an ended subject only removes capabilities.
- `CompositeState.Coherent.transfersCapabilities` — In a consistent state the transfer store sees the same capability store as the kernel.
- `CompositeState.Coherent.lifecycleCapabilities` — In a consistent state the lifecycle record sees the same capability store as the kernel.
- `CompositeState.Coherent.resumableCapabilities` — In a consistent state the saved-context bank sees the same capability store as the kernel.
- `installTerminatedSubject_shrinks` — Ending a subject only removes capabilities, cancels every pending transfer, and keeps the identity counter.
- `installTerminatedSubject_identityStep` — Ending a subject introduces no new capability identity.
- `publishInterruptCleanup_identityStep` — Cleaning up after a contained fault introduces no new capability identity.
- `installTransfers_identityStep` — Publishing a transfer-store change counts identities exactly as the transfer store does.
- `applyOperation_identityStep` — Every ordinary kernel operation only keeps old capability identities or hands out brand-new ones.
- `gate_identityStep` — The same holds through the kernel's entry gate, including when it is busy or halted.
- `authoritativeGate_identityStep` — Every authoritative kernel step, including blocking IPC and deferred cleanup, keeps or freshly allocates every identity.
- `InvalidationOperation.apply_identityStep` — Every step of the translation-invalidation protocol leaves capabilities and pending transfers unchanged.
- `lifecycleGate_identityStep` — Creating a subject with an issued identity introduces no new capability identity.
- `CompositeStep.identityStep` — Every ordinary kind of composite step keeps or freshly allocates every capability identity.
- `IdentityFrom.congr_left` — Identity accounting depends only on the capability slots and the identity counter.
- `spawnSpaced_identityStep` — Creating a child's address space installs one capability with a brand-new identity.
- `spawn_identityStep` — Spawning a child hands out only brand-new identities and changes no existing capability.
- `releaseChild_capabilities` — Returning an ended child's frames and records leaves the capability store unchanged.
- `releaseChild_pending` — Returning an ended child's frames and records leaves the pending transfers unchanged.
- `childGate_identityStep` — Every spawn-family operation, through the kernel's gate, keeps or freshly allocates every capability identity.
- `terminatedChild_shrinks` — Ending a child only removes capabilities and pending transfers and keeps the identity counter.
- `terminateChild_identityRetired` — Every capability removed when a parent ends a child has its identity retired, so no later step can hand that identity out again.
