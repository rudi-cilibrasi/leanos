# Mapping, unmapping, and protecting memory

These theorems show that changing a program's memory mappings publishes one memory state everywhere, flushes stale address translations, and keeps both the global and the blocking runtime invariants, and that sequences of operations keep device-access quarantine intact.

- `gate_map_accepted_preserves_runtimeWellFormed` — An accepted mapping changes only the mapping records; memory contents, address-space ownership, endpoints, and every other resource stay exactly as before, while every mapping consumer sees the same new state.
- `gate_unmap_accepted_invalidates_tlb` — An accepted unmapping updates the authoritative memory view and evicts the matching cached translation before anything is published, so no stale translation for the removed page can survive the step.
- `gate_protect_accepted_invalidates_tlb` — An accepted tightening of a page's permissions acts for the kernel-selected program and address root, is published to every consumer, and the affected cached translation is already gone before the reply is returned.
- `gate_map_preserves_blockingRuntimeWellFormed` — Mapping is harmless to sleeping (blocked) programs whatever its outcome: refusals change nothing, and acceptance touches only mapping and translation-cache records while every field a waiter observes is retained.
- `gate_unmap_preserves_blockingRuntimeWellFormed` — Unmapping preserves everything blocked programs rely on, while still evicting the removed page from the kernel's translation cache.
- `gate_protect_preserves_blockingRuntimeWellFormed` — Tightening page permissions preserves everything blocked and deferred programs rely on, while evicting the affected page from the translation cache.
- `dispatchHardware_running_returnAuthority_unarmed` — Bookkeeping: whenever an interrupt arrives while the kernel is running normally, the transient permission to return to user mode comes out switched off.
- `dispatchHardware_running_not_alreadyHalted` — Bookkeeping: an interrupt taken while the kernel is running can never be classified as "already halted".
- `select_user_return_is_reachable` — Spelling out the definition: the composite step that arms return-to-user authority is exactly the underlying selection routine, and syscall and timer paths re-arm only after their final context update.
- `syscall_entry_leaves_return_unarmed` — After any interrupt is taken through the gate, whether it ends in fault containment, a fatal halt, a timer, or a system call, the transient permission to return to user mode is left switched off.
- `runOperations_directPortIO` — No finite sequence of public operations, including anything attempted after a fatal halt, can loosen the reviewed device-port controls or change any modeled device.
- `runOperations_preserves_dmaQuarantined` — Every finite sequence of ordinary operations keeps the accepted and observed PCI device configuration exact, so devices remain locked out of memory and the DMA quarantine holds throughout.
