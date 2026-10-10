# Creating an empty address space inside the kernel state

Explicit spawn gives a new program its own empty address space. Until now the full kernel state could not create an address space at all; this section adds that step and proves it keeps every rule the kernel state promises. Creating an address space activates a never-used identifier, records the new program as its owner with no page mappings, and gives the owner one root permission over it.

- `VirtualMapping.createAddressSpace_accepted_state` — When the memory model accepts creating an address space, all of its checks held (live owner, valid empty slot, unused identifier, identity counter in range), and the result is exactly the state this section publishes.
- `addressSpaceCapabilities_subjects` — Bookkeeping: creating an address space does not change which subjects are alive.
- `addressSpaceCapabilities_slotCapacity` — Bookkeeping: creating an address space does not change how many permission slots any subject has.
- `addressSpaceCapabilities_nextIdentity` — Bookkeeping: creating an address space uses up exactly one fresh permission identity.
- `addressSpaceCapabilities_objects` — Bookkeeping: after creation exactly the new address space becomes live; every other object keeps its liveness.
- `addressSpaceCapabilities_kinds` — Bookkeeping: after creation the new identifier is recorded as an address space; every other object keeps its kind.
- `addressSpaceCapabilities_slots` — Bookkeeping: creation fills exactly the owner's chosen slot with the new root permission and leaves every other slot alone.
- `addressSpaceCapabilities_derivations` — Bookkeeping: creation records the new root permission's history entry and leaves all earlier history entries alone.
- `addressSpaceCapabilities_objects_mono` — Objects that were live stay live when an address space is created.
- `addressSpaceCapabilities_slots_mono` — Every permission a subject already held is still held after an address space is created into an empty slot.
- `addressSpaceCapabilities_authority_mono` — Creating an address space never takes authority away from anyone.
- `addressSpaceCapabilities_kinds_of_ne` — Bookkeeping: every object other than the new address space keeps its recorded kind.
- `addressSpaceCapabilities_objects_of_ne` — Bookkeeping: every object other than the new address space keeps its liveness.
- `addressSpaceCapabilities_derivations_of_lt` — Bookkeeping: every permission history entry recorded before the creation is unchanged.
- `addressSpaceCapabilities_wellFormed` — Creating an address space for a dead identifier into an empty, in-range slot of a live subject keeps the permission table well formed.
- `installCreatedAddressSpace_mode` — Bookkeeping: creating an address space does not change whether the kernel is running, handling an interrupt, or halted.
- `installCreatedAddressSpace_capabilities` — Bookkeeping: after creation the kernel's permission table is exactly the table with the new root permission installed.
- `installCreatedAddressSpace_empty` — The new address space is owned by the requested subject, in both of the kernel's views of ownership, and has no page mappings at all.
- `addressOwner_none_of_unissued` — In a well-formed kernel state, an address-space identifier that was never issued has no recorded owner.
- `installCreatedAddressSpace_preserves_runtimeWellFormed` — Creating an address space when its preconditions hold keeps the kernel's whole runtime rulebook: every copy of the permission table agrees, ownership, mappings, scheduling, saved contexts, and in-flight permission transfers all stay valid.
- `createdVirtualMemory_capabilities` — Bookkeeping: the memory view's permission table after creation is the table with the new root permission.
- `setOwner_mono` — Recording an owner for an identifier that had none keeps every existing owner record.
- `installCreatedAddressSpace_preserves_authoritativeRuntimeWellFormed` — Creating an address space also keeps the stronger rulebook covering blocked message receivers, their saved contexts, deferred cancellations, and pending translation invalidations.
