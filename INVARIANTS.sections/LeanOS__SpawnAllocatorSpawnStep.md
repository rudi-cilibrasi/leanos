# Spawning a child in the kernel is the allocator's spawn

A spawn in the kernel model creates a subject, an address space and an endpoint copy, and records the child in the parent's table. On every kernel state the allocator describes, this file shows that the kernel's spawn gives the same status and control word as the allocator, that an accepted spawn leaves a kernel state whose record is the allocator's next record, and that the result is again a state the allocator describes.

- `family_runtime` — These kernel states satisfy the kernel's runtime invariant.
- `family_lifecycleCapabilities` — On these kernel states, the lifecycle's copy of the capability registry is the registry itself.
- `family_spawnParent` — On these kernel states, the subject that spawns is the allocator's parent.
- `identityExhausted_issuer` — The kernel's test for a used-up identity counter is the allocator's test on the counter's next value.
- `family_issueSubject` — When subject identities are not used up, issuing a subject on these kernel states hands out the next subject identity.
- `family_dead_slots` — A subject that is not live holds no capability.
- `family_next_dead` — The next subject identity to be issued is not a live subject.
- `family_next_object` — The next object identity to be issued has never been used as an address space or memory object, is not live, and nothing owns it.
- `created_capabilities` — Issuing the next subject only marks that subject live in the capability registry, and the memory model keeps the same registry.
- `created_records` — Issuing the next subject changes no ownership record and no issued-object history.
- `endpointRights_subset` — Any valid endpoint rights are a subset of the parent endpoint's rights.
- `spaced_parentSlots` — After the spawn's address-space stage, the parent's slots are still exactly as the allocator reads them.
- `spaced_copy_accepted` — During a spawn, copying the parent's endpoint into the new child's first slot is accepted for every valid set of rights.
- `spawn_result_family` — On these kernel states, an authorized spawn's result is decided entirely by the allocator's record.
- `controlWord_eq` — For a slot inside the table and a valid generation, the kernel's control word is the allocator's control word.
- `controlGenerationAvailable_eq` — The kernel's test for an available control generation is the allocator's test.
- `freeSlot_none_count` — When the allocator finds no free child slot, the parent already has four children.
- `spawnAuthorize_family` — On these kernel states, checking the spawn right gives the allocator's answer: missing, stale, or held.
- `spawnCharged_family` — A charged spawn on these kernel states returns the allocator's status and value, and a refused spawn leaves the kernel state unchanged.
- `copy_accepted_fields` — An accepted capability copy advances the identity counter by one and changes no subject, object, kind or slot capacity.
- `spawn_post` — After an accepted spawn, each part of the kernel state the allocator and its invariant read has the expected value: counters advanced, the child live with its address space, and everything the parent holds unchanged.
- `map_range_set` — A stepping-stone fact: a table that agrees with another everywhere except one position is that table with the one position replaced.
- `spawnResultOf_spawned` — A spawn the record decides as accepted creates the next subject identity with the next object identity as its address space.
- `spawnCharged_accepted` — An accepted charged spawn on these kernel states spawns the next subject and records it in the allocator's free slot.
- `installChild_issuers` — Recording a child changes no identity counter.
- `installChild_capabilities` — Recording a child changes no capability.
- `installChild_nextChildGeneration` — Recording a child advances the control-generation counter by one.
- `installChild_nextGeneration` — Recording a child does not change the spawn-right generation counter.
- `installChild_authority` — Recording a child does not change who holds the spawn right.
- `installChild_budgetLimit` — Recording a child does not change any subject's frame limit.
- `installChild_children` — Recording a child writes exactly one new entry, with no frames and the next control generation, into the parent's table.
- `spawnCharged_abstraction` — After an accepted charged spawn, the kernel state's record is the allocator's next record.
- `family_childGate_invariants` — Every child operation on these kernel states keeps the kernel's resource, child-accounting and spawn-tree invariants.
- `family_owned_space_ne` — An address space that someone owns is not the next object identity to be issued.
- `family_live_object_ne` — A live object is not the next object identity to be issued.
- `spawnCharged_family_preserved` — An accepted charged spawn leaves a kernel state the allocator still describes.
