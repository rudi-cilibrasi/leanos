# Spawn keeps every rule of the kernel state

A successful spawn is three steps already proved safe in sequence (creating the identity, creating the address space, and copying one permission) followed by a record that no rule reads. This section proves that every spawn-related step, accepted or refused, keeps the full kernel rulebook and the resource guarantee.

- `issueSubject_execution` — Creating a subject identity does not change whether the kernel is running, which program is current, or the object identity counter.
- `spawn_unsupported` — Bookkeeping: no rule of the kernel rulebook or the resource guarantee looks at the spawn record.
- `withSpawn_resourceRuntimeWellFormed` — Changing only the spawn record keeps the full rulebook and the resource guarantee.
- `recordSpawn_resourceRuntimeWellFormed` — Recording a child's parent and address space keeps the full rulebook and the resource guarantee.
- `spaced_resourceWellFormed` — Creating the child's address space and advancing the object counter past it keeps the resource guarantee: the new identifier is below the advanced counter and no frame, binding, or budget changes.
- `spawn_creatable` — Inside a successful spawn, the address-space step's preconditions all hold on the state with the new child.
- `spawn_preserves_resourceRuntimeWellFormed` — Spawn, accepted or refused, keeps the full rulebook and the resource guarantee whenever the kernel is running.
- `SpawnOperation.apply_preserves_resourceRuntimeWellFormed` — Every spawn-family step (spawning, and the kernel granting or revoking a spawn permission) keeps the full rulebook and the resource guarantee.
- `spawnGate_preserves_resourceRuntimeWellFormed` — Every spawn-family step through the kernel's execution latch, including refusals while busy or halted, keeps the full rulebook and the resource guarantee.
