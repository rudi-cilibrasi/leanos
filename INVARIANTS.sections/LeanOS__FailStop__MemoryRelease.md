# Releasing a memory object everywhere

This section adds the kernel step that releases one memory object: every capability naming it is removed from every subject, every mapping of it is removed, cached translations are flushed, sealed transfers carrying it are cancelled, and its frame becomes free. It proves that the release keeps the whole kernel rulebook.

- `retireCapabilities_subjects` — Retiring an object does not change which subjects are alive.
- `retireCapabilities_nextIdentity` — Retiring an object does not use any capability number.
- `retireCapabilities_derivations` — Retiring an object keeps the whole history of capability records.
- `retireCapabilities_slotCapacity` — Retiring an object does not change how many slots any subject has.
- `retireCapabilities_objects` — After retiring an object it is dead, and every other object is as alive as before.
- `retireCapabilities_kinds` — After retiring an object it has no kind, and every other object keeps its kind.
- `retireCapabilities_slots_some` — After retiring an object, a slot holds a capability exactly when it held it before and the capability names some other object.
- `retireCapabilities_objects_of_ne` — Retiring an object does not change whether any other object is alive.
- `retireCapabilities_kinds_of_ne` — Retiring an object does not change the kind of any other object.
- `retireCapabilities_authority` — Retiring an object keeps every authority over every other object.
- `retireCapabilities_wellFormed` — Retiring an object keeps the capability rulebook.
- `installReleasedMemory_mode` — Publishing a release does not change whether the kernel is running, busy, or halted.
- `installReleasedMemory_capabilities` — After publishing a release, the kernel capability table is the retired one.
- `installReleasedMemory_released` — After a release the object is dead, no slot names it, nothing maps it, no pending transfer carries it, it has no frame, its frame is free, and no translation is cached.
- `releasedTransfers_pending` — A sealed transfer that survives the release was already pending, carries some other object, and keeps its message.
- `releasedTransfers_mailbox_some` — The release never creates a message in any mailbox.
- `releasedTransfers_mailbox_none` — A mailbox that was empty stays empty through the release.
- `installReleasedMemory_preserves_runtimeWellFormed` — Publishing a release keeps the whole kernel runtime rulebook.
- `installReleasedMemory_preserves_authoritativeRuntimeWellFormed` — Publishing a release keeps the full kernel rulebook, including the blocking, waiting, and invalidation parts.
