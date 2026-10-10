# What a spawned child receives, and what nobody else gains

These theorems spell out exactly what a newly spawned child starts with: one permission over the endpoint the parent named, with no more rights than the parent asked for and held, plus control of its own new empty address space, and nothing else. No other program, the parent included, gains any authority, and the child's identity was never used before.

- `SubjectLifecycle.create_accepted_state` — Bookkeeping: an accepted subject creation only marks the new identity as live and as issued.
- `Capability.copy_accepted_slots` — An accepted permission copy installs exactly one reduced copy of the source permission in the target slot and changes no other slot.
- `spawn_spawned_stages` — Bookkeeping: a successful spawn is exactly the identity step, the address-space step, the endpoint copy, and the record, in that order.
- `issueSubject_capabilities` — Bookkeeping: creating a subject identity only marks it live in the permission table; every slot is unchanged.
- `spawn_parent_ne_child` — The parent and the child are different subjects: the parent was alive and the child was not.
- `spawn_child_capabilities` — Exact inheritance: after a spawn the child holds exactly two permissions, a copy of an endpoint permission the parent held with the right to pass it on, carrying exactly the requested rights, which the parent also had, and the root permission of its own new address space; every other slot is empty.
- `spawn_child_authority` — The child can do something to an object exactly when it is a requested right over the granted endpoint or a root right over its own new address space; it has no authority over anything else that existed before.
- `spawn_other_slots_unchanged` — Every subject other than the child, the parent included, has exactly the same permission slots after the spawn as before.
- `spawn_no_authority_amplification` — No subject other than the child gains or loses any authority through a spawn.
- `spawn_parent_unchanged` — The parent's permissions are exactly the same after spawning as before.
- `spawn_registry` — Spawn leaves the table of spawn permissions unchanged, so the child receives no power to spawn, and records the parent and the address space for the child.
- `spawn_fresh_identity` — The child's identity is the next one the counter hands out, was never issued or alive before, and is larger than every identity ever issued; its address space identifier was likewise never issued.
- `spawn_keeps` — Spawn changes nothing outside the permission tables, the subject records, the new address space, the counters, and the spawn record: run queues, saved contexts, waiting receivers, mailboxes, transfers, device state, frame budgets, frames, and bindings are all unchanged.
- `spawn_child_starts_empty` — The child starts with nothing else: a zero frame budget; not runnable, not running, and not queued; no saved, blocked, or deferred context; not waiting on any endpoint; no message or permission transfer in flight from it; unchanged device state; and an address space it owns with no mappings.
- `spawnAuthorize_ignores_records` — The spawn permission check never reads the recorded parent/child relation or address-space record: the relation is never authority.
- `footprints_unread_spawn` — No other kernel operation reads the spawn record at all.
- `spawn_endpoint_resolves` — A successful spawn used a handle that, before the spawn, named a live endpoint permission of the parent's with the right to pass it on and rights covering the request.
- `spawn_stale_endpoint_rejected` — A malformed, stale, revoked, wrong-kind, or out-of-range endpoint handle makes spawn fail and roll back completely, even though the identity and address space had already been built.
- `spawnGate_unchanged_of_not_running` — While the kernel is busy handling an interrupt or halted, every spawn-family request is refused with nothing changed.
