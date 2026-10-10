# Stale child handles and cleanup after a child ends

This section shows that once a parent ends a child, every handle naming that child stops working and keeps failing, even after a new child takes the same table slot. It also shows that ending a child takes back everything the child was given.

- `TableAdvances.refl` — Bookkeeping: every state trivially relates to itself in the child-table order.
- `TableAdvances.retired` — A control handle that has stopped working stays stopped across any step that only adds child entries with new numbers.
- `TableAdvances.of_spawn_eq` — A step that leaves the spawn records alone keeps every stopped control handle stopped.
- `retired_rejected_unchanged` — Using a stopped control handle, to give memory or to end a child, is refused and leaves the state unchanged.
- `ChildOperation.apply_advances` — Every spawn operation only adds child entries with brand-new handle numbers or keeps old ones.
- `childGate_advances` — The same holds through the kernel's gate, including when it is busy or halted.
- `CompositeStep.advances` — Every ordinary kernel step leaves the child tables unchanged.
- `terminateChild_retires` — After a parent ends a child, the control handle it used no longer names anything.
- `terminateChild_revokes` — Ending a child removes every capability the child held, and every capability anyone held over something the child owned.
- `terminateChild_stale_word` — A handle that named something the ended child owned, such as a parent's endpoint to the child, no longer works.
- `stale_slot_after_respawn` — Spawning a new child never changes an existing subject's capability slots, so a slot emptied earlier stays empty.
- `stale_word_after_respawn` — A handle to something an ended child owned still fails after a new child is spawned.
- `terminateChild_releases` — Ending a child leaves it dead with no capabilities, not runnable, owning no address space, with all its frames returned to the parent, and with its table entry and spawn records removed.
