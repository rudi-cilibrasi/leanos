# Keeping track of who owns each piece of physical memory

The frame allocator is the kernel's ledger of physical memory: every frame of memory is either reserved (off-limits), free, or owned by exactly one owner. These theorems guarantee the ledger can never get confused — no frame is ever in two states at once, no frame ever has two owners, reserved memory is never handed out, and giving memory back or taking it out always moves it cleanly between the free pool and a single owner.

- `conservation` — Every tracked frame is always in one of exactly three states — reserved, free, or owned by some owner — with no fourth, undefined possibility.
- `init_establishes_conservation` — Bookkeeping: the ledger built at startup from the firmware's memory map already satisfies that three-state rule.
- `reserved_not_free` — A reserved frame is never simultaneously counted as free.
- `reserved_not_owned` — A reserved frame is never simultaneously owned by anyone.
- `ownership_exclusive` — A frame has at most one owner: whenever the ledger says two owners hold the same frame, they are in fact the same owner.
- `allocated_is_owned` — Whenever an allocation succeeds, the frame handed out is recorded as owned by exactly the requester.
- `allocated_not_reserved` — An allocation never hands out a reserved frame.
- `allocation_preserves_conservation` — Bookkeeping: after a successful allocation, every frame is still in exactly one of the three states.
- `released_is_free` — Whenever a release succeeds, the released frame is back in the free pool, available for reuse.
- `release_preserves_conservation` — Bookkeeping: after a successful release, every frame is still in exactly one of the three states.
- `invalid_release_explicit` — Trying to release a frame you do not own is always refused with an explicit error — it never silently succeeds.
