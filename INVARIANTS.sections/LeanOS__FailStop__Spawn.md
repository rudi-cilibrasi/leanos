# Explicit spawn: creating a child program in one step

A parent program holding a spawn permission creates a child in one all-or-nothing step: a fresh never-reused identity, an empty address space, and exactly one permission the parent chooses to pass on, with reduced rights if the parent wants. If any part fails, the kernel is left exactly as it was and the parent gets a specific error.

- `spawn_rejected_unchanged` — Every failed spawn, whatever stage it failed at, leaves the whole kernel state exactly as it was before.
- `spawn_rejected_iff` — The error a failed spawn reports is exactly the error of the first stage that failed.
- `spawn_missing_right` — A parent without a spawn permission is refused with the 'missing spawn right' error and nothing changes.
- `spawn_stale_spawn_capability` — A parent presenting an old or wrong spawn-permission number is refused with the 'stale spawn capability' error and nothing changes.
- `spawn_identity_exhausted` — When the supply of subject identities has run out, spawn is refused with the 'identity exhausted' error and nothing changes, not even the identity counters.
- `spawn_slot_table_full` — When the child's permission table is too small to hold what it must receive, spawn is refused and the identity it had just drawn is not used up.
- `spawn_address_space_exhausted` — When the supply of object identities has run out, spawn is refused and the child identity already drawn is rolled back.
- `spawnGrant_ok` — Bookkeeping: a successful endpoint hand-over step resolved the parent's handle, found the grant right, checked the rights requested, and installed the reduced copy.
- `spawnBuild_ok` — Bookkeeping: a successful spawn passed every stage, in order, and its result is exactly the state those stages build.
- `spawn_spawned_build` — Bookkeeping: a spawn that reports a new child came from a successful build of exactly that child.
