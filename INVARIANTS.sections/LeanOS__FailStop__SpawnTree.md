# Children never have children, and ending a child cleans up everything

This section shows that a spawned child can never hold permission to spawn, so it never has children of its own. Ending a child therefore leaves nothing behind. It also shows that ending a child gives back everything the child was given, including the frames of memory the child allocated.

- `spawnTree_of_empty` — A state with no spawn records satisfies the family-tree rules.
- `spawnTree_of_kept` — A step that leaves the spawn records alone and only adds to the identity history keeps the family-tree rules.
- `charged_child_childless` — Every child in any child table has no spawn permission and no children of its own.
- `not_recorded_of_authority` — A subject with spawn permission was never spawned as a child.
- `not_recorded_of_children` — A subject with children was never spawned as a child.
- `child_spawn_rejected` — When a spawned child is running, every spawn request is refused for missing permission and nothing changes.
- `CompositeStep.spawnTree` — Every ordinary kernel step keeps the family-tree rules.
- `memoryGate_spawnTree` — Every memory operation keeps the family-tree rules.
- `spawn_parent_record` — A spawn records exactly the new child's parent and changes no other parent record.
- `spawnCharged_spawnTree` — A charged spawn keeps the family-tree rules.
- `grantFrames_spawnTree` — Giving memory to a child keeps the family-tree rules.
- `terminateChild_spawnTree` — Ending a child keeps the family-tree rules.
- `childGate_spawnTree` — Every spawn operation, in every outcome, keeps the family-tree rules.
- `terminateChild_no_orphans` — Ending a child leaves no orphan: the child never had children, and afterwards no table names a child of it.
- `terminatedChild_retires_memory` — Ending a live subject kills every memory object it owned.
- `terminateChild_releases_everything` — Ending a child gives back everything: it is dead with no capabilities, not runnable, owns no address space; all its frames go back to the parent; the frames of its own memory are free, wiped, and unbound; it had no children; and its records are gone.
