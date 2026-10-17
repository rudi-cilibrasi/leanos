# The kernel's spawn family behaves exactly like the spawn allocator

This is the general result behind the spawn allocator. On every kernel state the allocator describes, every command the allocator decides (spawn, frame grant, termination, memory allocation and release, and the kernel's grant and revocation of the spawn right) runs through the kernel's gate to the allocator's status and value, leaves a kernel state whose record is the allocator's next record, and that state is again one the allocator describes. So everything proved about the allocator for every record holds for the kernel on all of these states, not only on a list of examples, and the same follows for whole sequences of commands.

- `familyStep_child` — On these kernel states, the gate runs every child operation and reports its result.
- `familyStep_memory` — On these kernel states, the gate runs every memory operation and reports its result.
- `child_simulates` — A child operation behaves like an allocator step whenever it returns the allocator's status and value and an accepted one keeps the record and the description; a refusal leaves both sides unchanged.
- `memory_simulates` — A memory operation behaves like an allocator step under the same conditions.
- `family_withAuthority` — Changing only who holds the spawn right keeps a state the allocator describes, as long as the parent's right stays within bounds and no one else gains one.
- `abstraction_withAuthority` — After changing only who holds the spawn right, the record changes only in its spawn-right fields.
- `grantBudgetedAuthority_eq` — The kernel's grant of a budgeted spawn right, written out: granted when the subject is live, the budget fits, its children fit the budget, and it is not itself a child; refused otherwise.
- `family_child_recorded` — A live subject other than the parent and the other subject is recorded as the parent's child, so the kernel never grants it a spawn right.
- `grantAuthority_simulates` — Every grant of the spawn right the allocator decides behaves in the kernel exactly as the allocator says.
- `revokeSpawnAuthority_eq` — Revoking a spawn right only removes that subject's right.
- `revokeAuthority_simulates` — Every revocation of the spawn right behaves in the kernel exactly as the allocator says.
- `allocateStep_value` — A memory allocation's value word is always zero.
- `releaseStep_value` — A memory release's value word is always zero.
- `familyStep_simulates` — The general simulation: on every kernel state the allocator describes, every command the allocator decides gives the allocator's status and value, a kernel state whose record is the allocator's next record, and a state the allocator still describes.
- `step_undecided` — The only commands the allocator leaves undecided are the kernel's grants of the spawn right that the record cannot hold.
- `familyTrace_simulates` — Whole sequences of commands: from a kernel state the allocator describes, every sequence the allocator decides gives the allocator's replies and ends in a state whose record is the allocator's final record.
