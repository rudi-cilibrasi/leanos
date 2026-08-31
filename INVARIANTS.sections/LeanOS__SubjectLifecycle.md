# Program creation and termination

These theorems govern how the kernel creates and terminates programs (called "subjects"). A program's identity number is used at most once, ever, and termination is a single atomic sweep: it revokes all of the program's permissions, reclaims its memory, tears down its address spaces and message endpoints, and leaves everything belonging to other programs untouched — after which the retired identity can never be brought back.

- `create_rejected_unchanged` — Whenever the kernel refuses to create a program, the system state is left exactly as it was.
- `terminate_rejected_unchanged` — Whenever the kernel refuses a termination request, the system state is left exactly as it was.
- `create_preserves_wellFormed` — Creating a program keeps the system internally consistent: every owned resource, every runnable program, and the currently running program still belong to live programs.
- `terminateState_preserves_wellFormed` — The internal termination sweep keeps the system internally consistent in that same sense.
- `terminate_preserves_wellFormed` — The full termination operation, whether it succeeds or refuses, keeps the system internally consistent.
- `terminated_not_live` — After the termination sweep, the program is no longer live.
- `terminated_slot_empty` — After the termination sweep, every one of the program's permission slots is empty; it holds no capabilities at all.
- `terminated_lookup_invalid` — Any attempt to look up a permission on behalf of the terminated program is refused as coming from an invalid program.
- `terminated_not_runnable` — After the termination sweep, the program can no longer be scheduled to run.
- `terminated_not_current` — After the termination sweep, the program is never the currently running program.
- `terminated_address_spaces_removed` — Every address space the program owned is removed by the termination sweep.
- `terminated_memory_reclaimed` — Every memory object the program owned is removed and its physical memory frame is returned to the free pool.
- `unrelated_memory_unchanged` — Memory owned by any other program is left exactly as it was by the termination sweep.
- `terminated_endpoint_removed` — Every message endpoint the program owned is removed, together with any message waiting in it.
- `issued_history_preserved` — Termination never erases the record of which program identities have ever been issued.
- `old_identity_never_recreated` — Trying to create a program using a terminated program's identity is always rejected: a consumed identity stays consumed forever.
