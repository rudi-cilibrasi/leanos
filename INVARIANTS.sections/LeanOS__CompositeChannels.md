# Leaks behind the observer's excluded operations

These theorems show that each operation left out of the observer's privacy guarantee really does leak. Each one starts from the kernel's standard example state and builds two states that the observer, program 2, cannot tell apart, using only its own steps: creating program 3, handing a permission to slot 2 or slot 3 of program 1, or offering one of its own permissions. The two states agree on every condition of the privacy theorems, including the public permission counter. The excluded operation then gives different answers or visibly different results.

- `step_wellFormed` — One kernel step from a healthy state reaches a healthy state.
- `observe_step_of_apply` — If an operation's effect leaves the observer's view unchanged, so does sending it through the kernel gate.
- `seed_wellFormed` — The kernel's standard example state is healthy.
- `seed_current` — In the standard example state, program 2 is running.
- `observe_created` — Program 2 creating program 3 leaves its own view unchanged.
- `observe_toSlot` — Program 2 handing a permission to program 1 leaves its own view unchanged.
- `ownStepCounter_of` — Two healthy states with program 2 running, the same mode and the same counter, that program 2 cannot tell apart, meet every condition of the privacy theorems.
- `seed_created` — The example state and the state after creating program 3 meet every condition.
- `slotThree_slotTwo` — The states after handing a permission to program 1's slot 3 or slot 2 meet every condition.
- `offered_offeredCreated` — The state after program 2's offer, with and without program 3 created, meet every condition.
- `create_output_inconsistent` — Creating another program reveals whether it is already alive.
- `terminate_output_inconsistent` — Terminating another program reveals whether it was ever created.
- `scheduleAdd_output_inconsistent` — Adding another program to the ready queue reveals whether it is alive.
- `terminate_step_inconsistent` — Terminating another program cancels every pending sealed permission, including the observer's own offer, exactly when the termination succeeds, so the observer can tell the results apart.
- `copy_destination_output_inconsistent_counter` — Even with the counter equal, handing a permission to another program reveals whether its destination slot is occupied.
- `revoke_other_output_inconsistent` — Revoking another program's slot reveals whether that slot is occupied.
- `revokeSubtree_other_output_inconsistent` — Revoking a permission tree at another program's slot reveals whether that slot is occupied.
- `offer_counter_step_inconsistent` — Without the public counter, the observer's own offer gives distinguishable results, because the sealed permission is numbered by the global counter.
