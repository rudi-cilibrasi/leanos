# Privacy when the observer ends itself or the hardware interrupts it

These theorems cover the observer's own termination and the kernel's interrupt entries while the observer runs. When the observer ends itself, everything it could see disappears: its table is emptied, it owns no address space, nothing is running and it waits on nothing. What it sees afterwards depends only on its table size and its pending reply, which agree in two indistinguishable states. An interrupt is classified from the hardware frame, the kernel mode and the running program alone, so it gets the same answer in both states, and it either ends the observer as above or changes nothing it sees. A non-maskable interrupt only halts the kernel and also gets the same answer. These results need the kernel's full health condition.

- `observe_dead` — A state in which the observer is gone, nothing runs and it owns no address space shows it a fixed view built from its table size and reply.
- `not_waiting` — In a healthy state, the running observer is not waiting on any endpoint.
- `terminate_self_blocking` — Removing a program that is not waiting from the blocking-message store keeps its waiting entry empty and its reply.
- `cleanup_self_fields` — Ending the running observer clears the running program, its liveness, its table and its address spaces, keeps its table size and reply, and leaves it waiting on nothing.
- `observe_installTerminatedSubject_self` — After the observer ends itself, it sees exactly the fixed view.
- `observe_publishInterruptCleanup_self` — After a contained fault ends the observer, it sees exactly the fixed view.
- `terminate_self_accepted` — The running observer is alive and was created, so terminating it succeeds.
- `apply_terminate_self` — Terminating the running observer runs the full cleanup for it.
- `apply_terminateCurrent_self` — Terminating the running program while the observer runs runs the full cleanup for the observer.
- `own_step_terminate_self` — The observer ending itself keeps indistinguishable healthy states indistinguishable.
- `own_step_terminateCurrent` — Terminating the running program keeps indistinguishable healthy states indistinguishable.
- `interrupt_action_eq` — The raw interrupt classification reads only the entry flag and the running program.
- `finishEntry_action` — A completed first entry's classification is computed from the raw classification.
- `dispatchHardware_action_eq` — An interrupt's classification depends only on the hardware frame, the kernel mode and the running program.
- `observe_apply_interrupt_own` — After an interrupt, the observer either sees the fixed view (its own fault was contained) or its unchanged view.
- `own_step_interrupt` — An interrupt while the observer runs keeps indistinguishable healthy states indistinguishable.
- `own_output_interrupt` — An interrupt while the observer runs gets the same answer in both states.
- `dispatchNmi_action_eq` — A non-maskable interrupt's halt decision depends only on the mode, the hardware snapshot, and the running program and address space.
- `own_output_nmi` — A non-maskable interrupt while the observer runs gets the same answer in both states.
