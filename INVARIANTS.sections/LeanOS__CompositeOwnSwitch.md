# The observer's timer switch and return path

These theorems cover the observer's own timer switch and its return to user mode. The kernel's bookkeeping for scheduling (the ready queue, its size limit, which programs have a saved snapshot waiting, how many snapshots fit, and how many programs may wait on one endpoint) is treated as public, like the scheduler's choice itself. With that, the switch picks the same next program in both runs and the answer names only that program. Selecting the return path always gives the same fixed answer, and a return to user mode gives the same answer in both runs unless one run halts the machine, which is the termination channel the claim leaves out.

- `KernelPublic.schedulerPublic` — Public scheduler bookkeeping includes the public ready queue and its size limit.
- `tick_full` — When the ready queue is full, a scheduler tick is refused and changes nothing.
- `tick_of_current` — With room in the queue, a tick moves the running program to the back and runs the program at the front.
- `contextFor_some_iff` — The snapshot bank holds a snapshot for a program exactly when that program is one of its owners.
- `switch_decision` — Whether a timer switch succeeds, and which program it resumes, is decided by public data alone: the kind of entry, whether the saved frame is valid, the ready queue, the bank's owners and size, and the running program.
- `yield_accepted_lifecycle` — A yield that picks a program changes only which program is scheduled.
- `switch_success_state` — A successful switch schedules exactly the resumed program and keeps the address translation.
- `switch_restored_of_error` — A switch that reports no error always resumes some program.
- `observe_installResumable_current` — Publishing a new snapshot bank that changes only the scheduled program changes only the scheduled program in every observer's view.
- `switch_decision_of` — For the running observer in a healthy state, the switch's outcome is the public decision above.
- `switchDecisionOf_eq` — Two runs the observer cannot tell apart, with the same public scheduler bookkeeping, reach the same switch decision.
- `observe_apply_resumePreempt_own` — After the observer's own switch, its view differs from before only in which program is scheduled, and only if the switch succeeded.
- `own_step_resumePreempt` — The observer's timer switch leaves two indistinguishable runs indistinguishable.
- `own_output_resumePreempt` — The observer's timer switch gets the same answer in both runs.
- `own_output_selectUserReturn` — Selecting the return path gets the same fixed answer in both runs.
- `completeUserReturn_running` — A return to user mode either goes ahead or halts the machine.
- `own_output_userReturn` — When neither run halts, a return to user mode gets the same answer in both runs.
