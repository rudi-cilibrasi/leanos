# Privacy for every request the observer makes

This is the complete per-step guarantee. Take two states in which the observer is the running program, that it cannot tell apart through its full view, and that agree on the inputs the claim declares public: the permission-number counter and the scheduler's bookkeeping. Then every request the observer can make through the subject gate leaves them indistinguishable through the full view, and gets the same answer in both, with one exception: a return to user mode can differ in whether it halts the machine, which is the termination channel the claim leaves out. Nothing else is excluded.

- `FullStep.ownStep` — The premise includes the ordinary own-step premise.
- `FullStep.full` — The premise includes agreement on the full view.
- `FullStep.agree` — The premise includes the fact-by-fact agreement on the extra authority.
- `FullStep.issuedLeft` — In the first state every held permission and pending handover is issued.
- `FullStep.issuedRight` — In the second state every held permission and pending handover is issued.
- `FullStep.carried` — The premise gives agreement on every object offered to the observer.
- `extra_of_dead` — A terminated observer's extra authority is empty.
- `full_of_frames` — A request whose effect, on each side, adds nothing the observer does not see keeps the full views equal when it keeps the ordinary views equal.
- `frame_of_unchangedApply` — A request that changes no object adds nothing the observer does not see.
- `gate_running` — While the kernel is running, the gate applies an ordinary request.
- `issued_apply` — A request applied in a healthy running state leaves a state where everything held or pending is issued.
- `full_of_agree` — A request keeps the full views equal when its applied effect keeps the fact-by-fact agreement and the ordinary views equal.
- `full_of_extra` — A request keeps the full views equal when its applied effect keeps the extra authority equal and the ordinary views equal.
- `full_ordinary` — Every ordinary request of the observer that names no other program keeps the full views equal.
- `full_blocking_frames` — A blocking request whose effect adds nothing the observer does not see keeps the full views equal.
- `full_blocking` — Every blocking request of the observer that names no other program keeps the full views equal.
- `full_drain_self` — The observer's drain of its own parked cancellation changes nothing.
- `refusesNestedTransfer_congr` — Whether the subject gate refuses an acceptance is decided by what the full view shows, so it is the same in both runs.
- `full_step` — Every request through the subject gate keeps two fully indistinguishable states fully indistinguishable.
- `output_ordinary` — Every ordinary request of the observer that names no other program, other than a return to user mode, gets the same answer in both runs.
- `output_authoritative` — Every such request, ordinary, blocking, or drain, gets the same answer in both runs.
- `full_output` — Every request through the subject gate gets the same answer in both runs; a return to user mode does too when neither run halts.
