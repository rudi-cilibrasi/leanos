# More operations by other programs that the observer cannot see

These theorems prove more of other programs' operations invisible to the observer, provided the kernel's main health condition holds. Asking the scheduler for the next program, yielding, timer ticks and adding to the ready queue change nothing the observer sees, and neither does removing a program that is not running. Offering or receiving a permission through an endpoint the observer cannot reach is invisible, and so is an interrupt that does not end the running program, a failed context switch, and returning a parked program other than the observer to the scheduler. With these operations silent, two runs that start indistinguishable and announce the same events still end indistinguishable. Returning a parked program is also safe for the observer's own runs.

- `observe_installTransfers_self` — Republishing the current transfer store changes nothing the observer sees.
- `observe_installTransfers_of` — A transfer update that keeps the observer's table and its objects' transfer fields changes nothing it sees.
- `offerWordsCheck_endpoint` — A successful offer validation resolved the caller's handle to the endpoint it then uses.
- `observe_apply_offer_other` — An offer through an endpoint the observer does not name leaves its view unchanged.
- `acceptWordCheck_endpoint` — A successful receipt validation resolved the caller's handle to the endpoint it then uses.
- `observe_apply_accept_other` — Another program receiving through an endpoint the observer does not name leaves its view unchanged.
- `observe_installResumable` — Republishing the saved-context store with the same scheduler and memory view leaves the observer's view unchanged.
- `observe_apply_interrupt` — An interrupt that does not end the running program leaves the observer's view unchanged.
- `switch_error_frame` — A failed context switch keeps the scheduler and the page-translation state.
- `observe_apply_resumePreempt` — A failed context switch leaves the observer's view unchanged.
- `observe_apply_scheduleRemove_unscheduled` — Removing a program that is not running from the queue leaves the observer's view unchanged.
- `drainDeferred_frame` — Returning a parked program changes only its own reply slot and scheduler bookkeeping.
- `observe_drain_other` — Returning a parked program other than the observer leaves the observer's view unchanged, whoever triggers it.
- `drain_self_rejected` — The running observer is never parked, so returning it is refused and changes nothing.
- `authoritativeGate_drain_pair` — With the same kernel mode, the gate either leaves both states alone or returns the parked program in both.
- `own_step_drain` — Returning any parked program keeps indistinguishable states indistinguishable while the observer runs.
- `own_output_drain_self` — Returning the observer itself gets the same answer in both states.
- `isSilentExtended_of_isSilentCoherent` — Every operation silent under the earlier classification is silent under this one.
- `transferTarget_not_named` — Bookkeeping: the silence test for a transfer means its endpoint is not one the observer names.
- `applyOperation_silentExtended_observe` — In a consistent state, every ordinary operation silent under this classification leaves the observer's view unchanged.
- `authoritativeGate_silentExtended_observe` — At the published gate and given the health condition, every operation silent under this classification leaves the observer's view unchanged.
- `runExtended_state` — The state part of an observed run under this classification is exactly the result of feeding the operations through the gate.
- `systemExtended_replaysOn` — In healthy states, this model meets the one-step replay guarantee.
- `finite_trace_lowEquiv_extended` — The main theorem with these operations silent: two healthy runs that start indistinguishable and announce the same events end indistinguishable.
