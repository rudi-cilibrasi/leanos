# Privacy over the gate a running program asks through

These theorems restate the observer's privacy guarantee over the subject gate, the gate a running program asks through. Another program's refused request changes nothing, so the observer cannot see it. When the observer itself names another program, both runs refuse in the same way, so the leaks of the earlier operations that named another program are gone; for every other request the subject gate is the kernel's engine and the earlier guarantees carry over. The last theorems re-run the exact example pairs on which those leaks were proved and show the answers and views now agree.

- `subjectGate_silent_observe` — A request the observer cannot see, including another program's refused request, leaves the observer's view unchanged.
- `run_state` — Bookkeeping: the state a run produces is exactly the run of requests through the subject gate.
- `system_replaysOn` — The observer's view of a run over the subject gate can be replayed from its events in any healthy state.
- `finite_trace_lowEquiv_subject` — Two runs through the subject gate that start from states the observer cannot tell apart, and show it the same events, end in states it cannot tell apart.
- `not_nmi_of_target` — A request that names a program is never a non-maskable interrupt.
- `authoritativeGate_not_running` — While the kernel is busy or halted, every request but a non-maskable interrupt changes nothing and is answered from the latch alone.
- `own_cross_stutter` — When the observer names another program, both runs change nothing and give the same answer.
- `own_step_cross` — Such a request leaves the two runs indistinguishable to the observer.
- `own_output_cross` — Such a request gets the same answer in both runs.
- `refuses_own` — A request by the scheduled observer that names no other program is never refused.
- `subjectGate_own` — Such a request, other than accepting a handover, is exactly the kernel's engine step.
- `own_step_consistent_subject` — Every request in the step-consistent family, now including every request that names another program and every drain, leaves two indistinguishable states indistinguishable, given the same identity counter.
- `own_output_consistent_subject` — Every request in the output-consistent family, now including every request that names another program, gets the same answer in two indistinguishable states, given the same identity counter.
- `cross_subject_channels_closed` — On the example pairs where creating, terminating, and queueing another program and copying into or revoking its slots used to leak, the subject gate gives equal answers and indistinguishable states.
- `revokeSubtree_other_closed` — On the example pair where revoking another program's permission tree used to depend on hidden history, the subject gate leaves the observer's view the same in both runs.
