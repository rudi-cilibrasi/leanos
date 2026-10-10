# The dispatcher's trace under the resource rules

This section shows that the stateful dispatcher's fixed trace, including its first step that creates subject 1 by a caller-named identity, satisfies the kernel's identity and frame-budget rules. The dispatcher starts from a boot state whose subject counter has not yet passed identity 1, which put that first step outside the whole-trace resource theorem. No kernel step ever looks at or changes the counters, so the proofs study a view of each dispatcher state that differs only in the subject counter, set just above 1. The dispatcher itself and its generated code are unchanged.

- `withIssuers_project` — Replacing the identity counters of a kernel state leaves every other part of the state exactly as it was.
- `issuers_unread` — No kernel step reads the identity counters.
- `authoritativeGate_withIssuers` — Running any kernel step on a state with different identity counters gives the same answer and the same result state, except for those counters.
- `authoritativeGate_issuers` — Every kernel step leaves the identity counters exactly as they were.
- `authoritativeGate_resourceView` — Taking the view and running a kernel step can be done in either order: the answer and the resulting state are the same.
- `resourceView_gate` — The view of a step's result is the step's result on the view.
- `resourceView_project` — The view differs from the dispatcher's own state only in the subject counter.
- `two_le_identityReserved` — The counter value 2 is inside the range of identities the kernel can issue.
- `resourceSeed_resourceRuntimeWellFormed` — The view of the boot state satisfies every kernel and resource rule, since nothing has been issued at boot.
- `runSteps_append_single` — Bookkeeping: running a list of steps and then one more step is the same as running the longer list.
- `materialize_pred` — Every dispatcher state other than the first is its predecessor's state after exactly one kernel step.
- `bind_pure_ok` — Bookkeeping: a successful "compute, then apply a function" result came from a successful computation.
- `materialize_resourceView` — The view of every state the dispatcher reconstructs is exactly what running its fixed command path from the view of the boot state produces.
- `resourceView_subject_next` — In the view, the next subject identity is always 2.
- `runSteps_subject_next` — Running the dispatcher's commands keeps the view's next subject identity at 2.
- `command_admissible` — Every dispatcher command meets the precondition of the whole-trace resource theorem when the next subject identity is 2; the only creation names identity 1, which is positive and below 2.
- `steps_admissible` — Every list of dispatcher commands meets those preconditions at every step.
- `dispatcher_createSubject_admissible` — Wherever the dispatcher accepts its create-subject-1 command (only at its first state), identity 1 is positive and below the view's subject counter, as the resource rules require.
- `dispatcher_edge_admissible` — Every accepted step of the dispatcher meets the precondition of the whole-trace resource theorem in the view of its starting state.
- `dispatcher_resource_trace` — For every state the dispatcher reaches, its view satisfies every kernel and resource rule, no subject identity is created twice or was issued before, and every subject's frame use and frame limit are exactly the boot values.
- `resourceView_budget` — The view and the dispatcher's own state have the same frame use and frame limit for every subject.
