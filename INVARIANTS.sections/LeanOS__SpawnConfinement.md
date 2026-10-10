# A spawned child can affect only what its capabilities reach

This section shows that a child created by spawn is confined. When the child acts through its own system calls, it can change what another subject sees only through an object both of them hold a capability to, or by naming that subject as the receiver of a capability it hands over or the holder of a capability it takes back. Right after spawn, the child holds capabilities to exactly two objects: the endpoint its parent gave it and its own new address space. The model still leaves some channels open, and the section names them: a receive that makes the child wait changes which subject is scheduled, and a whole-subtree revocation is always treated as visible.

- `names_iff` — A subject holds a capability to an object exactly when one of its usable capability slots names that object.
- `names_of_slot` — In a well-formed capability table, any capability a subject holds sits in a usable slot, so the subject counts as holding that object.
- `names_of_resolve` — When a handle presented by a subject resolves, the object it reaches is one that subject holds a capability to.
- `ipcTarget_named` — The endpoint a message send or receive acts on is always one the acting subject holds a capability to.
- `transferTarget_named` — The endpoint a capability hand-over offer or receipt acts on is always one the acting subject holds a capability to.
- `blockingTarget_named` — The endpoint a blocking send or receive acts on is always one the acting subject holds a capability to.
- `waiter_names` — A subject waiting for a message on an endpoint holds a receive capability to that endpoint.
- `child_step_silent` — Under the stated conditions, every system call of the child that leaves another subject's objects alone is classified as invisible to that subject.
- `child_step_confined` — When the child acts and shares no object with another subject, none of its system calls changes anything that subject sees, unless the call names that subject as the receiver or holder of a capability, or is a receive that makes the child wait.
- `child_run_confined` — The same holds for any sequence of such calls by the child: the other subject sees exactly what it saw before, and the kernel's safety invariant still holds.
- `reachDisjoint_of_bound` — If everything the child holds lies in some set and another subject holds nothing in that set, the two share no object.
- `spawn_child_names` — Right after spawn, the child holds capabilities to exactly two objects: the endpoint its parent gave it and its own new address space.
- `spawned_child_confined` — Right after spawn, any subject that holds neither of those two objects cannot be affected by the child's system calls, except when a call names that subject as the receiver or holder of a capability, or is a receive that makes the child wait.
