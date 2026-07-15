# Blocking IPC model

`LeanOS.BlockingIPC` composes the bounded scheduler, subject lifecycle, and
capability store into a sequential blocking-receive model. The scheduler's
lifecycle state is authoritative for subject identity, endpoint authority,
address-space ownership, runnable state, and the current subject. This layer
adds only bounded FIFO waiter queues and per-subject reserved completions.

`receiveOrBlock` atomically validates the current caller and receive authority,
checks for a reserved delivery, or appends the caller and deschedules it. An
accepted `send` removes the oldest waiter, reserves the exact two-word envelope
with scheduler-derived sender provenance, marks that receiver runnable, and
appends it once to the ready queue. Queue-capacity failures are unchanged-state
rejections. Reserving before wakeup prevents delivery theft.

Direct revocation atomically cancels and wakes its live victim. Transitive revocation filters every
waiter against the post-revocation capability store, including descendants,
and records typed cancellation. Endpoint destruction retires the object,
clears its mailbox, and wakes all live waiters with typed cancellation in the
same transition. Termination removes the dead identity without requeuing it.
Repeated cleanup is idempotent. Malformed stale waiters are removed by the
same authority filter.

## Bounds, observations, and progress

Wait queues and the scheduler ready queue have explicit fixed capacities.
FIFO order, queue occupancy, blocking, scheduling order, cancellation, and
delivery are intentional observations. A progress statement may assume
single-core sequential steps, a continuing scheduler, a live authorized
sender, available bounded capacity, and no later cancellation. It provides no
wall-clock, fairness, SMP, timeout, priority, or deadlock-freedom guarantee.

The Lean theorems concern this executable state machine. The executable
counterexamples record why split check/sleep and unreserved wakeup are unsafe.
Compilation and QEMU are integration evidence only; generated code, the boot
path, the compiler, and hardware remain outside this proof boundary.

Operations scan a bounded capability-slot function when checking receive
authority and filter bounded queues during cleanup. FIFO block/wake is linear
in the represented list length. No boot adapter is claimed by this model.
