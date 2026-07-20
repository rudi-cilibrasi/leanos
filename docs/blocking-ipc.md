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

The composite idle-block path is now part of the stable runtime claim. When a
typed blocking receive completes as `blocked` and its published scheduler has
no selected peer, the proof connects the dependency's exact caller and
scheduler mutation to the composite publisher: the caller is non-runnable,
the ready queue remains empty, the active translation is cleared, and both the
global runtime invariant and waiter/saved-context agreement are preserved.
The complementary immediate-handoff path is also part of the stable claim.
When the post-state names a selected peer, the proof fixes that peer as the
old ready-queue head, consumes exactly its kernel-owned resumable context, and
switches the modeled active translation to the same identity. Restore failure
remains a typed, state-preserving rejection rather than a partial block.

The typed blocked-context successor also exposes one atomic subject-termination
publication law: after lifecycle termination accepts, the same composite
post-state contains neither the dead subject's waiter index nor its suspended
blocked context. A lifecycle rejection publishes nothing and returns the
identical typed context and composite states. The public explicit-termination
gate and its scheduler-selected `terminateCurrent` spelling now use this
publisher before committing resumable/resource cleanup, so waiter and blocked
context absence are part of the same typed global result as lifecycle, ready
queue, resumable-context, and transfer cleanup. Terminating an endpoint owner still requires a broader
authority filter for other affected waiters before this predicate can be folded
into the global runtime invariant.

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
path, the compiler, and hardware remain outside this proof boundary. The
fixed-width `blockingIpcDemo` boundary encodes the one reviewed B-block,
A-send/wake, B-dispatch, and exact-delivery scenario. Its theorem connects each
accepted scalar result to the composite transition; it does not prove the C or
assembly bridge refines that transition.

Userspace-facing blocking receive and send use `receiveOrBlockWord` and
`sendWord`. Both consume the canonical 16-bit-slot/48-bit-generation opaque
word from `CapabilityHandle`, resolve it only in the trusted caller's capability
space, and preserve state on malformed, reserved, or stale encodings. The
raw-slot transitions remain internal model operations after this shared check.

Operations scan a bounded capability-slot function when checking receive
authority and filter bounded queues during cleanup. FIFO block/wake is linear
in the represented list length.
