# The observer's blocking operations

These theorems cover the observer's own blocking send, its blocking receive, and its cancellation of its own wait, with the kernel's scheduling bookkeeping treated as public. A blocking send's outcome depends only on the observer's handle, the endpoint's state, which the observer sees, the ready queue, and, when it wakes a waiting program, the size of the snapshot bank. The woken program's saved registers move into the bank; the answer names the woken program only, the first in a queue the observer sees. A blocking receive's outcome depends only on public data and data the observer sees. Cancelling its own wait changes nothing, because a running program waits on nothing.

- `observe_publishBlocking_eq` — Publishing a new blocking store changes the observer's view only in the scheduled program, the queues and mailboxes of the endpoints it names, and its own wait and delivery.
- `lowEquiv_publishBlocking` — Two runs that publish blocking stores agreeing on everything the observer sees stay indistinguishable.
- `send_congr` — A raw blocking send by the observer has the same outcome in two stores that agree on its handle, its endpoint, and the ready queue.
- `send_accepted_kind` — An accepted send went through an endpoint permission.
- `send_accepted_wake` — An accepted send to an endpoint with a waiting program wakes exactly the first waiting program.
- `endpointOf_of_lookup` — The endpoint a send or receive uses is the object the observer's endpoint permission names.
- `publishReleased_eq` — Handing a woken program's snapshot to the bank succeeds unless the bank is full.
- `dispatchBlockingSend_shape` — The observer's blocking send's answer and resulting view are a fixed function of public data and data the observer sees.
- `current_not_waiter` — The running observer is in no endpoint's waiting queue.
- `sendShape_eq` — That function gives the same result in two indistinguishable runs with the same public bookkeeping.
- `blockingCaps_eq` — The blocking store's copy of the permission table is the published one.
- `dispatchBlockingSend_pair_eq` — The observer's blocking send gives the same answer and indistinguishable views in both runs.
- `own_blockingSend` — The observer's blocking send, through the kernel's gate, leaves two indistinguishable runs indistinguishable and gives the same answer in both.
- `receive_congr` — A raw blocking receive by the observer has the same outcome in two stores that agree on its handle, its endpoint, its own delivery, and the queue limits.
- `restoreBlockingPeer_shape` — When the observer blocks, the kernel restores the first ready program exactly when the bank holds its snapshot.
- `receive_blocked_lifecycle` — A receive that blocks keeps the permission table, makes the caller not runnable, and schedules the first ready program, if any.
- `dispatchBlockingReceive_shape` — The observer's blocking receive's answer and resulting view are a fixed function of public data and data the observer sees.
- `receiveShape_eq` — That function gives the same result in two indistinguishable runs with the same public bookkeeping.
- `dispatchBlockingReceive_pair_eq` — The observer's blocking receive gives the same answer and indistinguishable views in both runs.
- `own_blockingReceive` — The observer's blocking receive, through the kernel's gate, leaves two indistinguishable runs indistinguishable and gives the same answer in both.
- `dispatchBlockingCancel_self` — Cancelling the running observer's own wait answers that it is not waiting and changes nothing.
- `own_blockingCancel_self` — Cancelling its own wait leaves two indistinguishable runs indistinguishable and gives the same answer in both.
- `reply_scheduleAdd_self` — Asking to queue the running observer itself is always refused as a duplicate.
