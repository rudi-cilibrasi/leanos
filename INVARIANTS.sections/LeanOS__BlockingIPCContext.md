# Saving a sleeping program's place so it can resume

When a program goes to sleep waiting for a message, the kernel saves a snapshot of exactly where it left off so it can later pick up as if nothing happened. These theorems guarantee that saved snapshots and waiting lines always agree one-for-one — every sleeper has exactly one valid snapshot, and no snapshot exists without its sleeper — and that every wake-up, cancellation, cleanup, or termination hands back or discards exactly the right snapshot in the same indivisible step, so a program can never be lost, duplicated, or resumed with someone else's state.

- `validSaved_owner` — Bookkeeping: a snapshot that passes the validity check belongs to the very program it is saved for.
- `validSaved_kind` — Bookkeeping: a valid snapshot is marked as a program paused mid-run, never a fresh not-yet-started one.
- `detachInvalidated_preserves_contextAgreement` — When cleanup unhooks sleepers whose meeting point has disappeared, the one-for-one agreement between sleepers and snapshots still holds afterward.
- `detachInvalidated_invalidated_exact` — A sleeper whose meeting point was destroyed is fully unhooked: its waiting record and active snapshot are removed, and that exact snapshot is set aside in a holding area for later revival.
- `detachInvalidated_retained_exact` — A sleeper whose meeting point survived is left exactly as it was: waiting record, snapshot, and holding-area entry all untouched.
- `drainDeferred_rejected_unchanged` — When returning a set-aside program to service is refused for any reason, nothing changes: not the kernel state, not the holding area, not the resume list.
- `drainDeferred_drained_exact` — A successful return does all of this in one step: it removes the entry from the holding area, marks the program able to run, puts it in the run queue, leaves it a "cancelled" receipt because its wait produced no message, and places its snapshot at the front of the resume list.
- `drainDeferred_drained_reserves_capacity` — Before a return succeeds, every fact is rechecked: the snapshot is valid, the program is alive and owns its memory space, no duplicate resume entry exists, and there is room in both the run queue and the resume list.
- `drainDeferred_drained_scheduler_exact` — A successful return changes the scheduler in exactly the standard wake shape — appended once to the run queue and marked able to run — and in no other way.
- `drainDeferred_drained_deferred_exact` — A successful return removes exactly the selected entry from the holding area and leaves every other set-aside program untouched.
- `drainDeferred_readyQueueFull_exact` — A refusal because the run queue is full can only happen after every validity and authority check has passed, and it leaves everything exactly as it was.
- `drainDeferred_resumableBankFull_exact` — A refusal because the resume list is full is checked last of all, and it too leaves everything byte-for-byte unchanged.
- `drainDeferred_preserves_deferredWellFormed` — Whether it succeeds or refuses, a return attempt keeps all records — active sleepers, the message system, and the holding area — consistent.
- `receive_preserves_wellFormed` — A receive attempt that saves a snapshot keeps both the message records and the snapshot records consistent, whatever the outcome.
- `send_preserves_wellFormed` — Every send keeps them consistent too, including when it wakes a sleeper and hands its snapshot back.
- `receive_contextRejected_unchanged` — A receive refused because the offered snapshot was bad, or because the caller already has one on file, changes nothing.
- `receive_ipcRejected_unchanged` — A receive refused by the underlying message layer changes nothing.
- `receive_blocked_exact` — When a receive puts the caller to sleep, the snapshot it stored had passed validation and is exactly the one now on file for the caller.
- `receive_delivered_ipc_exact` — When a message is delivered immediately, the state change is exactly the plain message layer's delivery; the snapshot layer adds nothing to it.
- `receive_delivered_blocked_unchanged` — An immediate delivery consumes only message data and leaves every saved snapshot untouched.
- `receive_blocked_ipc_exact` — When the caller goes to sleep, the message-layer change is exactly the plain layer's blocking step, published as-is rather than rebuilt.
- `receive_blocked_blocked_exact` — Going to sleep files exactly one new snapshot — the caller's — and every other program's snapshot stays exactly as it was.
- `send_rejected_unchanged` — Any send that is not accepted changes nothing at all.
- `send_accepted_unreleased_scheduler_unchanged` — A send accepted with nobody to wake simply parks the message in the mailbox and leaves the scheduler untouched.
- `send_accepted_unreleased_waiterEndpoint_unchanged` — Such a mailbox-only send also leaves every waiting record untouched.
- `send_accepted_unreleased_blocked_unchanged` — And it leaves every saved snapshot untouched.
- `send_accepted_ipc_exact` — Every accepted send at this layer is, underneath, exactly the plain message layer's accepted send.
- `send_released_exact` — When a send hands back a snapshot, that snapshot belonged to the program at the front of that meeting point's waiting line, the send really was accepted, and that program's snapshot slot is now empty.
- `send_released_blocked_exact` — Handing back a snapshot clears exactly that one receiver's entry and nobody else's.
- `cancel_preserves_wellFormed` — Cancelling a sleeper keeps message and snapshot records consistent, whatever the outcome.
- `cancel_rejected_unchanged` — A refused cancellation changes nothing.
- `cancel_cancelled_exact` — A successful cancellation hands back exactly the snapshot that was on file for the cancelled program, and its slot is now empty.
- `cancel_cancelled_ipc_exact` — A successful cancellation performs, underneath, exactly the plain message layer's cancellation, wake-up included.
- `terminate_blocked_self` — Once a program's termination is accepted, its saved snapshot is gone.
- `terminate_rejected_unchanged` — A refused termination changes nothing, so it can never strip a still-live sleeper of its snapshot.
- `terminate_accepted_cleans_self` — An accepted termination removes the dead program's waiting record and its snapshot in the same indivisible step — a dead program can linger in neither.
