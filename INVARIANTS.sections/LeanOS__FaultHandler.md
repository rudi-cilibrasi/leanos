# A fault handler program for one kind of fault

When a program crashes on a fault, the kernel normally ends it and runs the next program in line. This module adds one optional alternative, fixed when the machine starts: for one kind of fault raised by one named program, a second, named handler program is told about the fault instead. The crashed program is put on hold, the handler receives a small fixed record describing the fault (which kind, which program, where it happened, and the hardware's error number) and nothing else, and the handler's only possible answer is "end it", which ends the program in exactly the normal way. These theorems guarantee that without such a handler nothing changes, that the handler learns only that record and gains none of the crashed program's permissions, that the crashed program never runs again, and that no other program ever receives a fault record.

- `unbound_is_default` — With no handler set up, a fault is handled exactly as before, with the same result and the same effect on the system.
- `unbound_class_is_default` — Even with a handler set up, a fault of a different kind, or one raised by a different program, is handled exactly as before.
- `fault_default_or_delivered` — Every fault either takes the usual path unchanged or is handed to the handler; there is no third outcome.
- `boundFor_some` — The handler applies to a fault only when it is the configured kind from the configured program, and the record it would receive is built directly from that fault.
- `delivered_exact` — When a fault is handed to the handler, it was the configured kind from the configured program, which was running normally; that program is put on hold and taken out of the run queue, the handler's inbox holds exactly the fault record, no other inbox changes, and permissions, saved states and memory views are untouched.
- `record_fields_only` — The fault record depends only on the fault's kind, the program, the fault location and the error number, so nothing else about the crashed program can leak through it.
- `delivered_no_amplification` — Handing a fault to the handler leaves every program's permissions exactly as they were.
- `receive_core` — Collecting a fault record from an inbox changes nothing else in the system.
- `received_own_inbox` — A program collecting a fault record only ever gets the record in its own inbox.
- `reply_terminates` — When the handler answers "end it", exactly the program on hold is ended in the normal way: it is no longer alive, not waiting to run, not running, has no saved state to resume from, and nothing remains on hold.
- `reply_other_rejected` — An answer from any program other than the configured handler is refused and changes nothing.
- `reply_no_amplification` — Ending the program on hold only ever removes permissions; nobody, including the handler, gains a permission they did not already have.
- `fault_preserves_binding` — Handling a fault never changes which program is the configured handler.
- `receive_preserves_binding` — Collecting a fault record never changes which program is the configured handler.
- `reply_preserves_binding` — Answering a fault never changes which program is the configured handler.
- `step_preserves_binding` — No step of this mechanism changes the handler configuration set at start-up.
- `step_preserves_inboxBound` — Only the configured handler ever has a fault record waiting, and every step keeps it that way.
- `received_only_by_handler` — Any program that actually receives a fault record is the configured handler.
- `faultHandlerRoute_agrees` — The small numeric checker the running kernel consults gives exactly the model's answers for the demonstrated fault, for faults it must leave on the usual path, and for the handler's answer and the refused answers.
- `unbound_witness_is_containment` — In the example system with no handler, the divide-by-zero fault is handled exactly as before: the faulting program is ended and the next one runs.
- `witness_delivery` — In the example system, the divide-by-zero fault is handed to the handler with exactly the expected record, the faulting program is put on hold, and no other program receives anything.
- `witness_terminate` — In the example system, the handler's answer ends the faulting program while the surviving program keeps its permission.
