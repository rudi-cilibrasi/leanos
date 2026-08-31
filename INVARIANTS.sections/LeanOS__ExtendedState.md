# Denying user programs the floating-point and vector units

Until the kernel can manage floating-point and vector-math state per program, it locks those instruction families (x87, MMX, SSE, AVX) away from user programs entirely. These theorems guarantee that the lock-out policy is checked exactly, that a trapped instruction is always blamed on the correct, freshly verified program, that the offending program is completely removed and can never run again before a legitimately scheduled peer takes over, and that the compact numeric decision procedure handed to the machine boundary agrees with the full model.

- `validatePolicy_accepted_iff` — The policy check passes exactly when the processor-feature snapshot is internally consistent and the control settings are precisely the intended lock-everything-out configuration, never for any other combination.
- `validatePolicy_total` — Bookkeeping: the policy check always produces an answer, accept or reject, for every input.
- `validatePolicy_deterministic` — Bookkeeping: running the policy check twice on the same input always gives the same answer.
- `attacker_payload_erasure` — Any extra words an attacker attaches to a trap event are completely ignored: classification with one payload gives exactly the same outcome as with any other.
- `classify_total` — Bookkeeping: classifying a trap event always produces an outcome, no matter what the state or event looks like.
- `classify_deterministic` — Bookkeeping: classifying the same event in the same state twice always gives the same outcome.
- `denied_subject_confined` — Whenever the kernel contains a denied instruction, the program it blames is exactly the one currently running, the event came from a user program rather than the kernel, and the denial policy and the current address-space ownership record were all verified live at that moment.
- `kernel_attempt_never_contained` — An event originating inside the kernel itself is never treated as a routine contained denial; it can only be handled as a fatal error.
- `policy_mismatch_never_contained` — Whenever the live control settings fail the policy check, no event whatsoever can be handled as a routine contained denial.
- `already_fatal_absorbing` — Once the system has latched into its fatal halt, every further event is answered with the same halted report and changes nothing.
- `return_allowed_requires_denial` — The gate that lets a user program resume can approve only the current program, and only while the denial policy and the address-space ownership record are still intact.
- `compositeGate_total` — Bookkeeping: the whole-system gate always produces an outcome for every operation.
- `compositeGate_deterministic` — Bookkeeping: the whole-system gate gives the same outcome every time for the same state and operation.
- `compositeGate_policy_mismatch_atomic` — Whenever the live policy check fails, the whole-system gate halts with only its halt latch set; no subsystem is left partially changed.
- `compositeGate_published_requires_denial` — Any result the whole-system gate actually publishes, of any kind, is possible only while the exact lock-out policy holds.
- `accepted_composite_user_return_requires_denial` — In particular, an accepted return to a user program through the whole-system gate is possible only while the exact lock-out policy holds.
- `compositeGate_preserves_policy` — Once the lock-out policy holds, no modeled operation of any kind (system call, timer, message, mapping, scheduling, and so on) can ever break it.
- `runComposite_preserves_policy` — The lock-out policy also survives any sequence of modeled operations, however long, run one after another.
- `dispatchDenied_total` — Bookkeeping: handling a denial always produces an outcome.
- `dispatchDenied_deterministic` — Bookkeeping: handling the same denial in the same state twice always gives the same outcome.
- `denial_cleanup_cannot_resume` — After cleanup, the faulting program is no longer a recognized program, is not waiting in the ready queue, is not the current program, and has no saved context left, so it can never resume in any way.
- `dispatched_peer_is_scheduler_selected` — Whenever a denial hands the processor to another program, that program is exactly the one the scheduler picked after cleanup, restored from its own kernel-held saved context and matching address space.
- `dispatchDenied_fatal_atomic` — Whenever denial handling ends fatally, the system state is exactly the pre-existing state with only the halt latch set; no partial cleanup is ever exposed.
- `denialDispatchModel_nm_refines_authoritative` — On the reviewed trap case for an available floating-point instruction, the compact machine-boundary number equals exactly what the full cleanup-and-dispatch model computes.
- `denialDispatchModel_ud_refines_authoritative` — On the reviewed invalid-instruction trap case, the compact machine-boundary number equals exactly what the full cleanup-and-dispatch model computes.
- `denialDispatchModel_corrupt_context_fails_closed` — On the reviewed case where the peer's saved context is missing, both the compact version and the full model refuse to dispatch, agreeing exactly.
- `denialDispatchModel_empty_queue_refines_idle` — On the reviewed case where no other program is ready, both the compact version and the full model clean up and go idle, agreeing exactly.
- `denialMachineGate_refines_composite_policy_all_inputs` — For every possible input, the machine-boundary gate applies the halt latch and the live policy check in exactly the same order as the whole-system wrapper before allowing any dispatch.
- `denialMachineGate_policy_mismatch_fails_closed` — Whenever the policy word is anything other than the single live value, the machine-boundary gate publishes nothing at all.
- `denialMachineGate_live_policy_publishes_exact_dispatch` — With the live policy word, the machine-boundary gate's output is exactly the dispatch decision, nothing added and nothing removed.
- `denialDispatchDemo_refines_machine_gate_all_inputs` — Spelling out the definition: the exported demonstration function is, for every input, literally the machine-boundary gate.
