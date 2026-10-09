# Preemption and interrupts keep the kernel consistent

These theorems cover timer preemption that saves one program and resumes another, and hardware interrupts that are fatal, contained to one faulting program, or ordinary. Each case either preserves the global runtime invariant or halts the machine cleanly.

- `schedulerSelectNext_preserves_capabilities` — Bookkeeping: picking the next program never changes the permission store.
- `schedulerTick_preserves_capabilities` — Bookkeeping: a scheduler tick never changes the permission store.
- `resumeSwitch_preserves_capabilities` — Bookkeeping: a full save-select-restore switch never changes the permission store, whatever its outcome.
- `resumeSwitch_preserves_virtualMemory` — Bookkeeping: a save-select-restore switch never changes the authoritative virtual-memory records.
- `resumeSwitch_halted_preserves_scheduler` — Bookkeeping: if a switch ends in the halt latch, the scheduler is left exactly as it was.
- `installResumable_nonfatal_preserves_runtimeWellFormed` — Publishing a non-fatal switch result preserves every kernel record: the switch machinery owns the scheduler and translation updates, and authority, mailboxes, and transfers are untouched.
- `gate_resumePreempt_nonfatal_preserves_runtimeWellFormed` — Every non-fatal preemption step, whether a real switch or any of its refusals, preserves the whole-kernel guarantee; attacker-supplied frame and register contents cannot desynchronize the kernel's record of who is running.
- `resumeSwitch_halted_requires_fatal_dispatch` — A stepping-stone fact used by later theorems: the only way a switch can land in the halt latch is that the interrupt itself was classified as fatal.
- `resumeSwitch_halted_state_eq` — A stepping-stone fact used by later theorems: when a switch halts, the result is exactly the old switch state with the halt latch set and nothing else moved.
- `fatalInterrupt_dispatchHardware_halts` — A stepping-stone fact used by later theorems: a fatally classified interrupt always drives the execution latch into halted mode with a diagnostic record.
- `dispatchHardware_preserves_wellFormed_internal` — A stepping-stone fact used by later theorems: hardware interrupt entry keeps the execution latch's own records consistent in every mode.
- `dispatchHardware_fatal_halts` — Whenever interrupt entry reports a fatal outcome, the execution latch really is left halted with a diagnostic record.
- `interruptDispatch_ordinary_state` — Bookkeeping: a timer, system-call, or rejected interrupt classification leaves the low-level interrupt state untouched.
- `dispatchHardware_ordinary_state` — Bookkeeping: an ordinary interrupt entry (timer, system call, or rejection) changes nothing except switching off the transient return and copy permissions.
- `closeCopyWindow_preserves_runtimeWellFormed` — Closing the kernel-owned copy window changes nothing the whole-kernel guarantee cares about.
- `clearInboundAuthority_preserves_runtimeWellFormed` — Finishing an ordinary interrupt clears the transient return and copy permissions without touching any authoritative subsystem state.
- `installResumable_fatal_preserves_runtimeWellFormed` — A stepping-stone fact used by later theorems: publishing a fatal entry, a halted execution latch together with the halt bit on the switch machinery, preserves the whole-kernel guarantee.
- `gate_resumePreempt_fatal_preserves_runtimeWellFormed` — A fatal entry during preemption latches the same fail-stop mode used everywhere else while freezing the scheduler, saved contexts, translations, messaging, and authority exactly.
- `resumePreempt_operationPreservesRuntimeWellFormed` — Preemption preserves the guarantee in all four cases: a successful switch, a refusal with a reason, fatal latching, and busy-or-halted absorption.
- `gate_resumePreempt_accepted_flushes_translations` — An accepted switch of the active address root preserves the guarantee and empties the translation cache, matching the full flush required on hardware without per-address-space cache tags.
- `publishInterruptCleanup_preserves_runtimeWellFormed` — A stepping-stone fact used by later theorems: the interrupt path's cleanup publisher, which retires the faulting program and then closes the copy window, preserves the whole-kernel guarantee.
- `interrupt_operationPreservesRuntimeWellFormed` — Every normalized hardware interrupt preserves the guarantee: contained user faults reuse the authoritative termination cleanup, fatal entries set both halt records together, and ordinary entries only clear transient permissions, with no branch quietly repairing anything else.
