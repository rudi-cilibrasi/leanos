# The kernel's first response to interrupts, and its gate back to programs

This file models the kernel's very first reaction when the processor is interrupted — a program crashes, a timer ticks, or a program asks for a service — plus the strict checklist the kernel runs before ever letting a program resume running. Its theorems guarantee that only trusted hardware-supplied facts, never a program's own register contents, decide what the kernel does; that a crashing program is terminated without touching anyone else's memory, permissions, or messages; and that a return into a user program is approved only after every safety check on the list passes.

- `accepted_attests_exact_request` — When the return-to-program checker approves a request, the approval it hands back is exactly the request it examined, so an approval can never be quietly attached to a different request.
- `accepted_user_return_context_confined` — An approved return carries proof of every check at once: an allowed purpose, a machine that is running rather than halted, a saved frame that genuinely came from a user program with the correct code and stack selectors and well-formed addresses, only permitted processor flags, a subject that is alive, runnable, current, and the owner of the address space being entered, a matching page-table root, and a jump target and stack that both lie inside that program's own memory.
- `diagnostic_recovery_never_authorizes_user_return` — A request labeled as internal kernel diagnostic recovery is always refused; that purpose can never be used to jump back into a user program.
- `oracleModelAccepts_iff` — Bookkeeping: the simple yes/no test wrapper answers yes exactly when the full checker approves the request unchanged.
- `userReturnDemo_accepts_reviewed_purposes` — A worked example confirming that the three approved reasons to enter a program — first launch, resuming after a system call, and a scheduler restore — are accepted by both the simplified test adapter and the full model.
- `userReturnDemo_rejects_mutated_consumption` — A worked example confirming that if the return address is tampered with after approval, the final consumption step refuses it in both the test adapter and the full model.
- `decodeVector_deterministic` — Translating an interrupt number into its meaning always gives one answer; the same number can never be read two different ways.
- `attacker_registers_cannot_change_dispatch` — The values a program left in its general-purpose registers have no influence at all on how the kernel classifies and handles an interrupt.
- `dispatchHardware_preserves_trusted_context` — Handling an interrupt never alters the kernel's trusted context: which subject is current, which address space is active, the kernel stack, and the already-in-the-kernel flag all stay exactly the same.
- `attacker_registers_cannot_change_trusted_context` — Putting the two facts above together: nothing a program leaves in its registers can change the kernel's trusted context through interrupt handling.
- `dispatch_preserves_invariant_or_fatal` — Every interrupt either leaves the kernel's bookkeeping healthy and consistent or ends in a deliberate full stop — never a silently corrupted in-between state.
- `user_page_fault_contained` — A memory fault raised by a user program is contained: the kernel terminates exactly the current subject and nothing else.
- `kernel_page_fault_is_fatal` — A memory fault arising inside the kernel itself is treated as fatal; the kernel stops rather than guessing at recovery.
- `unsupported_vector_is_fatal` — An interrupt number the kernel does not recognize is treated as fatal, never improvised around.
- `timer_preserves_state` — A timer tick changes nothing: the kernel notes the tick and leaves every piece of state exactly as it was.
- `kernel_syscall_has_wrong_origin` — A system call that appears to come from inside the kernel rather than from a user program is rejected as having the wrong origin.
- `contained_fault_terminates_only_current_memory` — When a faulting program is terminated, memory owned by any other subject is left exactly as it was.
- `contained_fault_preserves_unrelated_authority` — Terminating a faulting program leaves another subject's permission entries untouched, provided they do not point at the terminated program's resources.
- `contained_fault_preserves_unrelated_mapping` — Memory mappings in address spaces owned by other subjects are unchanged when a faulting program is terminated.
- `contained_fault_preserves_unrelated_frame` — Physical memory pages owned by another subject keep both their owner and their free-or-used status when a faulting program is terminated.
- `contained_fault_preserves_unrelated_endpoint` — Another subject's communication endpoint keeps its owner when a faulting program is terminated; only a pending message that the terminated program itself sent gets discarded.
- `syscall_entry_requires_user_origin` — Whenever the kernel treats an event as a system call, that event genuinely came from a user program.
- `syscall_preserves_trusted_subject` — Handling a system call never changes which subject the kernel considers current.
- `fatal_cannot_be_syscall` — Bookkeeping: an outcome classified as fatal is never simultaneously classified as a system call.
