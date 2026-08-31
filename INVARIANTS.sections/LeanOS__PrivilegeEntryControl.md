# One doorway into the kernel (privilege entry control)

A processor offers several instructions a program can use to jump into the kernel, and every extra one is an extra attack surface. These theorems establish that LeanOS leaves exactly one reviewed doorway open, the classic software-interrupt entry, and keeps every faster alternative switched off; a program that tries a disabled doorway is either safely denied and cleaned up, or the kernel halts entirely rather than guess. They also show the kernel re-checks this configuration before every sensitive operation, so a corrupted setting can never be silently ridden past.

- `validate_accepted_iff` — The quick configuration check the kernel runs answers yes exactly when the full written-out acceptance policy holds, no more and no less.
- `validate_total` — Bookkeeping: the configuration check always produces an answer on every possible input; it can never get stuck.
- `validate_deterministic` — Checking the same configuration twice always gives the same answer; there is no randomness or hidden state.
- `accepted_exactly_int80` — In any accepted configuration, exactly one system-call doorway is enabled, the reviewed software-interrupt entry, and both fast alternatives are provably switched off.
- `attacker_payload_erasure` — Whatever bytes an attacker attaches to a forbidden entry attempt make no difference at all: the kernel's decision is identical no matter what the payload says.
- `classify_total` — Bookkeeping: the routine that judges a forbidden entry attempt always reaches a verdict on every possible input.
- `classify_deterministic` — Judging the same entry attempt twice always yields the same verdict; there is no randomness or hidden state.
- `denied_subject_confined` — Whenever the kernel contains a forbidden entry attempt by denying one program, that program is exactly the one currently running, the configuration is accepted and freshly confirmed, the attempt came from user code on the trusted kernel stack, no alternate kernel target was ever executed, and the program's identity and address-space records all agree.
- `kernel_attempt_never_contained` — An attempt that originates inside the kernel itself is never handled by quietly denying a program; the kernel treats it as fatal instead.
- `alternate_target_never_contained` — If a disabled doorway somehow ran an alternate kernel destination, the situation is never treated as a routine denial; it is fatal.
- `user_stack_never_contained` — An entry attempt that arrived on a stack owned by user code is never treated as a routine denial; it is fatal, because that stack cannot be trusted.
- `already_fatal_absorbing` — Once the kernel has halted for a fatal entry-control failure, every further attempt changes nothing and simply reports that the system is already halted.
- `return_allowed_requires_single_entry` — The kernel authorizes a return to user code only for the current program, only under an accepted configuration freshly confirmed against the live hardware, and only when that program's identity records all line up.
- `compositeGate_published_requires_single_entry` — No kernel operation of any kind can publish a result unless the single-doorway configuration is accepted and matches the live hardware reading at that moment.
- `accepted_composite_user_return_requires_single_entry` — In particular, an accepted return to user code through the main operation gate is only possible when the single-doorway configuration holds; a stepping-stone restatement of the previous theorem for that specific case.
- `compositeGate_preserves_policy` — Passing any single operation through the main gate keeps the single-doorway configuration intact; no operation can loosen it.
- `runComposite_preserves_policy` — Running any finite sequence of operations, however long, still leaves the single-doorway configuration intact at the end.
- `controlDemo_refines_scalar_all_inputs` — Bookkeeping: the small numeric routine exported for the real build gives exactly the same answer as the reference version, on every possible input.
- `canonical_control_adapter_accepts` — A concrete worked example: fed the one correct boot configuration, the exported check accepts.
- `contained_syscall_adapter_binds_authoritative_subject` — A concrete worked example: a forbidden fast-entry attempt of the first kind is denied and the denial names exactly the currently running program.
- `contained_sysenter_adapter_binds_authoritative_subject` — A concrete worked example: a forbidden fast-entry attempt of the second kind is likewise denied and pinned on exactly the currently running program.
- `denial_cleanup_cannot_resume` — After the kernel cleans up a program it denied, that program is gone for good: it holds no rights, waits in no queue, is not the running program, and has no saved state from which it could ever resume.
