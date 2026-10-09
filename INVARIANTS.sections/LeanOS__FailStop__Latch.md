# The kernel's fail-stop latch: one irreversible halt

This file models the kernel's "fail-stop" rule for entering and leaving the kernel: on any fatal error (a forbidden nested interrupt, an emergency hardware signal, a corrupted return to a program) the kernel latches into a permanent halt that absorbs every later event, rather than limping on in an unknown condition. It is the first piece of the fail-stop core, which is split across the `LeanOS/FailStop/` files and re-exported as one model by `LeanOS/FailStop.lean`.

- `latchNmi_preserves_wellFormed` — Whenever the kernel latches a halt in response to an emergency hardware signal, its internal consistency check still passes: program records are untouched, permission to return to a program is switched off, and the busy flag is set in the same single step as the halt record.
- `dispatchNmi_preserves_wellFormed` — Handling an emergency (non-maskable) interrupt always leaves the kernel's core consistency check intact, no matter which branch of the handler runs.
- `dispatchNmi_core_lifecycle` — Bookkeeping: handling an emergency interrupt never changes the kernel's records of which programs exist and what they own.
- `dispatchNmi_currentSubject` — Bookkeeping: handling an emergency interrupt never changes which program the kernel considers current.
- `dispatchNmi_activeAddressSpace` — Bookkeeping: handling an emergency interrupt never changes which memory space is active.
- `dispatchNmi_nonhalted_halts` — Whenever an emergency interrupt arrives while the kernel is not already halted, the kernel ends up halted with a recorded reason.
- `dispatchNmi_nonhalted_disarms` — Whenever an emergency interrupt arrives while the kernel is not already halted, permission to return to a user program is switched off.
- `accepted_nmi_terminal` — An emergency interrupt that passes the kernel's checks halts the machine with an exact diagnostic record while leaving every program record, current-program marker, memory-space marker, and return-policy field exactly as it was, except that return permission and the kernel copy window are closed.
- `halted_nmi_absorbing` — Once the kernel has halted, a later emergency interrupt changes nothing: it simply reports the original halt record.
- `selectReturnAuthority_core` — Bookkeeping: choosing the return policy for the next return to a program never touches the kernel's core interrupt state.
- `selectReturnAuthority_mode` — Bookkeeping: choosing the return policy never changes whether the kernel is running, busy, or halted.
- `selectReturnAuthority_returnPlan` — Bookkeeping: choosing the return policy never changes the installed page-table plan.
- `selectReturnAuthority_returnAddressSpace` — Bookkeeping: choosing the return policy never changes the kernel's stored views of program memory layouts.
- `selectReturnAuthority_wellFormed` — Choosing the return policy keeps the kernel consistent: the policy is armed only when the current program's identity, liveness, and memory ownership all check out against the kernel's own records.
- `latchInvalidUserReturn_preserves_wellFormed` — Rejecting a bad outgoing return to a program and latching the halt preserves the kernel's consistency check; program records and the bound return policy are unchanged, and the halt is recorded exactly as terminal mode requires.
- `accepted_user_return_is_atomic` — When a proposed return to a program passes validation, the kernel accepts it without changing any state at all.
- `rejected_user_return_latches` — When a proposed return to a program fails validation, the kernel halts with a record naming the purpose and reason, leaves the program records untouched, and closes the kernel copy window.
- `halted_user_return_absorbing` — Once halted, the kernel answers any further return attempt with the original halt record and changes nothing.
- `accepted_user_return_uses_authority` — An accepted return uses exactly the purpose, page-table root, and code and stack memory regions from the kernel's own policy record; a program's proposal cannot substitute its own.
- `accepted_user_return_has_bound_authority` — A return can be accepted only when the kernel's return policy was genuinely bound to the live current program and its installed memory view.
- `accepted_user_return_requires_running` — A return can be accepted only while the kernel is in its normal running state, never while busy with an entry or after a halt.
- `accepted_user_return_state_unchanged` — An accepted outgoing return changes nothing: it merely certifies the kernel-normalized request.
