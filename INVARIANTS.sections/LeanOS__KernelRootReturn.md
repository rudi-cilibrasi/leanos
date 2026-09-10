# Closed-root preparation and terminal return tail

The return composition keeps the currently active closed root separate from the
pending subject root. It reuses the existing lifecycle and frame validator, then
plans a mandatory root reload. Actual root construction, immutable storage,
machine reload verification, exception cleanup and IRET remain external obligations.

- `terminal_absorbing` — No event leaves the terminal return state.
- `interruption_terminal` — Interruption terminates every phase rather than resuming a pending return.
- `failed_reload_terminal` — A failed root reload terminates every phase.
- `user_requires_iret` — The tail can reach user mode only by completing IRET from the phase that awaits it.
- `iret_requires_reload` — The phase awaiting IRET can be reached only by reporting a verified reload from the initial tail phase.
- `preparation_requires_closed` — Accepted preparation requires the selected closed root to be active, maskable interrupts disabled, and PCID and global pages disabled.
- `step_preserves_plan` — Every tail step retains the exact plan, without replacing its frame or target-root authority.
- `prepared_request_validated` — A prepared request is attested by the existing user-return validator.
- `prepared_request_exact` — Preparation preserves the exact request presented to that validator.
- `prepared_publication` — Preparation preserves the original state in the plan, selects the requested root, requires a reload and plans an empty translation cache.
