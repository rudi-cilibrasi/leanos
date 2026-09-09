# Binding the J1900 CPU to its control readback

The J1900 control check combines the measured CPU capabilities with the expected Intel fast-entry and extended-state controls. It checks the supplied observations, including whether initialization and readback completed. It does not establish the missing SMAP isolation policy or authorize entry to user mode.

- `validate_normalized_iff` — The executable check succeeds exactly when the CPU snapshot passes the J1900 selector and the complete supplied control state matches the expected tuple.
- `normalized_disables_fast_entry` — A matching tuple disables both SYSCALL and SYSENTER in the finite entry-control model.
- `normalized_requires_completed_readback` — A matching tuple requires both initialization and readback to be recorded as complete; coincidental register values with either observation missing cannot pass.
- `raw_readback_requires_denied_msrs` — Every passing raw Intel MSR snapshot maps to the exact disabled fast-entry register state used by the entry-control model.
