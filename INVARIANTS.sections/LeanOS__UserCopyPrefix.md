# Interrupted copy prefixes

This sequential model applies a completed prefix only after validating the entire request. It does not implement copy-window entry, root cleanup, interrupt handling, or resumption. Partial writes remain visible; rollback is not promised.

- `rejected_unchanged` — Failed whole-request validation leaves all state unchanged, regardless of the supplied progress count.
- `zero_progress_unchanged` — Interrupting before the first byte leaves the entire state unchanged.
- `preserves_kernel` — Copy-to progress never changes any kernel buffer.
- `preserves_authority` — Copy-to progress never changes the modeled mappings, ownership, or allocation authority.
- `outside_prefix` — Every physical byte outside the completed destination prefix keeps its original value, including uncompleted destinations when they do not alias a prefix byte.
- `complete_agrees` — At or beyond the requested length, the prefix model produces exactly the existing complete copy-to state; progress saturates at the request length.

- `from_rejected_unchanged` — Copy-from validation failure leaves the entire state unchanged regardless of progress.
- `from_zero_progress_unchanged` — Zero completed read bytes leave the entire state unchanged.
- `from_preserves_user` — Copy-from progress never modifies user memory.
- `from_preserves_authority` — Copy-from progress never changes mappings, ownership, or allocation authority.
- `from_outside_prefix` — Copy-from preserves all other kernel buffers and every destination byte at or beyond the completed prefix.
- `from_validated_exact` — Copied values are exactly the validated source prefix in its original order.
- `from_complete_agrees` — Full or excessive read progress agrees with the existing complete copy-from operation.
