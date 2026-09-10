# Interrupted copy-to prefixes

This sequential model applies a completed prefix only after validating the entire request. It does not implement copy-window entry, root cleanup, interrupt handling, or resumption. Partial writes remain visible; rollback is not promised.

- `rejected_unchanged` — Failed whole-request validation leaves all state unchanged, regardless of the supplied progress count.
- `zero_progress_unchanged` — Interrupting before the first byte leaves the entire state unchanged.
- `preserves_kernel` — Copy-to progress never changes any kernel buffer.
- `preserves_authority` — Copy-to progress never changes the modeled mappings, ownership, or allocation authority.
- `outside_prefix` — Every physical byte outside the completed destination prefix keeps its original value, including uncompleted destinations when they do not alias a prefix byte.
- `complete_agrees` — At or beyond the requested length, the prefix model produces exactly the existing complete copy-to state; progress saturates at the request length.
