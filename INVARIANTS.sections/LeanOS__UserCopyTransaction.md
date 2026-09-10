# Copy transaction termination

This abstract contract composes whole-request validation with partial-copy effects. It assumes entry under an established closed root and stable authority. Cleanup verification is a report from a future trusted root-switch and invalidation boundary, not a property verified by this model.

- `finish_returned_iff` — Normal return requires a verified-closed report, a finished stop, and exactly the requested progress.
- `returned_requires_contract` — A transaction can return normally only after successful whole-request validation and the complete finish contract.
- `rejected_memory_unchanged` — Rejected validation changes no memory.
- `cleanup_failure_terminal` — After successful validation, unverified cleanup terminates and remains explicitly unverified in the outcome.
- `exceptional_stop_terminal` — An interrupted or faulted transaction terminates, even when cleanup succeeds.
- `wrong_progress_terminal` — Incomplete or excessive progress cannot produce a normal return.
- `preserves_authority` — No transaction outcome changes mapping, ownership, or allocation authority.
- `to_effects` — Copy-to effects are precisely the observed prefix, regardless of stop or cleanup outcome; termination does not roll back writes.
- `from_effects` — Copy-from effects are precisely the observed prefix, regardless of stop or cleanup outcome.
