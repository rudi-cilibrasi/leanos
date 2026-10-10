# Old capability handles stay dead forever

This section shows that a handle naming something an ended child held or owned keeps failing after any later sequence of kernel steps, spawn operations, and memory operations, because capability numbers are never handed out again.

- `allocatedState_identityStep` — An allocation hands out exactly one brand-new capability number.
- `releasedState_identityStep` — A release only removes capabilities and pending transfers.
- `memoryGate_identityStep` — Every memory operation, in every outcome, hands out only brand-new capability numbers.
- `ChildTraceStep.identityStep` — Every step of a run, from a well-formed state, hands out only brand-new capability numbers.
- `runChildSteps_identityStep` — Along a whole run, every capability number at the end was there at the start or is brand new.
- `stale_word_forever` — After a parent ends a child, a handle that named something the child held or owned fails for every subject and kind after any later run.
