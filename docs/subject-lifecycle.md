# Subject lifecycle model

`LeanOS.SubjectLifecycle` is a finite, sequential model of trusted subject
creation and termination. Subject identifiers have append-only issued history:
once terminated, an identifier cannot become live again.

Termination is atomic in the model. It removes every capability held by the
subject; retires its exclusively owned memory and endpoint objects (including
capabilities delegated to other subjects); frees owned frames; removes owned
address spaces and mappings; clears endpoint mailboxes owned by, or containing
provenance from, the subject; and removes the subject from current and runnable
state. A capability held by another subject for an object not owned by the
terminated subject is preserved. Repeated termination and identifier replay
are typed, state-preserving rejections.

The Lean proofs establish rejection stability, stale lookup denial, complete
cleanup of the modeled resources, preservation of unrelated memory ownership,
and non-reuse of issued identity. Executable examples cover delegated
authority, a live mapping, a pending message, termination of the current
subject, repeated termination, and identifier replay.

This is not executable ring-3 teardown and does not prove physical memory
zeroization. The trusted caller is the kernel lifecycle operation itself;
authorization policy for a future management capability is outside this first
model. Concurrency, scheduling fairness, destructors, generated code, and the
machine implementation remain outside the proved claim.
