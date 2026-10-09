# Kernel invariants split by the state parts they read

The global runtime guarantee is a long list of separate promises. Each promise here is stated together with the parts of the kernel state it reads, and a proof that it reads nothing else. A step that does not write any of those parts keeps the promise automatically, so adding a new part of the kernel state with its own promise only needs new proofs for the operations that actually write that part.

- `ProjectionInvariant.untouchedBy_untouched` — Bookkeeping: if a step's declared write set misses every part a promise reads, then the step leaves each of those parts unwritten.
- `ProjectionInvariant.preserved_of_frames` — A step that leaves every part a promise reads untouched keeps that promise, with no proof specific to the step.
- `ProjectionInvariant.All.preserved_of_frames` — A step keeps a whole list of promises as soon as the promises reading something it writes are proved again; all the others carry over automatically.
- `ProjectionInvariant.all_append` — Bookkeeping: holding every promise of two joined lists is the same as holding every promise of each list.
- `runtimeWellFormed_iff_all` — The global runtime guarantee is exactly its fourteen separately stated promises, each with the parts of the kernel state it reads.
- `runtimeWellFormed_preserved_of_frames` — A step that respects a declared write set keeps the global runtime guarantee once the promises reading something it writes are proved again; every other promise carries over automatically.
- `runtimeWellFormed_preserved_of_untouched` — A step whose declared write set misses everything the global runtime guarantee reads keeps that guarantee with no further proof.
- `gate_preserves_projectionInvariant` — Every outcome of the ordinary kernel gate keeps any separately stated promise whose parts the operation does not write.
- `gate_preserves_authorityInvariant` — Every outcome of the ordinary kernel gate keeps the device-port controls and the device-access quarantine promise, derived from the frame rule alone.
