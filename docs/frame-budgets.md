# Admitted per-subject frame budgets

`LeanOS.FrameBudget` is a finite, sequential reference model that wraps the
authoritative `MemoryLifecycle.State`. At boot, trusted policy commits each
budgetable physical frame to zero or one subject with a frame-to-subject
function. The model does not keep a second allocator or infer charge from a
capability holder: the physical allocator still records the memory-object
owner, while the immutable commitment records the charging subject.

Budgetable frames are allocator-enumerated, non-reserved frames selected by the
boot admission policy. Firmware-reserved, boot/kernel, page-table, stack,
capability-table, IPC-buffer, DMA, and other unmodeled metadata frames are not
charged by this slice. `WellFormed` requires each commitment to name a modeled
non-reserved frame and an issued subject, every live binding to use one such
commitment, and every allocator-owned object to have its authoritative live
binding. Because commitment is a function, a frame cannot be admitted to two
subjects. `usage` is derived by enumerating owned frames in the subject's fixed
partition; there is no cached usage counter to drift or mint credit.

## Operations and exhaustion

`allocate` receives the charging subject from trusted kernel context. The
caller supplies only the fresh object identity and that same subject's
generation-bounded capability slot. Allocation deterministically selects the
first free committed frame. A subject with no such frame receives typed
`budgetExhausted`; every rejected operation preserves the complete budget and
memory state. This is distinct from capability identity exhaustion, invalid or
occupied slots, and stale subjects. In an admitted state, peer allocations can
never consume this subject's partition, so a valid allocation with an available
committed frame succeeds even if another subject is at its limit.

`release` uses the existing generation-checked capability lookup and
memory-object retirement path. It frees the allocator frame but does not alter
the immutable commitment, so exactly one unit becomes reusable by its admitted
subject. Stale and repeated release restore nothing. Whole-subject termination
enumerates that subject's committed frames, retires all corresponding live
objects and delegated aliases, frees each owned frame once, marks the subject
dead, and preserves both object/subject issued histories. Repeated termination
is state-preserving. A reused frame still enters a fresh never-reused object
lifetime; publication must continue through the existing scrub-before-use
boundary. This model does not bypass virtual-mapping or TLB lifetime checks.

Capability delegation neither transfers nor duplicates charge. A delegated
holder can exercise attenuated authority, but usage remains assigned to the
subject whose partition contains the backing frame. Ownership transfer and
budget reassignment are outside this issue.

## Machine-checked properties and traces

- `usage_le_limit` and `commitments_disjoint` establish the finite bound and
  exclusive admission partition.
- `allocation_charge_confined` proves accepted allocation binds and assigns a
  frame committed to the trusted subject; no object word or holder can redirect
  the charge.
- `allocation_other_usage_unchanged` proves allocation leaves every peer's
  usage unchanged.
- `available_allocation_accepted` is the advertised isolation result: valid
  object/slot inputs and one available committed frame imply acceptance.
- rejection atomicity covers allocation, release, and termination;
  `termination_frees_charged_frame` and
  `termination_preserves_other_frame` express cleanup conservation.

Executable regressions cover zero-, one-, and multi-frame budgets, independent
two-subject exhaustion, wrong trusted subject, out-of-range and occupied slots,
over-budget retry, release/reallocation, stale release, delegated authority,
multi-object termination, repeated termination, and corrupted
allocator/binding coherence.

## Complexity and proof boundary

Budget and allocation scans are O(F) in modeled allocator frames. Termination
also scans the terminated partition and uses a finite retired-object list when
filtering bindings and capabilities; the functional maps are mathematical
model representations, not a concrete kernel data structure.

The theorems apply only to the named Lean state and sequential transitions.
There is no refinement theorem to generated C, boot code, the broader composite
runtime gate, QEMU, compiler/linker output, firmware, or hardware. Admission is
a trusted fixed Phase 2 boot-policy input; the model checks its structural
invariant but does not prove firmware capacity or implementation installation.
Dynamic admission, reassignment, overcommit, swap, concurrency/SMP, fairness,
timing availability, production OOM policy, and the following emulator scenario
are excluded. The existing compiler/runtime/boot/hardware TCB boundary remains
unchanged.
