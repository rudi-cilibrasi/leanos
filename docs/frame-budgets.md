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
The generated scenario gives the exact accepted termination and release edges
distinct full-state tokens with typed `RetirementEffect.flush` meaning. Every other
state/command pair returns zero. The machine path may publish released capacity
or scrub/reuse the frame only after the corresponding no-PCID full-cache action
completes.

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

## Generated and QEMU vertical slice

`LeanOS.FrameBudgetScenario` adds a fixed eight-edge sequence to the existing
`CompositeDispatcher.dispatch` ABI. It composes the authoritative
`FrameBudget.State` with the existing `FrameScrub.State`; current subject and
active address space are kernel-selected fields, and no command carries a
subject, budget, frame, object identity, expected result, or next owner. The sequence proves A's retry
is the typed `budgetExhausted` result with the complete state unchanged, B's
first allocation remains accepted, termination restores exactly A's one
charged frame, and physical frame 100 retains A's canary through reclamation
before B's publication scrubs every byte and installs never-reused identity 3.
Resolving A's old identity-1 word in B's current capability space is denied as
a stale generation. The canonical corpus includes every pre-state token, command, typed
reply, next-state token, and hostile replay/forgery encodings.

The same module now wraps the authoritative termination/reclamation step in
`RetirementPublication`. `prepareRetirement` computes the existing budget and
scrub successor but retains the complete published pre-state, so model frame 0
and scrub frame 100 remain owned by object 10 and A's old mapping remains
visible while the flush is pending. Only `acknowledgeRetirement` with the exact
termination token exposes the released capacity and reclaimed frame; the
explicit-release token is rejected even though it also denotes a full flush.
`publishFreshAfterRetirement` is disabled before that acknowledgement and then
reuses the existing allocation transition, whose `FrameScrub.Fresh` proof
establishes the complete scrub before object 21 and B's fresh mapping appear.
This is a bounded model ordering theorem over the shared issue-112 state, not a
proof of machine flush completion.

`LEANOS_BOOT_SCENARIO=frame-budget ./scripts/run-image.sh` runs the separate
version-20 QEMU transcript. Both subjects enter CPL3 under their checked roots.
The C bridge retains the generated canonical state token, the generated
Multiboot decoder's next eligible unpublished physical-frame number, and the
generated mapping-page result—not quota, usage, allocation, identity, mapping,
or cleanup policy. The boot allocation remains published as object 1 on the
decoder's first eligible frame. The scenario selects a distinct second eligible
frame, records that it has no prior publication, and rejects any attempt to
publish a live boot or scenario frame twice. After A's accepted allocation, the
bridge scrubs and maps the scenario frame at the generated page and A writes
`0xa5` to its first and last bytes directly in CPL3. Accepted termination
removes A's leaf, crosses a compiler barrier, reloads and reads back the active
no-PCID B root, acknowledges the generated termination-flush token, and only
then retires that publication. The bridge then scrubs all 4096 bytes through
the physical identity, invokes the generated fresh-publication edge, and maps
the same retired frame for B at the generated page. B directly reads both edge
bytes in CPL3 and reports zero; the old generation is rejected.

The fixed model partitions frames and does not model cross-subject commitment
reassignment. Consequently the correspondence between model frame 100 and the
Multiboot-selected machine frame is an explicit unproved binding assumption.
The bounded state codec, mapping choice, and their Lean refinement proofs are
proved; Lean code generation, the scalar ABI, Multiboot2 capacity input,
C/assembly allocation and CR3 bridge, scrub loop, serial protocol, compiler,
QEMU, and physical-page interpretation are
trusted/tested boundaries. The machine transcript is integration evidence,
not a binary-refinement theorem.
