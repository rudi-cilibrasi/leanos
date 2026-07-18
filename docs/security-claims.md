# Security claim index

This index uses the evidence vocabulary fixed by
[ADR 0001](adr/0001-phase-1-scope-threat-model-and-tcb.md). Every **Proved** row
names an independently restated theorem in the default-built
`LeanOS.SecurityClaims` contract. Proofs apply to Lean models only; generated C,
the runtime, boot code, QEMU, hardware, timing, concurrency, and covert channels
remain excluded unless a separate refinement claim says otherwise.

<!-- claim-index:start -->
| ID | Contract declaration | Source theorem | Model / transition | Assumptions | Evidence | Explicit exclusions |
| --- | --- | --- | --- | --- | --- | --- |
| SC-KERNEL-DET | `kernel_transition_deterministic` | `KernelTransition.transition_deterministic` | `KernelTransition.transition` | Same state and command; two evaluations equal the named outcomes | Proved | Generated code and boot boundary |
| SC-KERNEL-WF | `kernel_transition_preserves_wellFormed` | `KernelTransition.transition_preserves_wellFormed` | `KernelTransition.transition` | `KernelTransition.WellFormed state` | Proved | Generated code and boot boundary |
| SC-CAP-AUTH | `capability_copy_no_authority_amplification` | `Capability.copy_no_authority_amplification` | `Capability.copy` | Full modeled pre-state; authority exists after copy | Proved | Information flow, concurrency, lifetimes, binary |
| SC-FRAME-OWNER | `frame_ownership_exclusive` | `FrameAllocator.ownership_exclusive` | Frame ownership state | Both ownership predicates hold for the same frame | Proved | Firmware truth and allocator integration |
| SC-FRAME-BUDGET-ISOLATION | `admitted_frame_budget_isolation` | `FrameBudget.available_allocation_accepted` | `FrameBudget.allocate` over fixed boot-admitted frame partitions | Live trusted subject; valid empty generation-bounded slot; fresh object identity; at least one free frame committed to that subject | Proved | Dynamic admission or reassignment, concurrency/SMP, fairness/timing, generated code, boot policy installation, QEMU, hardware |
| SC-PT-SEPARATION | `page_table_distinct_spaces_separated` | `X86PageTable.distinct_spaces_separated` | Encoded page tables and `walk` | Both leaves exist at the page and their frames differ | Proved | Hardware walks, CR3/TLB, compiler |
| SC-SYSCALL-CONFINEMENT | `syscall_authority_confinement` | `Syscall.dispatch_authority_provenance` | Trusted-context syscall dispatch | Post-dispatch modeled authority | Proved | Entry path establishing trusted context |
| SC-FAILSTOP | `failstop_halted_suffix_absorbing` | `FailStop.halted_suffix_absorbing` | `FailStop.runOperations` | Execution mode already equals the named halted record | Proved | Machine reset/NMI behavior and persistence |
| SC-COMPOSITE-GATE-WF | `composite_gate_sealed_receive_preserves_runtimeWellFormed` | `FailStop.gate_sealed_receive_preserves_runtimeWellFormed` | Sealed-mailbox rejection path of `FailStop.gate` | Globally well-formed running composite state; the caller's canonical endpoint handle resolves to a mailbox with a pending sealed descendant | Proved | Other composite operations until their preservation slices land; generated adapters, concurrency/SMP, compiler, QEMU, hardware |
| SC-USER-RETURN-CONFINEMENT | `user_return_context_confinement` | `Interrupt.accepted_user_return_context_confined` | `Interrupt.validateUserReturn` | Exact accepted attestation; allowed purpose; running CPL3 frame/selectors; canonical and subject-contained RIP/RSP; complete raw/decoded flag policy; live, runnable, current subject; owned address space and matching CR3 | Proved | Frame/flag decoding, generated adapter, assembly, CR3/TLB writes, `iretq`, compiler, QEMU, hardware |
| SC-USER-RETURN-AUTHORITY | `user_return_authority_confinement` | `FailStop.accepted_user_return_has_bound_authority` | `BootPageTablePlan.compile`, `FailStop.selectReturnAuthority`, `FailStop.completeUserReturn` | Well-formed state and accepted outgoing return; selected subject/address-space view agrees with lifecycle ownership and exact compiled-plan root/user-text/user-stack leaves | Proved | Live installation of the compiled plan, generated C, assembly, compiler, QEMU, hardware |
| SC-USER-RETURN-LIVE-PLAN | `user_return_authority_requires_live_plan` | `FailStop.selectLiveReturnAuthority_armed_implies_live` | `FailStop.selectLiveReturnAuthority` | Armed composite authority implies the compiled user-text/user-stack leaf frames equal live memory-object bindings whose object kinds and allocator ownership agree with the active virtual-memory mappings; `user_return_composite_entry_witness` establishes syscall/return non-vacuity | Proved | Generated C, assembly, compiler, QEMU, page-walk hardware |
| SC-USER-RETURN-FAILSTOP | `user_return_rejection_failstop` | `FailStop.rejected_user_return_composite_atomicity` | `FailStop.gate` | Running composite state with armed authority and live plan/mapping refinement; authoritative normalized return request is rejected | Proved | Frame/context decoding before the modeled gate, generated C, assembly restore, terminal serial transport, compiler, QEMU, hardware |
| SC-SCHEDULED-ISOLATION | `scheduled_finite_trace_isolation` | `ScheduledObservation.finite_trace_lowEquiv` | Finite paired scheduled runs | Initial low-equivalence and equal declared public event projections | Proved | Timing, termination, public channels, binary refinement |
<!-- claim-index:end -->

## Review workflow

To add a claim, add an independently typed wrapper theorem, then one unique row
with its assumptions and exclusions. To revise a claim, update its wrapper,
index row, and the relevant ADR/model document in the same change. Growing an
assumption or shrinking a conclusion requires an explicit rationale. Preserve
an old ID when its meaning is unchanged; otherwise deprecate it in prose and
introduce a new ID that names the superseded claim. Tested evidence must link a
repository-owned script and must never be classified as Proved.
