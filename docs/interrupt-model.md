# Interrupt and exception model

`LeanOS.Interrupt` is a small total, sequential model for vectors 14 (page
fault), 32 (timer), and 128 (the existing `int 0x80` syscall relationship).
Every other vector is a typed fatal outcome. Nested entry is disabled: an
entry while the trusted `entryActive` flag is set is fatal.

The hardware-supplied frame contains the vector, error code, saved privilege,
instruction and stack state, selectors, flags, and explicit canonicality
checks. General-purpose registers are modeled separately as attacker-controlled
values. The dispatch function erases them before classification; the Lean
theorem proves that changing them cannot change dispatch or trusted context.
A valid user return requires CPL3 provenance, the selected user code/data
selectors, canonical instruction and stack pointers, and allowed flags.
Syscall entry from kernel privilege is rejected separately as a wrong-origin
event rather than being mislabeled as a malformed user return.

`validateUserReturn` is the authoritative total outgoing transition. Its input
combines the frame with kernel-selected purpose, live subject, owned address
space, CR3 identity, execution mode, executable region, writable stack region,
and the raw saved RFLAGS word. It rejects diagnostic kernel recovery, halted mode,
stale scheduler/context bindings, noncanonical or out-of-region addresses,
wrong selectors or CR3, cleared IF, and set DF, AC, NT, VM, or IOPL. Acceptance
returns an attestation of the entire immutable request, preventing the model API
from validating one tuple and consuming another. The confinement theorem pins
exact request identity and every validator condition: purpose and mode,
canonicality and region containment, complete flags, subject liveness,
runnability and selection, address ownership, and CR3 binding. The composite
`FailStop.selectLiveReturnAuthority` transition first binds the live scheduler
subject and owned address space to a proof-carrying `BootPageTablePlan.Plan`. It
arms an exact purpose, CR3 root, executable page, and stack page only when the
root and exact user-text/user-stack leaves occur in that compiled plan and
their physical frames equal the active virtual-memory mappings' live object
bindings.
`FailStop.completeUserReturn` refuses an unarmed record,
normalizes scheduler identity from execution state, and takes the remaining
policy from the bound record. It converts rejection into a
typed absorbing halt record without changing lifecycle, authority, scheduling,
IPC, or resource views.
Initial dispatch selects through the typed `selectUserReturn` gate operation;
syscall and scheduler-return paths reselect automatically only after the final
context update. Syscall classification itself stays unarmed, so an immediate
return cannot skip the modeled syscall body. The syscall body performs its
reselection only after publishing its resulting virtual-memory and lifecycle state. Lifecycle,
scheduler, capability, and virtual-memory
installation clears any earlier selection before that reselection.
The shared machine epilogue clears the kernel-managed saved DF and AC bits
before validation; the other forbidden flag fields remain reject-only.

A user page fault atomically applies the subject-lifecycle termination policy
to the kernel-selected current subject. Existing lifecycle proofs establish
complete cleanup; this module additionally proves preservation of unrelated
owned memory, capability slots that do not reference terminated resources,
address-space mappings, physical-frame state, and endpoint ownership. Mailbox
provenance from the terminated subject is deliberately cleaned up by the
lifecycle policy. A kernel page fault is a distinct fatal outcome and cannot
be reported as containment. Timer delivery preserves the complete state and
produces only a scheduling event. A well-formed state is preserved by every
nonfatal transition; fatal transitions cannot resume as any subject. Any
accepted return has a valid CPL3 frame and retains the kernel-selected current
subject. The stable authority claim exposes the installed-view binding, and a
concrete well-formed witness reaches an armed state and completes an accepted
return, so the contract is not vacuous.

Executable traces cover user and kernel page faults, an unexpected vector,
timer delivery, valid return, wrong-origin syscall entry, malformed selectors
and flags, and nested entry.

## Proof, tests, and trusted assumptions

The proved claims apply only to the Lean transition model: deterministic vector
classification, trusted-context continuity, user-fault isolation through the
subject-lifecycle model, invariant preservation, and rejection of malformed
returns. Compilation and execution of examples test the executable model; they
do not prove the machine boundary.

Hardware construction and decoding of the trap frame and flags, IDT and TSS
descriptors, kernel-stack selection, interrupt masking, assembly save/restore,
CR3/TLB operations, `iretq`, canonical-address and region checks, page tables,
generated code, compiler, QEMU, and x86-64 semantics remain trusted. This model
slice adds no `unsafe`, `extern`, FFI, axiom, or constant declaration. The boot
image now routes initial dispatch, syscall resume, and timer restore through one
bounded C validator and shared assembly epilogue. Final-ELF inspection permits
only that CPL3 `iretq` plus the separately classified diagnostic CPL0 recovery
site, and rejects calls or context changes between validation and consumption.
The C adapter and inspection are integration evidence, not refinement proofs.
The shared generated-model oracle derives expected return results from
`validateUserReturn`, proves pointwise agreement with the allocation-free
adapter for every corpus vector, and replays those vectors through hosted
generated code and the boot image. A controlled corrupt-frame QEMU corpus
remains required.
