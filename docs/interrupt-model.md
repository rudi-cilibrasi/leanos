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
subject.

Executable traces cover user and kernel page faults, an unexpected vector,
timer delivery, valid return, wrong-origin syscall entry, malformed selectors
and flags, and nested entry.

## Proof, tests, and trusted assumptions

The proved claims apply only to the Lean transition model: deterministic vector
classification, trusted-context continuity, user-fault isolation through the
subject-lifecycle model, invariant preservation, and rejection of malformed
returns. Compilation and execution of examples test the executable model; they
do not prove the machine boundary.

Hardware construction of the trap frame, IDT and TSS descriptors, kernel-stack
selection, interrupt masking, assembly save/restore, `iretq`, canonical-address
and flags checks, page tables, generated code, compiler, QEMU, and x86-64
semantics remain trusted. This change adds no `unsafe`, `extern`, FFI, axiom, or
constant declaration and does not change the executable image. Connecting the
model to that image is future integration work.
