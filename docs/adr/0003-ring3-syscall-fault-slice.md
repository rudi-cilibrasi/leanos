# ADR 0003: Ring-3 syscall and contained-fault slice

- Status: Accepted
- Date: 2026-07-14

## Decision

The first Phase 2 binary boundary uses a DPL-3 `int 0x80` interrupt gate. A
minimal GDT adds user code/data descriptors and a 64-bit TSS supplies a separate
16 KiB kernel entry stack. The entry stub saves the general-purpose registers
used by this fixed ABI, and `iretq` restores the CPU-created privilege frame.
The kernel rejects an entry whose saved CS is not ring 3; caller and active
address-space identity are fixed kernel state and are never read from user
registers.

Four-level 4 KiB identity mappings cover only the first 16 MiB. Every leaf is
supervisor-only and NX by default. Kernel instruction pages are read-only and
executable. Exactly one user instruction page is user-readable and executable,
but not writable; exactly one bounded user-stack page is user-readable/writable
and NX. Page tables, kernel data, the TSS, IDT, and entry stack remain
supervisor-only. `scripts/check-image-policy.sh` checks ELF section flags,
required boundary symbols, and the narrow page-table construction.

Vector 14 accepts only a user-mode protection fault. The handler classifies the
deliberate access to supervisor address zero, replaces the saved user RIP with
the reviewed recovery label, and returns to ring 3. This is containment evidence
for that single case, not a general exception subsystem.

## Evidence and assumptions

The version-2 serial protocol records CPL3 entry, an accepted modeled call, a
rejected malformed call, the contained fault, kernel resumption, and final
guest success. The exact transcript plus QEMU debug-exit status is required.
Host fixtures prove missing/partial traces, guest failure, and timeout cannot
pass. `./scripts/check.sh` independently checks the Lean models and proof
integrity; QEMU output does not prove those properties.

Trusted assumptions added by this slice are the x86-64 interrupt, paging, TSS,
IDT, and `iretq` semantics; assembly and C entry code; linker layout; generated
C and Lean runtime primitive; GRUB/firmware; QEMU/TCG; compiler and linker; and
the host inspection scripts. No x86 instruction, generated code, kernel binary,
QEMU behavior, or hardware property is proved.

## Threat model and TCB inventory

The deliberately adversarial subject controls its scalar syscall words and may
execute the selected invalid memory access. It does not control kernel-selected
subject/address-space context, descriptor tables, page tables, exception
frames, or the kernel entry stack. The tested claim is limited to rejecting the
one malformed request and containing the one reviewed user protection fault;
malicious concurrency, DMA, speculative execution, side channels, and other
fault classes remain out of scope.

This slice adds the GDT/TSS/IDT and page-table setup in `boot/boot.S`, the entry
and exception assembly, `boot/kernel.c` dispatch and recovery code, linker
layout, generated `syscallDemo` C, and the image-policy/trace scripts to the TCB
already inventoried in ADR 0001 and the boot-image guide. The compiler, linker,
GRUB, QEMU/TCG, and x86-64 architectural semantics remain trusted. A defect in
any of these can forge the trace, bind the wrong caller, expose supervisor
memory, corrupt the exception frame, or invalidate containment evidence.

## Consequences

This deliberately supports one subject, one synchronous gate, scalar arguments,
and one expected page fault. It adds no scheduler, IPC, preemption, user-pointer
copying, signals, general fault recovery, speculative-execution defense, or
production-hardening claim.

## Version-14 containment follow-up

The original reviewed-RIP recovery remains historical evidence and remains in
the normal blocking-IPC and preemption scenarios.  It is not the policy used
by the independent `fault-containment` image.  That image starts A in CPL3,
observes the architectural protection fault at address zero through the shared
normalized entry path, and passes the kernel-bound vector, origin, current
subject/address space, ready head, and context owner to the fixed-width
`LeanOS.FaultDispatch` adapter.  Only its encoded composite result authorizes
A's cleanup and B's selection; C does not select a recovery label or implement
a second scheduler for this scenario.

The version-14 transcript separately records hardware entry, the trusted A
binding, all five non-resumption witnesses, deterministic B selection, B's
validated return under B's checked CR3, and unchanged B canary/resource
witnesses.  The ordinary image and its transcript are unchanged.  A
kernel-origin page fault still bypasses containment and enters the existing
typed terminal path; vector 8 remains the distinct double-fault/IST purpose.

The Lean theorem and oracle concern the bounded model and adapter inputs.  Raw
x86 delivery, the entry stack, assembly context copy, CR3 load, generated C,
compiler/linker, final return validation, QEMU, firmware, and the host evidence
runner remain tested or trusted boundaries, not proved refinement steps.
