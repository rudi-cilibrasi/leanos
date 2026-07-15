# ADR 0005: One-shot timer preemption

- Status: Accepted
- Date: 2026-07-15

## Decision and evidence

The image programs the QEMU q35 legacy 8254 PIT channel 0 in mode 0 with count
65535 and remaps PIC IRQ0 to vector 32. Subject A enters CPL3, reports entry,
then loops without yielding. The first accepted interrupt is masked before EOI
and is accepted only when the generated `leanos_preemption_demo` witness agrees
with `LeanOS.Preemption.oneShotTick`, which composes interrupt classification
with the bounded round-robin scheduler. The selected subject and address space
are decoded from that witness rather than from interrupted registers.

The assembly saves all general-purpose registers plus the hardware RIP, CS,
RFLAGS, RSP, and SS frame. It installs B's fresh RIP, stack, and register
canaries, switches to B's CR3, records completion, and returns with `iretq`.
B's authorized syscall succeeds only with kernel-owned subject 2 and checks
both canaries. The exact version-5 transcript rejects missing delivery, old
subject resumption, wrong CR3/caller binding, duplicate records, corruption,
guest failure, and timeout. CI retains the ISO, ELF, map, tool versions, QEMU
log, and smoke-test log.

## Claims and trusted computing base

Lean proves only that the modeled accepted timer transition uses the scheduler,
preserves its invariant, accepts at most one tick, and returns a context whose
subject/address-space binding comes from lifecycle state. The QEMU run tests one
concrete machine path. It is not a proof of interrupt delivery, liveness,
assembly refinement, page tables, CR3/TLB semantics, or the final binary.

TCB additions are PIT/PIC programming and QEMU's emulation, IDT vector 32,
interrupt masking/EOI ordering, the assembly save/restore and CR3 sequence,
the C adapter and protected globals, compiler/linker/GRUB, existing page-table
and TSS construction, serial checker, and x86-64 semantics. The adapter relies
on CR3 reload invalidation for this no-PCID slice. No new Lean axiom, constant,
`unsafe`, `extern`, FFI declaration, `sorry`, or `admit` is introduced.
