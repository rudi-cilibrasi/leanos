# ADR 0008: Bounded resumable preemption

- Status: Accepted
- Date: 2026-07-16

## Decision and evidence

The boot image extends ADR 0005 with exactly two independently armed PIT mode-0
events. The first saves subject A's complete interrupt image and installs B's
fresh context; the second saves B separately and restores A's original image.
Each kernel-owned image is 160 bytes: fifteen general registers followed by
RIP, CS, RFLAGS, RSP, and SS. Selection comes only from the generated bounded
`leanos_preemption_demo` result and protected `current_subject`, never from a
user register or syscall word.

The handler masks IRQ0 before EOI. B explicitly reaches an authorized syscall
before the second one-shot is armed. Both directions reload CR3 and verify the
selected root before `iretq`. A polls a harmless kernel-state token, then checks
its distinct `r12`/`r13` canaries after resumption; the kernel also checks the
separate saved A/B canaries and the actual image selectors, CS `0x23` and SS
`0x1b`. The exact transcript requires two timer, context, paging, and switch
records plus A's original-frame resume record and `FINAL ticks=2`.

The shared oracle contains both scalar scheduler bindings and composite
save/select/restore witnesses for A-to-B and B-to-A. The composite encoding
packs the restored owner, address space, logical stack, and r12 marker beside
the outgoing bank owner, stack, and r12 marker. The assembly passes immutable
kernel-owned owner tags for the selected and outgoing banks, while C derives
both logical stack markers from the target and saved RSP words and both r12
markers from their concrete buffers. A cross-owned restore bank is a generated
rejecting vector and a boot-side preflight negative; corrupt saved RSP data
fails before the final transcript. Assembly snapshots each bank's exact
original RIP, RSP, and RFLAGS into separate kernel-owned metadata. C compares
both
saved banks and A's restored target against those snapshots before claiming
that the original frame resumed.
The runner rejects missing or duplicate ticks, restart instead of resume,
cross-restored identity, stale CR3, wrong caller, corrupt register/stack/flags
or selectors, a forged final PASS, guest failure, and timeout. The real QEMU
run and retained ELF, map, corpus, and serial log are reproducible tests.

## Claims and trusted computing base

Lean proves the bounded model's ownership, separation, cleanup, and round-trip
properties. QEMU exercises one concrete save/select/restore path; it does not
prove assembly refinement, compiler correctness, timer delivery, `iretq`, or
CR3/TLB hardware semantics. The context-copy assembly, protected storage,
PIT/PIC programming, C protocol state, compiler/linker/GRUB, serial checker,
QEMU, and x86-64 semantics remain trusted. This no-PCID slice relies on CR3
reload invalidation. No proof escape or new unchecked declaration is added.
