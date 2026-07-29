# ADR 0012: Frame-budget exhaustion and tested reuse

## Status

Accepted.

## Decision

Add one independent, deterministic two-subject QEMU mode backed by the
canonical generated stateful dispatcher. Subject A has one admitted model
frame and subject B has two. A allocates once and receives a complete-state
preserving `budgetExhausted` on retry; B remains available; checked termination
retires A; and B receives fresh identity 3 only after the model and machine
paths completely scrub the reclaimed frame and deny A's identity-1 handle.

The guest supplies operation numbers and the old generation-checked handle
only. Kernel-normalized current subject and active CR3 select the charged
subject. Object/frame identities, budgets, expected results, next owner, and
cleanup decisions are canonical generated data.

## Evidence and failure policy

The shared 354-record corpus is evaluated by Lean, hosted generated C, and
every boot image. The version-19 serial transcript is exact and bounded by the
ordinary runner timeout and debug-exit contract. Controlled fixtures reject a
global-counter substitution, cross-charge, user-selected owner, exhaustion
relabel, partial publication, double credit, leaked canary, stale authorization,
missing/reordered records, and forged final status.

CI preserves the corpus, per-step hosted results, generated source/header,
budget diagnostics, image, ELF/map, compiled page-table plan, exact serial log,
and controlled-negative logs.

## TCB and excluded claims

Lean proves the finite sequence against `FrameBudget.State`, including
rejection atomicity, peer availability, cleanup conservation, fresh identity,
and stale authority denial. The model's immutable partitions do not express
cross-subject physical-frame reassignment. Binding its fresh B allocation to
the machine bridge's released A frame is therefore an explicit tested, unproved
assumption.

Trusted components include the bounded token codec, Lean code generator,
generated-C ABI, compiler/linker, Multiboot2 capacity report, C/assembly entry,
CR3 and allocation bridge, scrub loop, linker frame placement, UART protocol,
GRUB, SeaBIOS, QEMU/TCG, and assumed x86-64/page semantics. This scenario is
finite integration evidence, not proof that the binary refines the model.
