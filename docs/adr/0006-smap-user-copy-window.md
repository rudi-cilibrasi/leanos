# ADR 0006: Bounded SMAP user-copy window

- Status: Accepted
- Date: 2026-07-15

## Decision and evidence

The boot slice enables CR4.SMAP only after the exception table and TSS are
installed. Supervisor access to user leaves is therefore denied while
EFLAGS.AC is clear. One fixed syscall copies at most 16 bytes between subject
A's active two-page stack mapping and a typed 16-byte kernel buffer. Its
assembly wrappers disable interrupts, execute the repository's only two
`stac` instructions immediately before `rep movsb`, execute `clac` immediately
afterwards, and restore the prior interrupt state. All interrupt entries clear
AC before dispatch. The image-policy check inventories both sites and fails if
another `stac` is introduced.

The QEMU path performs a cross-page copy-in and copy-out and observes AC clear
on return. A direct CPL0 read of a user page with AC clear must page fault. The
serial protocol also records bounded policy vectors for zero/maximal lengths,
unmapped and read-only ranges, overflow, noncanonical addresses, wrong-subject
context, and stale lifetime state; the Lean model is the policy evidence for
those vectors, while QEMU tests only the concrete accepted path and direct
denial probe.

`LeanOS.UserCopyWindow` composes complete-range `UserCopy.validate` with the
x86 page-table classifier. Its theorems prove that closed encoded user leaves
are denied, an open window follows successful whole-range validation, write
permission is not amplified, rejection leaves modeled memory unchanged, and
both public copy transitions return with AC clear. Existing `UserCopy`
boundedness, footprint, caller/address-space confinement, ownership, and
atomic rejection theorems remain the underlying policy.

## Claims and trusted computing base

These are model-level proofs plus integration tests, not verification of the
generated C, compiler, assembly, page tables, QEMU, or hardware. The C symbol
range check, fixed syscall decoder, kernel buffer, STAC/CLAC wrappers,
interrupt masking and entry cleanup, CR4 setup, fault classification, and
single-core sequential assumption are trusted. Validation and transfer are
atomic only because interrupts are disabled and this slice has no concurrent
DMA or second CPU. Future asynchronous mapping mutation requires pinning or a
lock. No `sorry`, `admit`, new axiom/constant, `unsafe`, `extern`, or Lean FFI
declaration is added.
