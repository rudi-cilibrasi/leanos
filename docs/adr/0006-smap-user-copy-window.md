# ADR 0006: Bounded SMAP user-copy window

- Status: Accepted
- Date: 2026-07-15

## Decision and evidence

The boot slice enables CR4.SMAP only after the exception table and TSS are
installed. Supervisor access to user leaves is therefore denied while
EFLAGS.AC is clear. One fixed syscall copies at most 16 bytes between subject
A's active two-page stack mapping and a typed 16-byte kernel buffer. Its
assembly wrappers disable interrupts, execute `stac` immediately before
`rep movsb`, execute `clac` immediately afterwards, and restore the prior
interrupt state. All interrupt entries clear AC before dispatch. The
image-policy check inventories every `stac` and fails if another is
introduced. There are three: the two copy windows and `smap_omit_cleanup_probe`,
the controlled probe described below.

The QEMU path performs a cross-page copy-in and copy-out and reads EFLAGS to
confirm AC is clear on return. A direct CPL0 read of a user page with AC clear
must page fault. Booted C executes bounded policy vectors for zero/maximal
lengths, unmapped and read-only ranges, overflow, noncanonical addresses,
wrong-subject context, and stale lifetime state, and checks rejection canaries.
A controlled assembly probe deliberately returns with AC set; the booted
detector must observe the policy violation before explicitly recovering with
CLAC. These are integration tests of the range-check adapter (generated from
Lean since #478; see the amendment below). The Lean model,
not these tests, is the policy evidence.

`LeanOS.UserCopyWindow` composes complete-range `UserCopy.validate` with the
x86 page-table classifier. Its theorems prove that closed encoded user leaves
are denied, an open window follows successful whole-range validation, write
permission is not amplified, rejection leaves modeled memory unchanged, and
both public copy transitions return with AC clear. Existing `UserCopy`
boundedness, footprint, caller/address-space confinement, ownership, and
atomic rejection theorems remain the underlying policy.

## Amendment (issue #478): generated range check and instruction plan

- **The range check.** The booted range check is no longer handwritten.
  `validate_copy` calls `leanos_user_copy_policy`, generated from
  `LeanOS.UserCopyPolicy`. That module instantiates `UserCopy.validate` for
  subject A's boot mapping:
  - text is mapped read-only and the stack read/write;
  - each page is its own object, so no two pages alias; and
  - a stale lifetime retires the stack objects.

  The export is fixed-width and allocation-free. It agrees with the model on
  the fourteen oracle vectors, which boot and the hosted replay both execute
  and whose expected words come from the model. It also agrees on a 540-case
  boundary grid. That is testing, not a proof for every input.
- **Two behavior changes**, both following the model:
  - a read of subject A's own text is now accepted (the page plan maps text
    user-readable); and
  - a range ending exactly at 2^64 is non-canonical rather than overflow.
- **The instruction plan.** Both copy windows are a Lean instruction plan,
  `LeanOS.SmapWindowPlan`. Theorems over that plan, treated as data, show
  three things. Every `ret` and `popfq` happens with the window closed. User
  memory is touched only inside it. The copy instruction is the only fault
  exit. `build-image.sh` requires the bytes and labels at both windows in every
  final ELF of the lane to equal the plan, and it requires a copy of
  `leanos.elf` with `clac` overwritten to fail the same check.
- **What stays trusted.** The x86 meaning of the planned instructions is taken
  from the manual: the check is byte equality, not an x86 semantics. The fault
  exit leaves with AC set, and the interrupt entry's AC cleanup closes it.

## Claims and trusted computing base

These are model-level proofs plus integration tests, not verification of the
generated C, compiler, assembly, page tables, QEMU, or hardware. The C call
into the generated range check, the linked text/stack symbols it passes, the
fixed syscall decoder, kernel buffer, STAC/CLAC wrappers,
interrupt masking and entry cleanup, CR4 setup, fault classification, and
single-core sequential assumption are trusted. Validation and transfer are
atomic only because interrupts are disabled and this slice has no concurrent
DMA or second CPU. Future asynchronous mapping mutation requires pinning or a
lock. No `sorry`, `admit`, new axiom/constant, `unsafe`, `extern`, or Lean FFI
declaration is added.
