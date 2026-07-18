# User extended-state denial model

LeanOS currently saves and restores only the fifteen general-purpose registers
and the five-word architectural return frame. The proved resumable-context
properties therefore do not cover x87, MMX, SSE, AVX, or other XSAVE-managed
state. Until a later design gives that state clean initialization and exclusive
per-subject ownership, Phase 2 adopts a fail-closed model policy.

## Checkpoint policy

`LeanOS.ExtendedState` models the relevant CPUID projection and requires this
exact live control snapshot before a user return can be armed:

| Control | Required value | Modeled purpose |
| --- | --- | --- |
| CR0.EM | 1 | Trap available x87/MMX use |
| CR0.MP | 1 | Keep WAIT/FWAIT subject to the denial state |
| CR0.TS | 1 | Produce the reviewed device-not-available denial for available x87/MMX |
| CR4.OSFXSR | 0 | Do not OS-enable legacy SIMD state |
| CR4.OSXMMEXCPT | 0 | Do not expose SIMD exception handling as an enabled facility |
| CR4.OSXSAVE | 0 | Do not OS-enable XSAVE or AVX state |
| XCR0 | not read (`none`) | XCR0 has no modeled meaning while OSXSAVE is clear |

The model rejects incoherent feature projections (SSE2 without SSE, or AVX
without both XSAVE and SSE). For a representative available x87 or MMX
instruction it expects vector 7 (#NM). An unavailable instruction family and
the deliberately OS-disabled SSE/SSE2/AVX families use the separately typed
vector 6 (#UD) path. Intel's architectural definitions for these controls and
exceptions are in the [Intel 64 and IA-32 Software Developer's Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).

The classifier accepts containment only for user origin, the expected vector,
the exact accepted control policy, and a normalized subject/address-space pair
equal to kernel-owned current state. Attacker payload words are erased. A
kernel-origin attempt, stale binding, unexpected vector, or control-policy
mismatch becomes typed fatal state. The return check rejects any attempted
policy relaxation.

## Evidence boundary

Proved in Lean for this finite model:

- the policy validator and classifier are total and deterministic;
- validator acceptance is equivalent to the explicit denial predicate;
- a contained denial names only the authoritative current subject and live
  address space, independent of attacker payload;
- kernel-origin and policy-inconsistent events cannot be contained user faults;
- an already-fatal state absorbs later classification; and
- an allowed modeled user return implies the exact denial policy remains live;
- contained denial cleanup reuses the authoritative resumable-preemption
  lifecycle, ready queue, context bank, mapping, and TLB state, leaving the
  faulting subject neither live, queued, current, nor resumable;
- a successful peer result comes only from `Scheduler.selectNext` and the
  selected subject's kernel-owned saved context; and
- policy, binding, or dispatch inconsistency changes only the absorbing halt
  latch, without publishing partial cleanup.
- the exact denied-state predicate wraps the authoritative composite gate, so
  every modeled interrupt, return, syscall, preemption, IPC, capability,
  mapping, lifecycle, and scheduler operation preserves it; a live mismatch
  halts before publishing any subsystem change; and
- every finite sequence of those composite operations preserves the predicate,
  while an accepted user return itself implies the live denied policy.

Executable `native_decide` cases cover an accepted policy and user #NM,
unexpected vector, kernel origin, stale subject binding, cleared CR0.TS,
enabled CR4.OSXSAVE, incoherent CPUID projection, and policy relaxation before
return. The shared 112-record oracle adds fixed-width #NM/#UD peer-dispatch, idle,
policy-mismatch, kernel-origin, stale-binding, and dispatch-invariant cases and
replays the generated adapter in both hosted C and the boot image. These are
finite model/boundary tests, not a refinement proof.

The versioned emulator evidence matrix treats dedicated x87 and MMX
two-subject denial images as mandatory accepted-boot scenarios. Each report
binds the exact QEMU command, source revision, image and ELF hashes, and
complete serial log. CI retains both ISOs, ELFs, link maps, final page-table
plans, serial transcripts, decoded CPUID/control-state snapshots, and
extended-state policy verdicts for 14 days.

The source and final-ELF policy gates also fix the reviewed CR0/CR4 write
inventory and reject `clts`, `fxrstor`, and `xrstor`. Controlled fixtures add
each forbidden instruction and an extra CR0 write to the source snapshot and
must retain their typed rejection diagnostics. The final-ELF gate additionally
requires `fld1` in the x87 image and `pxor %mm0,%mm0` in the MMX image; a
controlled class-swap fixture rejects each ELF under the other's expected
probe. This protects the inspection gate from silent relaxation; it does not
prove the disassembler or source scan complete for arbitrary instruction
encodings.

Still trusted and unproved are CPUID and control-register reads, instruction
decoding, hardware exception priority and delivery, descriptor loads, assembly,
generated code, the compiler/linker, firmware/GRUB state, and the final binary.
The QEMU scenario is tested evidence for one pinned emulator configuration; it
does not turn any of those boundaries into proved properties.

## Boot control-state integration

The early 32-bit boot path now derives the denial controls before enabling
long mode. It sets CR0.EM, CR0.MP, and CR0.TS, clears CR4.OSFXSR,
CR4.OSXMMEXCPT, and CR4.OSXSAVE, and retains the required PAE setting. After
the exception table and supervisor controls are installed, the guest rereads
CR0/CR4 and rejects any mismatch before a user return. The final-ELF/source
policy checker binds the two named normalization sites to their reviewed
instructions. These are inspected and QEMU-tested machine-boundary facts, not
proof that the processor implements the Lean control-state model.

The release scenario pins `qemu-system-x86_64` 8.2.2 under TCG with the Q35
machine, one CPU, and `-cpu max`. The guest decodes CPUID leaf 1 after control
normalization and requires x87, MMX, SSE, SSE2, XSAVE, and AVX to be advertised
while the dynamic OSXSAVE bit remains clear. A missing leaf, feature mismatch,
or inherited OSXSAVE state fails before CPL3 entry. The runner records that
decoded feature line together with the live CR0/CR4 line in
`extended-state-control-snapshot.txt`; this is reproducible evidence for the
pinned emulator contract, not a general hardware or CPUID theorem.

## Shared entry integration

Vectors 6 and 7 are now user-only interrupt gates in the same bounded entry
manifest and trap-frame normalizer as page fault, timer, and syscall entry.
Their assembly stubs clear AC/DF, save only the modeled GPR frame, and call the
shared kernel-owned authorization adapter before any denial operation.  A
same-privilege kernel #UD/#NM cannot normalize as a contained event.
The Lean transition now composes normalization-compatible classification with
authoritative cleanup and peer selection. The post-normalization C endpoint
invokes the generated fixed-width #NM/#UD adapter, which is also replayed by
the shared oracle, and assembly publishes the selected peer through the common
validated return path in the dedicated denial image.

## Remaining integration

The machine endpoint now consumes the cleanup/dispatch result, retires A, and
restores the scheduler-selected peer. The global model also carries the
denied-state predicate around #104's authoritative operation vocabulary and
proves single-step and finite-sequence preservation. The deterministic x87 and
MMX two-subject QEMU scenarios are now release-blocking and retain exact serial
and final-ELF evidence. Both attempts must trap before their selected shared
bank changes, retire A through the same normalized cleanup, and restore B
through the common validated return path. Final work still needs representative
SSE/SSE2/AVX denial coverage, refinement of the global wrapper to the
generated/machine gate, broader handler/runner negative fixtures, and the
remaining threat-model/TCB inventory updates.
