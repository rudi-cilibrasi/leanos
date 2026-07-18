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
- an allowed modeled user return implies the exact denial policy remains live.

Executable `native_decide` cases cover an accepted policy and user #NM,
unexpected vector, kernel origin, stale subject binding, cleared CR0.TS,
enabled CR4.OSXSAVE, incoherent CPUID projection, and policy relaxation before
return. These execute the Lean model; they are not machine tests.

Still trusted and unproved are CPUID and control-register reads, instruction
decoding, hardware exception priority and delivery, descriptor loads, assembly,
generated code, the compiler/linker, firmware/GRUB state, and the final binary.
No QEMU claim is made by this checkpoint.

## Boot control-state integration

The early 32-bit boot path now derives the denial controls before enabling
long mode. It sets CR0.EM, CR0.MP, and CR0.TS, clears CR4.OSFXSR,
CR4.OSXMMEXCPT, and CR4.OSXSAVE, and retains the required PAE setting. After
the exception table and supervisor controls are installed, the guest rereads
CR0/CR4 and rejects any mismatch before a user return. The final-ELF/source
policy checker binds the two named normalization sites to their reviewed
instructions. These are inspected and QEMU-tested machine-boundary facts, not
proof that the processor implements the Lean control-state model.

## Shared entry integration

Vectors 6 and 7 are now user-only interrupt gates in the same bounded entry
manifest and trap-frame normalizer as page fault, timer, and syscall entry.
Their assembly stubs clear AC/DF, save only the modeled GPR frame, and call the
shared kernel-owned authorization adapter before any denial operation.  A
same-privilege kernel #UD/#NM cannot normalize as a contained event.  The
current post-normalization endpoint is intentionally fail-stop until lifecycle
cleanup and peer dispatch are composed; this checkpoint does not claim a
successful contained machine denial.

## Remaining integration

The next checkpoint must compose normalized user denial with issue #101's
authoritative cleanup/peer-dispatch path.
Issues #104 and #105 must then carry this predicate through the global runtime
and generated stateful boundary. Final work also needs source/final-ELF policy
checks, negative fixtures, a two-subject QEMU scenario, preserved snapshots and
disassembly, and documentation of the exact pinned QEMU CPU contract.
