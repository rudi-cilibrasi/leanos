# Interrupt and exception model

`LeanOS.Interrupt` is a small total, sequential model for vectors 14 (page
fault), 32 (timer), and 128 (the existing `int 0x80` syscall relationship).
The companion `LeanOS.ExtendedState` classifier owns the admitted user-only
vector 6 (#UD) and vector 7 (#NM) denial cases; they are not generic recoverable
exceptions. Every other vector is a typed fatal outcome. Nested entry is disabled: an
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

## Inbound entry manifest and normalization

`LeanOS.InterruptEntry` defines the complete ordinary boot manifest: vector 14
is a DPL0 interrupt gate with a hardware error word and user-fault or supervisor
diagnostic purpose; vector 32 is a DPL0 interrupt gate without an error word;
and vector 128 is the sole DPL3 interrupt gate and has syscall purpose. All use
selector `0x08`, IST0, and interrupt-gate masking. Vector 8 remains owned by the
separate terminal IST1 protocol, and vector 13 remains its bounded probe gate.

Raw frames have two distinct constructors. A privilege-changing frame contains
RIP, CS, RFLAGS, RSP, and SS. A same-privilege frame contains only RIP, CS, and
RFLAGS; normalization cannot read or synthesize absent RSP/SS fields. Origin is
derived from the reviewed CS/CPL rule together with that constructor, never
from saved registers or user-looking words at later offsets. A kernel vector-14
frame becomes `diagnosticRecovery`, never user containment.

The total normalizer rejects a duplicate or unsupported manifest, unbound
vector/stub, wrong error convention, truncated or misaligned frame, wrong raw
shape or origin, out-of-bounds entry stack, nested entry, and uncleared AC/DF.
Accepted records copy subject, active address space/CR3, and stack identity from
`KernelContext`; attacker registers are absent from the function input. Lean
proves manifest validity, uniqueness of the DPL3 syscall gate, totality and
determinism, attacker-register erasure, rejection stability, same-privilege
confinement, nested/uncleared-state nonauthorization, and exact kernel-context
binding. These are model results only.

The generated allocation-free `leanos_entry_demo` adapter is replayed in the
version-one oracle with valid syscall, user page fault, timer, and diagnostic
records plus wrong binding, error shape, length, alignment, origin, stack,
nested-latch, and AC/DF fixtures. `scripts/check-entry-policy.sh` enumerates the
final-ELF entry paths and requires cleanup, shared authorization, the typed
handler, and latch completion in that order. `scripts/test-entry-policy.sh`
applies bounded one-field descriptor, path, error-shape, and TSS mutations to
controlled source snapshots and requires the production checker to reject each
with its vector and field/path diagnostic. At boot, `check_entry_manifest`
decodes every present IDT entry and the relevant TSS stack pointers and rejects
unmanifested present gates.

The bounded entry-adversarial image executes `int $14` and `int $32` from CPL3.
Both attempts must deliver vector 13 with the selector-derived error code, must
leave the privileged vector-14 and vector-32 handlers unreachable, and must
then complete the ordinary syscall path with its trusted subject/address-space
binding. Firmware PIC lines are masked when the IDT is installed; only the
preemption scenario remaps and deliberately unmasks IRQ0, preventing a legacy
IRQ from being confused with the dedicated vector-8 terminal protocol.

## Ordinary entry-stack layout and budget contract

`LeanOS.PrivilegeEntryStack` introduces the model vocabulary shared by the
ordinary entry manifest. Byte ranges are half-open. The usable stack grows
downward from one 16-byte-aligned exclusive `stackTop`; a one-page lower guard
must be adjacent, absent, and disjoint from every supplied reserved interval.
Accepted usable leaves are supervisor-writable, non-user, and non-executable.
The model uses natural-number addresses below the 64-bit address limit, so its
checked subtraction cannot model machine-word wraparound.

Every manifest entry uses one `BudgetRequest`. Its fixed contribution accounts
for the three- or five-word hardware frame, the optional hardware error word,
the fifteen-register save bank, and the stub's dummy/alignment slots. The
machine-derived boot-reachable C/generated call contribution, return-validator
contribution, and safety margin remain explicit inputs; the model does not
assign operations or boot scenarios private limits. `checkedRemaining` mints a
remaining-budget fact only when the complete request fits the usable interval.
Lean proves the subtraction equation, exact accepted stack identity and bounds,
and that both accepted and fatal results retain the exact inbound composite
state. An insufficient request is a typed atomic fatal result and cannot
authorize an operation handler or return.

The executable witnesses use zero machine-derived contribution solely to check
the common fixed protocol for syscall, timer, user-page-fault, and supervisor
diagnostic purposes. They are not a concrete production budget. The concrete
image now places the ordinary stack in a page-aligned linker-owned 16 KiB
`.entry_stack` interval immediately above a 4 KiB `.entry_stack_guard`; both
ranges are half-open, and `TSS.rsp0` receives the linker's exclusive
`__entry_stack_end`. The accepted linker-resolved page-table plan classifies
the usable pages as supervisor-only writable/NX stack leaves and emits no leaf
for the guard in either root. Early assembly removes that leaf from both live
tables, while the guest decoder rejects a controlled attempt to restore it.
Final-ELF policy checks bind the section flags, exact adjacency and sizes,
canonical top symbol, TSS assignment, and reviewed unmapping instruction.

The image compiler now emits `.su` reports for the handwritten and generated C
objects. `scripts/entry-stack-callgraph.tsv` records the reviewed boot-reachable
ordinary-entry paths, their user/kernel origin, hardware-error shape, and a
4 KiB safety margin. `scripts/check-entry-stack-budget.sh` derives the prefix
from those frame fields and the counted 15-register assembly save bank, then
rejects a changed save count, missing or dynamic usage, unresolved indirect
edges, cycles in a path, or any total above the 16 KiB usable interval. Its
machine-readable report is retained with the image. In particular, a CPL3
syscall or timer prefix is 176 bytes (40-byte hardware frame, 120-byte save
bank, and 16-byte normalizer), rather than a manually entered constant.
CI also retains the exact reviewed call-graph snapshot, raw compiler `.su`
files, sorted final-ELF symbols, and final disassembly beside that report.
After the final link, the gate extracts direct and tail-call edges from the ELF,
requires every reviewed stack contributor to be retained and reachable from
its named entry stub, rejects indirect transfers anywhere in that reachable
closure, and rejects every transitively reachable compiler-reported function
that the reviewed manifest does not account for. It also counts the expanded
register-save pushes in each final entry-stub disassembly and rejects direct or
mutual recursion cycles in the final reachable graph. Targeted ELF fixtures
remove one save push and introduce a two-function cycle so these gates cannot
be satisfied by the reviewed source manifest alone.
The extracted edges and final-ELF verdict are retained as checking evidence,
not a proof of GCC, generated C, assembly, or the final machine path.

The model-level handoff now uses `BudgetedNormalizedFrame` to bind the one
normalized interrupt record to the budget minted by `authorize`. The binding
accepts only matching stack identities and entry purposes, and carries the
half-open usable bounds, canonical exclusive top, required bytes, and checked
remaining bytes into the handler-facing record. Lean proves that an accepted
binding retains the exact normalized frame and authoritative layout, with
`remaining + required = usable`. This is a modeled fact; the C adapter and
final binary correspondence remain checked evidence.

The accepted normal and preemption images additionally paint the unused
ordinary-entry stack before the first CPL3 dispatch. At each scenario's final
accepted checkpoint they scan upward from the lower bound, require at least
the 4 KiB static safety margin to remain untouched, and emit a bounded
`ENTRY-HIGH-WATER` record. Both images first exercise a CPL3 read of the
supervisor-only zero page and record the resulting error-code-5 vector-14 path
before recovery; their final records cover the blocking-IPC syscall or the
cumulative timer/context-switch scenario. The runner requires both records in
order, validates their path identities and arithmetic, and retains them as a
CI artifact. Targeted runner fixtures reject a missing, duplicate, reordered,
mislabeled, or arithmetically inconsistent observation. This
diagnostic can miss writes that reproduce the paint word, is cumulative rather
than path-isolated, and does not replace the final-ELF/compiler gate. A
kernel-origin diagnostic path does not switch through `rsp0`; a separate
boot-stack high-water observation is therefore not claimed here.

The accepted boot-reservation manifest now carries distinct
`.ordinaryEntryGuard` and `.ordinaryEntryStack` identities. Allocator
initialization rejects non-adjacency or overlap with page tables, descriptor
tables, the separate double-fault stack reservation, or embedded user images;
the enclosing loaded-image reservation intentionally contains both. A separate
deterministic image places `RSP` at the ordinary guard boundary before raising
a real exception. Delivery crosses the absent guard and escalates to vector 8
on IST1. Its terminal record requires the IST1 range and canaries, both
ordinary-stack boundary canaries, the absent guard, no ordinary handler, and no
return. The shared evidence matrix retains that image, ELF, map, and serial log;
adversarial runner fixtures reject a direct-handler claim, mapped guard, stale
`rsp0`, adjacent write, partial or reordered output, reset, triple fault, and
hang. This is checked x86/QEMU evidence rather than a refinement proof. The stable
`SC-PRIVILEGE-ENTRY-STACK` claim covers only accepted authorization in this
Lean layout/budget model. [ADR 0010](adr/0010-guarded-privilege-entry-stack.md)
records the separate checked machine evidence and its trusted boundary.

## Proof, tests, and trusted assumptions

The proved claims apply only to the Lean transition model: deterministic vector
classification, trusted-context continuity, user-fault isolation through the
subject-lifecycle model, invariant preservation, and rejection of malformed
returns. Compilation and execution of examples test the executable model; they
do not prove the machine boundary.

Hardware construction of the trap frame, IDT/TSS loads, kernel-stack selection,
interrupt masking, assembly save/restore,
CR3/TLB operations, `iretq`, canonical-address and region checks, page tables,
generated code, compiler, QEMU, and x86-64 semantics remain trusted. This model
slice adds no `unsafe`, `extern`, FFI, axiom, or constant declaration. The boot
image now routes initial dispatch, syscall resume, and timer restore through one
bounded C validator and shared assembly epilogue. Final-ELF inspection permits
only that CPL3 `iretq` plus the separately classified diagnostic CPL0 recovery
site, and rejects calls or context changes between validation and consumption.
The C adapter and inspection are integration evidence, not refinement proofs.
For vectors 6/7, the saved selector, live CR3, protected current subject,
expected probe vector, generated denial result, cleanup publication, and peer
return are additional trusted machine operations. Controlled source fixtures
remove those bindings or reorder the handler before cleanup/normalization and
require typed policy rejection.
The shared generated-model oracle derives expected return results from
`validateUserReturn`, proves pointwise agreement with the allocation-free
adapter for every corpus vector, and replays those vectors through hosted
generated code and the boot image. A controlled corrupt-frame QEMU corpus
boots eleven negative images that mutate the actual outgoing frame immediately
before validation: kernel/wrong stack selectors, noncanonical and out-of-region
RIP/RSP, AC/DF, stale CR3/context, and a post-validation RIP mutation. Every
image must emit its typed rejection and terminate before the first CPL3 entry;
the post-validation image must also fail final-ELF policy inspection. CI
preserves each image, ELF/map, policy diagnostic, and serial log as integration
evidence, not as a refinement proof of assembly, QEMU, or hardware.
