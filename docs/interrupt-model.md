# Interrupt and exception model

`LeanOS.Interrupt` is a small total, sequential model for vectors 14 (page
fault), 32 (timer), and 128 (the existing `int 0x80` syscall relationship).
The companion `LeanOS.ExtendedState` classifier owns the admitted user-only
vector 6 (#UD) and vector 7 (#NM) extended-state denial cases. The separate
`LeanOS.PrivilegeEntryControl` classifier also admits the exact vector-6,
zero-error-code event produced by a raw `SYSCALL` or `SYSENTER` attempt under
its accepted AMD long-mode denial contract. Neither classifier makes vector 6
or 7 a generic recoverable exception: purpose, live controls, current subject,
CR3, and ordinary-stack identity must match the kernel-owned expectation.
Every other vector is a typed fatal outcome. Nested entry is disabled: an entry
while the trusted `entryActive` flag is set is fatal.

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
The machine implementation additionally rereads the complete fast-entry MSR
denial tuple at this sole outbound gate, after the extended-state checks and
immediately before consuming the entry latch. A mismatch cannot be repaired or
treated as an ordinary return rejection: it enters the absorbing fail-stop
path. The modeled composite operation wrapper carries no field that can rewrite
the accepted entry-control snapshot, and its preservation theorem covers every
registered nonfatal operation sequence. These are model and checked-machine
facts respectively; there is no proof that `rdmsr`, the assembly epilogue, or
the final ELF implements the model.
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

The later [`LeanOS.FaultDispatch`](fault-dispatch.md) composition consumes any
normalized contained-class result (vector 14 page fault, vector 0 divide
error, or vector 3 breakpoint) and the authoritative resumable scheduler state
as one transaction. It rejects stale kernel bindings without changing state,
requires the selected current subject to remain live and runnable, applies
whole-subject cleanup only to that kernel-owned subject, and returns either the
exact deterministic survivor context or typed idle, carrying the typed
contained reason without letting it select a cleanup variant. Every inbound normalizer
`.fatal reason` result, kernel-origin fault, and already-halted state sets or
retains the absorbing halt latch without exposing cleanup. Inbound failures retain the
exact `InterruptEntry.RejectReason`; kernel-origin and already-halted outcomes
use distinct fatal tags. Its proofs and traces do not refine x86 delivery,
the normalizer, machine context restore, or the final binary.

## Inbound entry manifest and normalization

`LeanOS.InterruptEntry` defines the complete ordinary boot manifest: vector 0
is a user-only DPL0 interrupt gate without an error word and with the shared
user-fault containment purpose — its DPL stays 0 so a CPL3 `int $0` cannot
software-select the divide-error path; vector 3 is the deliberately CPL3
software-callable DPL3 interrupt gate (an `int3` breakpoint requires gate
DPL 3) without an error word and with the same containment purpose — the
interrupt-versus-trap-gate choice is explicit (interrupt gate, IF masked on
entry) and `validateManifest` rejects any other DPL/type combination for
vector 3 and any DPL3 form of vector 0; vector 13
is a user-only DPL0 interrupt gate with a hardware error word and a typed
general-protection purpose; vector 14 is a DPL0 interrupt
gate with a hardware error word and user-fault or supervisor
diagnostic purpose; vector 32 is a DPL0 interrupt gate without an error word;
and vector 128 is the DPL3 interrupt gate with syscall purpose. The DPL3
inventory is exactly the breakpoint and syscall gates
(`only_breakpoint_and_syscall_are_dpl3`). All use
selector `0x08`, IST0, and interrupt-gate masking. Vector 8 remains owned by the
separate terminal IST1 protocol.

The contained synchronous fault classes are a finite typed vocabulary
(`ContainedReason`: page fault, divide error, breakpoint) keyed by
`containedReason?` on the manifest-bound vector only. Per the AMD64 manual,
only the page fault carries an architectural error word, and the saved RIP
names the faulting instruction for #DE/#PF but the following instruction
boundary for the #BP trap. The raw snapshot carries typed restart-class
evidence; the normalizer rejects a claim that disagrees with the reviewed
per-vector table (`wrongRestartClass`). These are normalized machine
inputs/assumptions: no modeled transition rewrites RIP, and containment always
terminates the faulting subject rather than resuming or retrying it.

Raw frames have two distinct constructors. A privilege-changing frame contains
RIP, CS, RFLAGS, RSP, and SS. A same-privilege frame contains only RIP, CS, and
RFLAGS; normalization cannot read or synthesize absent RSP/SS fields. Origin is
derived from the reviewed CS/CPL rule together with that constructor, never
from saved registers or user-looking words at later offsets. A kernel vector-14
frame becomes `diagnosticRecovery`, never user containment.

The total normalizer rejects a duplicate or unsupported manifest, unbound
vector/stub, wrong error convention, wrong restart-class evidence, truncated
or misaligned frame, wrong raw
shape or origin, out-of-bounds entry stack, nested entry, and uncleared AC/DF.
Accepted records copy subject, active address space/CR3, and stack identity from
`KernelContext`; attacker registers are absent from the function input. Lean
proves manifest validity, the exact DPL3 breakpoint/syscall gate inventory,
totality and
determinism, attacker-register erasure, rejection stability, same-privilege
confinement, nested/uncleared-state nonauthorization, exact kernel-context
binding, and manifest-bound vector/error-shape/restart-class binding for
accepted records (`accepted_binds_manifest_shape`,
`accepted_contained_error_shape`). These are model results only. Kernel-origin
divide errors and breakpoints are same-privilege frames under a user-only
origin policy and therefore terminal `wrongOrigin` rejections; only vector 14
retains the supervisor diagnostic relabeling.

### Canonical page-fault provenance

`InterruptEntry.normalizePageFault` is strictly layered on the accepted
ordinary vector-14 entry. It then decodes the architectural error word and
binds the CR2 sample. The bounded AMD64 profile admits `P`, `W/R`, `U/S`, and
`I/D`; an asserted `RSVD` indication has its own terminal rejection and every
bit at position five or above—including PK, shadow-stack, and SGX—is
unsupported and rejected. Read, write, or execute is derived from `I/D` then
`W/R`; no payload supplies an access label. Saved-CS origin must agree with
the error word's `U/S` bit.

The normalized record retains full CR2 and derives the page as unsigned
`CR2 / 4096`, accepting only canonical x86-64 linear addresses. Current
subject, address space, CR3, and WP/NXE/SMEP/SMAP come from
`PageFaultContext`; saved GPRs and diagnostics are explicitly confined away
from authorization. This provenance layer does not walk or mutate page
tables, invalidate TLB entries, retry instructions, or implement demand
paging.

`CanonicalPageFault` has a version-one fixed width of 19 `UInt64` words. Its
decoder rejects wrong versions, truncation or extension, a nonzero reserved
word, unsupported controls, noncanonical addresses, mismatched pages, and
access/protection/privilege relabeling. It also validates the reviewed saved
CS/RSP/SS shapes, canonical saved RIP, RFLAGS bit one, and nonzero
subject/address-space/CR3/stack identities. Lean proves width, valid-record
roundtrip, encoding injectivity, exact bit/page binding, that every decoded
record has a concrete accepted normalizer preimage, decode-failure no-action,
normalizer totality/determinism, and GPR/diagnostic confinement. The codec
action boundary additionally takes an independent trusted `PageFaultContext`,
renormalizes the decoded architectural fields under it, and authorizes only
when the resulting serialization exactly matches the decoded record. Thus
serialized subject, address-space, CR3, and WP/NXE/SMEP/SMAP fields remain
claims to check; a mismatch returns no authorization and leaves containment
state unchanged. The generated
five-word adapter is only a compact executable corpus projection, not the
canonical codec or a machine-refinement theorem; its scalar result nevertheless
attests the exact compact context plus WP/NXE/SMEP/SMAP and is checked
independently by the live C handler before containment.

The generated allocation-free `leanos_entry_demo` adapter is replayed in the
version-one oracle with valid syscall, user general-protection/direct-port,
user page fault, user divide-error, user breakpoint, timer, and diagnostic
records plus wrong binding, error shape, restart-class evidence, length,
alignment, origin (including kernel-origin #DE/#BP), spurious #DE/#BP error
words, stack, nested-latch, and AC/DF fixtures. The live boot image installs the
reviewed vector-0 (`isr0`, DPL0, no error word) and vector-3 (`isr3`, DPL3
software breakpoint) gates; both converge on the shared normalizer and the
generated typed dispatcher, and the real divide-error and breakpoint QEMU
scenarios boot them. `scripts/check-entry-policy.sh` enumerates the
final-ELF entry paths and requires cleanup, shared authorization, the typed
handler, and latch completion in that order, and additionally source-orders the
two contained integer-fault stubs (AC cleanup before shared normalization before
the operation-specific handler). `scripts/test-entry-policy.sh`
applies bounded one-field descriptor, path, error-shape, and TSS mutations to
controlled source snapshots and requires the production checker to reject each
with its vector and field/path diagnostic, including the vector-0/3 negatives:
missing, extra, swapped, user-callable (DPL3), wrong-IST, and wrong-type gates,
and handler-before-normalization or branch-around-cleanup contained paths. At
boot, `check_entry_manifest` decodes every present IDT entry and the relevant
TSS stack pointers and rejects unmanifested present gates.
`scripts/test-run-integer-fault.sh` drives the machine-level QEMU-runner
negatives for both scenarios — wrong delivered vector, synthetic error word,
wrong saved-RIP class, direct-called handler, page-fault reason substitution,
RIP-rewrite recovery, partial cleanup, attacker-selected survivor, stale
address space, corrupted peer canary, nested entry, forged or reordered records,
guest error, reset, triple fault, and timeout — where a forged serial PASS is
still rejected by the independent guest debug-exit status.

The bounded entry-adversarial image executes `int $14` and `int $32` from CPL3.
Both attempts must deliver vector 13 with the selector-derived error code, must
leave the privileged vector-14 and vector-32 handlers unreachable, and must
then complete the ordinary syscall path with its trusted subject/address-space
binding. Firmware PIC lines are masked when the IDT is installed; only the
preemption scenario remaps and deliberately unmasks IRQ0, preventing a legacy
IRQ from being confused with the dedicated vector-8 terminal protocol.

## Terminal non-maskable entry model

Vector 2 is not added to the ordinary manifest. `InterruptEntry.terminalManifest`
contains exactly one DPL0 interrupt gate with selector `0x08`, no hardware error
word, terminal-only purpose, and dedicated IST identity 2. The ordinary
manifest cannot authorize that entry, and IST2 is distinct from the existing
vector-8 IST1 machine protocol. The linker now owns a separate aligned 16 KiB
IST2 interval, the TSS selects its exclusive upper bound, and the IDT installs
only the reviewed vector-2 DPL0 interrupt gate for this terminal purpose. Boot
loads the fully initialized TSS before installing the IST2 gate and publishing
the runtime IDT, so the kernel's live vector-2 descriptor never references the
prior TSS. Vector 2 is also kernel-owned in both bootstrap phases: the
bootstrap tables route it to dedicated non-returning stubs, so no stale
firmware target is reachable after the first kernel `lidt`. The remaining
trusted window is the reviewed eleven-instruction entry prologue plus the
single-instruction long-mode IDTR handoff: the boot contract assumes that
firmware does not deliver
NMI before the first kernel `lidt` or exactly on that handoff boundary. That
residual window is outside the model and the QEMU monitor-injection evidence,
which begins only after `NMI-READY`; the separate mandatory `bootstrap64-nmi`
probe row supplies the bootstrap-window injection evidence through its own
exact `EARLY64-READY` checkpoint, and the `bootstrap32-ud` row drives a
real #UD through the 32-bit bootstrap table (see the boot-interrupt phase
section below).

`RawNmiFrame` always contains saved RIP, CS, RFLAGS, RSP, and SS. This includes
a CPL0 interruption because the selected contract assumes an IST switch; it
never reuses the ordinary same-privilege three-word shape. `normalizeNmi`
requires the exact descriptor and target, no error word, and a 40-byte
five-word frame starting at offset 8 modulo 16 whose end is exactly the
reviewed IST2 upper bound, without arithmetic wraparound,
canonical saved pointers, cleared AC/DF, matching user or kernel selectors,
and a kernel-owned current subject/address space. Its active CR3 and prior
execution mode are explicit trusted snapshot inputs. Attacker registers are
erased, and a claimed origin that disagrees with saved CS is rejected.
The canonical `0x900000..0x904000` interval is an abstract coordinate system
for normalized snapshots, not the linked IST2 virtual address. The final-ELF
policy separately checks the live linker interval, its 16 KiB size, and the
`end - 40` post-push frame relation. Constructing the normalized snapshot from
those machine coordinates remains an explicit trusted boundary.

An accepted result carries vector 2, terminal purpose, origin, IST identity,
all five saved frame words, current subject/address space, active CR3, stack
identity, and the interrupted `running` or `handling` mode. `NmiResultWords`
and `FailStop.NmiTerminalWords` are the version-1 fixed-width normalized-result
and halt-record vocabularies reserved for the later stateful corpus; the latter
includes the complete optional ordinary active frame rather than a lossy
purpose tag. This slice does not yet export or replay either encoding through
generated C. The scalar classifier accepts a typed `.halted` snapshot only to
exercise normalization; `FailStop.dispatchNmi` checks the execution latch first
and preserves an already-halted record without invoking that normalizer.
Malformed snapshots retain a typed normalization reason and authorize no
ordinary handler.

`FailStop.dispatchNmi` is separate from `beginEntry`, `finishEntry`, ordinary
fault containment, and scheduler dispatch. From `running` or any ordinary
`handling` state it clears return authority and the copy override, records the
accepted active CR3/stack identity and prior mode, and latches halt. The
complete composite theorem freezes lifecycle, capabilities, virtual memory,
IPC, scheduler, preemption, and the current subject/address-space/kernel-stack
projection, then absorbs every typed suffix. A repeated modeled NMI after halt
returns the original terminal record unchanged; because this model has no NMI
return, it assumes a second physical NMI remains architecturally blocked rather
than modeling nested-NMI recovery.

These are sequential Lean model properties. NMI may be selected between atomic
composite steps or while the modeled mode is `handling`; this is not a theorem
about arbitrary compiler instruction boundaries or partially committed C
mutations. Physical NMI delivery, blocking/coalescing, descriptor semantics,
TSS/IST switching, frame construction, stack mapping, assembly, generated C,
compiler/linker behavior, QEMU, firmware, and hardware remain trusted or future
tested boundaries. The bounded classifier is now replayed through hosted
generated C and the final ELF under QEMU. A mandatory probe image additionally
publishes a CPL0 `handling` boundary with IF clear; the evidence runner injects
a real QEMU NMI, observes the five-word IST2 frame and one terminal record, and
rejects any return or post-terminal output. This is integration evidence, not
a proof of x86 delivery, coalescing, or emulator correctness.

The retained QMP exchange contains the greeting, the capability command and
reply, and the single `inject-nmi` command. It normally also contains QEMU's
empty success reply. The terminal guest can reach `isa-debug-exit` before QEMU
flushes that reply, however, so EOF or a connection reset immediately after
the recorded command is also admitted. That transport race is never sufficient
evidence: the runner still requires QEMU's exact NMI terminal exit status and
the unique full guest terminal record, and rejects every other exit or
transcript shape.

## Boot-interrupt phase ownership

`LeanOS.BootInterruptPhase` fixes the finite publication chain
`inherited → bootstrap32 → bootstrap64 → runtime → terminal`. Each owned phase
names its permitted table, descriptor width (`legacy8` or `long16`), stack
assumption, vector-2 ownership, and terminal target; only the runtime phase
may ever carry return authority, and the `contract_table` theorem pins those
facts. `publish` accepts exactly the next chain step — the runtime manifest
additionally requires its TSS, IST-stack, and gate-manifest prerequisites —
and every wrong or premature publication fails closed into the absorbing
terminal latch. `dispatch` delegates runtime events unchanged to the separate
ordinary/terminal runtime contracts, types the inherited window as unowned,
and latches every bootstrap event immediately. Lean proves totality,
determinism, publication monotonicity with an unreachable inherited phase,
business-state preservation, that no step arms return authority, that events
never advance the chain, immediate terminal latching with the bounded reason,
and absorption of every operation suffix after a latch; concrete witnesses
cover both bootstrap phases and the orderly chain. The 18-vector
`bootphase.*` block replays the allocation-free `bootPhaseDemo` adapter
through the hosted oracle and the boot image with an opaque business token
that must round-trip unchanged.

The machine implementation makes the phases mechanically recognizable. The
entry prologue executes only `cli`, one `lgdt` of the kernel GDT, a far jump
onto the kernel 32-bit code selector, five segment loads, the bounded boot
stack pointer, and then the first kernel `lidt` of the statically initialized
`boot_idt32`; the Multiboot2 handoff registers are stored only after the
`boot_idt32_published` label. All 256 legacy gates are DPL0 interrupt gates
through selector `0x38`; vector 2 targets `boot_early_isr2_32` and every
other vector the phase catch-all. The long-mode switch publishes `boot_idt64`
in the instruction immediately after the paging CR0 write, so exactly one
instruction boundary separates long-mode activation from kernel 16-byte-gate
ownership; its 256 gates use selector `0x08` with IST 0 because no TSS exists
yet, and delivery stays on the live boot stack. Each of the four bootstrap
stubs clears interrupts and DF, emits one fixed `LEANOS/18 EARLY-TERMINAL`
record naming its phase, table, width, vector class, stack, and target,
requests a phase-typed debug exit (`0x16` for bootstrap32, `0x17` for
bootstrap64), and halts; no stub pushes, calls, returns, or touches runtime C
state, the Lean runtime, the ordinary entry stack, or the later IDT/TSS, and
outside the two dedicated probe images below no stub reads the exception
frame. `privilege_init` then replaces `boot_idt64` with
the runtime manifest only after the TSS, IST stacks, and checked gate
manifest exist, with no intermediate reload of any earlier table.

`scripts/check-early-idt-policy.py` runs inside the shared image policy for
every ELF variant. It decodes both bootstrap tables byte-for-byte against the
linker-pinned stub slots (rejecting wrong selector, DPL, type, IST, reserved
words, or targets), verifies both IDTR pointer images, disassembles the
32-bit prologue in its real mode to require the reviewed pre-`lidt`
allowlist, the exact `boot_idt32`/`boot_idt64` publication order, and the
one-instruction CR0-to-`lidt`-to-far-jump handoff, forbids `sti`, port I/O,
`int`, calls, and returns in the entry interval, bounds all four stubs as
contained non-returning terminal CFGs, and inventories every `lidt` (exactly
two bootstrap publications plus the single runtime publication) and rejects
any `sidt`. `scripts/test-early-idt-policy.sh` rebuilds controlled negatives
— deleting or delaying the first `lidt`, swapping the tables, DPL3 or
IST-bearing bootstrap gates, re-pointed vector-2 gates, `iretq`/`call`/escape
edges in stubs, early `sti`, and early PIC access — and requires the exact
policy diagnostic for each. The stub serial/debug-exit instructions are
inventoried in every direct-port site manifest.

Two dedicated probe images demonstrate both sides of that handoff under QEMU.
The `bootstrap32-ud` image compiles `boot.S` with
`LEANOS_BOOTSTRAP32_UD_PROBE`: one real `ud2` becomes the first instruction
after the first kernel `lidt` — at the `boot_idt32_published` boundary,
before any page-table, CR, MSR, PCI, port, or generated-code operation — so
vector 6 must reach the pinned 32-bit catch-all stub through `boot_idt32` on
the live boot stack. The `bootstrap64-nmi` image compiles with
`LEANOS_BOOTSTRAP64_NMI_PROBE`: immediately after the boot-stack publication
in the long-mode entry — with `boot_idt64` live, no TSS or IST, IF still
clear since the entry `cli`, and the runtime `lidt` unpublished and
unreachable past a halt loop — the guest emits one exact
`LEANOS/18 EARLY64-READY` record and halts. `scripts/run-bootstrap64-nmi.sh`
extends the `run-nmi.sh` discipline: it waits for that exact record and the
QMP socket, negotiates capabilities, issues a single `inject-nmi`, and
accepts no fixed sleeps, synthetic `int $2`, direct handler calls, or C-set
flags, so vector 2 must cross the masked window through `boot_idt64` to the
pinned bootstrap64 stub. In these two images only, the targeted stub
additionally attests the exact architectural frame with decode-stable reads
before claiming its record — the no-error `EIP/CS/EFLAGS` #UD shape at the
probe opcode for bootstrap32, and the IST-0 five-word boot-stack shape with
`CS=0x08` and IF clear for bootstrap64 — and any other shape emits a typed
`status=FAIL reason=probe-frame-policy` record with the distinct debug exit
`0x18`. The accepted probe terminals are versioned and early-only:
`phase=bootstrap32 … vector=6 reason=invalid-opcode … return=none` with debug
exit `0x16` (host status 45), and `phase=bootstrap64 … vector=2
reason=non-maskable-interrupt … return=none` with debug exit `0x17` (host
status 47). Both stay disjoint from the runtime `LEANOS/17` `prior=handling
ist=2` vocabulary, so no later runtime delivery can satisfy either mandatory
row in `scripts/emulator-evidence-matrix.tsv`; each runner additionally
rejects duplicate, reordered, forged, runtime, or post-terminal output and
any other exit status.

`scripts/check-early-probe-policy.py` binds each probe image to that exact
shape in the final ELF and source: the `ud2` placement at
`boot_idt32_published`, the readiness site at its exported symbol after the
stack publication, the halt loop dominating the otherwise-unreachable
`kernel_main` call, every instruction of all four stubs and the long-mode
entry tail, the frame-guard immediates, both debug-exit codes, and the exact
record bytes. `scripts/test-early-probe-policy.sh` rebuilds sixteen
controlled negatives — an `int $6` substitute, moved or pre-`lidt` probes,
dropped frame guards, wrong success and failure exit codes, forged terminal
and readiness records, a readiness site moved before the stack publication or
behind an extra instruction, a skipped halt loop, a synthetic `int $2`, a
duplicate output site, and cross-probe contamination — and requires each
exact diagnostic. The probe serial and debug-exit sites are inventoried in
dedicated direct-port manifests. The two runs are the machine counterparts of
the existing `bootphase.noerror-fault-bootstrap32` and
`bootphase.nmi-bootstrap64` oracle rows.

These checks and records are integration evidence: descriptor-load and IDTR
semantics, delivery inside the residual prologue/handoff window, x86/QEMU
behavior, and the final binary remain trusted. The phase markers, fixed
records, debug-exit codes, and pinned stub addresses are deliberately stable;
the two early-injection scenarios above consume them. QEMU demonstrates two
selected executions — a pre-paging #UD and one masked-window NMI — and does
not prove that the binary refines the phase model, that every early fault at
every bootstrap instruction is contained, or anything about GRUB's own IDT,
firmware/SMM, physical NMI, machine checks, nested NMI, or SMP.

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
When scenario-specific compilation produces multiple static `.su` records for
one function, the gate conservatively charges the largest reported usage;
inconsistent static/dynamic qualifiers remain rejected.
The extended-state image has a companion reviewed call graph for vectors 6
and 7 through peer restoration and the sole user-return validator, so both the
ordinary fail-stop build and the accepted denial scenario receive final-ELF
reachability and stack-budget checks.
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
Lean layout/budget model. [ADR 0015](adr/0015-guarded-privilege-entry-stack.md)
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
return are additional trusted machine operations. The fast-entry vector-6 path
also trusts the selected CPU feature report, the complete EFER/STAR/SYSENTER
MSR read/write semantics, the architectural claim that the disabled raw
instructions fault before consuming an alternate CPL0 target or stack, and the
single allowlisted probe opcode. Controlled source and runner fixtures remove
those bindings, mutate the vector/error shape or controls, claim an unexpected
target, or reorder the handler before cleanup/normalization and require typed
policy rejection.
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
