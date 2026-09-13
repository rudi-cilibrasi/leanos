# ADR 0017: Qotom kernel page tables and bounded copy windows

## Status

Proposed for review under [#329](https://github.com/rudi-cilibrasi/leanos/issues/329).
This is a design gate for #291 and #332. The page-table projection, transition
model, and first production-bound root builder now exist. Entry and return
integration remain unfinished. This record does not authorize CPL3 on Qotom.

The `qotom-copy-roots-v1` control checkpoint now validates CR0.WP, EFER.NXE,
disabled interrupts, and disabled CR4.SMEP/SMAP/PCID/PGE before making the exact
CR4.SMEP transition. It reads back the result through a generated Lean boundary
and reports both roots and CPL3 authority as zero. The following opt-in
checkpoint constructs the roots and exercises a bounded transfer, while still
withholding CPL3 authority.

## Required protection and alternatives

The first Qotom scenario should retain architectural denial of ordinary kernel
access to user-owned memory outside a validated copy. Its J1900 has SMEP and NX
but no SMAP. [ADR 0006](0006-smap-user-copy-window.md) relies on SMAP to enforce
that denial while AC is clear. The same instructions and claim cannot be reused
on this CPU.

Removing STAC/CLAC and keeping only software bounds checks would preserve the
modeled explicit-copy policy, but ordinary supervisor loads could still reach
mapped user memory. That weaker lab claim is possible under the issue's scope,
but it does not meet the protection selected here. Merely changing a user leaf
to supervisor is also insufficient: supervisor code can still access it.

Use separate page-table roots instead. The closed kernel root omits every
virtual alias of each user-owned physical frame, including supervisor aliases
in the identity map. A bounded copy root adds only dedicated supervisor, NX
aliases for pages covered by a validated copy. Subject roots remain distinct.
This design requires auditing physical aliases, not only virtual U/S bits.

## Proposed transition contract

1. Before CPL3, publish the complete live user-frame inventory and construct a
   closed root with those frames absent at every virtual address. Use only 4 KiB
   leaves; reject large-page mappings rather than leaving an unexamined alias. Keep kernel
   code, entry stacks, TSS, IDT, page tables and required device mappings available
   in each root where they are used. Reject any overlap between protected frames
   and indispensable kernel frames.
2. Every entry from a subject switches to the closed root before calling C or
   dereferencing a subject-supplied pointer. The short transition uses only
   fixed trusted operands and shared entry mappings. Entry cleanup verifies the
   selected root. No no-SMAP entry path executes STAC or CLAC.
3. Validate the entire caller-owned buffer with the existing `UserCopy.validate`
   contract: at most 16 bytes, canonical and nonoverflowing bounds, current
   address-space/lifetime authority, and direction-appropriate permissions.
   Preserve its cross-page case, which needs at most two copy aliases. Validation
   happens under the closed root; a rejected request changes no memory.
4. Hold the validated mappings and frame lifetimes stable. The initial mechanism
   is BSP-only, with maskable interrupts disabled during the transaction and DMA
   quarantined by the selected platform policy. No allocation, callback, subject
   switch or mapping mutation may run while the window is open.
5. Publish the bounded aliases and select the copy root. The transfer stub uses
   the validated byte count and offsets, not the original user virtual pointer.
   It may read source pages or write destination pages according to the admitted
   direction; it cannot execute those aliases. The kernel buffer remains a typed
   bounded object. Restore and verify the closed root before ordinary C resumes.
6. For the first implementation, an interrupt or fault during the transfer aborts
   the transaction and terminates the scenario. Entry first attempts the fixed
   closed-root transition. A failed cleanup enters an assembly terminal path;
   it must not return to C or CPL3 with an unverified copy root. Do not claim that
   a fault rolls back bytes already copied: the model must bound any partial
   effects to the validated prefix and preserve all other memory.
7. A subject return selects only that subject's validated root in the final
   assembly return sequence. No arbitrary kernel work may occur between that
   switch and IRET. Nested exception paths must obey the same closed-root rule.

Require PCID and global-page translations disabled for this initial strategy,
with checked control readback and the required translation invalidation at each
root transition. Do not infer effective cleanup from a CR3 address comparison
alone. The trusted page-table construction and invalidation operations must
establish which translations can actually remain usable.

## Architecture basis and claim delta

Intel's [System Programming Guide, Volume 3A](https://cdrdv2-public.intel.com/819714/253668-sdm-vol-3a.pdf),
sections 4.6 and 4.10.4, supplies the architectural access-right and invalidation
rules on which this proposal depends. Absent translations deny access; clearing
U/S does not deny supervisor access. CR3 invalidation behavior depends on PCID
and global-page controls, so those controls are part of the strategy rather
than an assumed side effect. These rules motivate the proposed construction;
they do not verify our page tables, assembler, compiler or processor.

The proposed Qotom claim is denial through missing translations under a closed
kernel root, with bounded temporary aliases for explicit copies. It is not a
claim that SMAP is enabled, that AC controls access, or that a q35 SMAP fault probe
passed. This is an architectural access claim, not a speculative-execution or
covert-channel claim. Existing q35 SMAP evidence keeps its original meaning.

`KernelUserRoot.close` models the first projection. Given a complete protected
frame inventory, it removes all aliases of those frames and preserves retained
leaves. Its access-denial theorem uses `X86PageTable.classify` without assuming
SMAP or AC. The inventory's completeness, actual root installation, TLB state,
copy aliases, byte transfer, exceptional cleanup and return ordering are outside
that initial theorem. Those obligations remain before any runtime admission.

## Evidence required before enabling CPL3

The remaining model must connect validated copy authority to the selected root,
alias permissions, byte progress, interrupted/faulted copies and cleanup results.
It must prove nonamplification, exact or bounded-prefix footprints, preservation
outside that footprint, closed-root restoration and terminal behavior after
cleanup failure. The current atomic SMAP model does not establish these new
exceptional-path properties.

Lean and generated C must agree on the complete strategy selection. Execution
fixtures without SMAP must cover permitted and forbidden buffers, zero/maximum
lengths, page boundaries, overflow, stale authority, injected interruption/fault,
cleanup failure and attempted access through an omitted supervisor alias.
Final-object checks must cover all reachable entry, copy and return paths,
including NMI and double-fault handling, and reject unsupported STAC/CLAC or
CR4.SMAP writes on the selected path. Records must name the new strategy and
report SMAP as absent. Physical Qotom evidence remains required. Until these
obligations are discharged, retain a typed pre-CPL3 rejection.

The intermediate serial record `NO-SMAP-CONTROL profile=qotom-copy-roots-v1`
reports the live controls and fixed bounds of sixteen bytes and two aliases. A
successful record terminates at `qotom-copy-roots-pending`; it cannot be read as
root publication or CPL3 acceptance.

### Production-bound root construction checkpoint

The opt-in `COPY-ROOTS profile=qotom-copy-roots-v1` step derives five protected
frames from the linked user A/B text and stack ranges. It accepts only the exact
4 KiB-leaf source hierarchy for the initial 16 MiB arena, rejects overlapping
root storage and malformed ancestors, removes every present protected-frame
alias from both output roots, and adds exactly two supervisor/NX aliases to the
copy root at source-absent slots. Validation completes before either output root
or its result record is written.

The Qotom wrapper separately checks that both eleven-page output structures are
page aligned, below 16 MiB, and mapped as supervisor writable NX storage. It
scans every output leaf, writes a known value across the two user A stack pages,
and invokes the existing audited transfer helper through immutable byte operands.
Success requires all sixteen bytes to match and CR3 to read back as the closed
root after the helper reloads closed, copy, then closed roots.

The generated boundary requires the exact observed counts (five protected
frames, three removed aliases, 4,088 retained present leaves and two temporary
aliases), distinct aligned roots, both complete scans, the sixteen-byte result,
and final closed-root readback. Only then may the serial record mark both roots
published. Word six of the boundary always returns zero, so this checkpoint
cannot authorize CPL3. A successful record terminates at
`qotom-entry-integration-pending`.

This checkpoint does not establish that the linked ranges are a complete future
subject-frame inventory, that every entry path switches to the closed root, or
that subject return selects an admitted subject root. Those remain the next
machine-integration obligations. The generated boundary also consumes trusted
scalar observations; its proof does not establish the C builder, scans, assembly,
compiler, CR3 invalidation semantics, or physical execution.

The later opt-in exception checkpoint described in
[`qotom-exception-integration.md`](../qotom-exception-integration.md) returns
through the audited primitive a second time, executes a real CPL3 `UD2`, and
requires the vector-6 assembly stub to reload/read back the closed root and
validate the exact hardware frame before emitting its direct terminal marker.
This is checked machine evidence layered on the non-authorizing scalar
boundary. It does not add asynchronous routing or production dispatch authority.

### Sequential interruption model

`LeanOS/UserCopyPrefix.lean` models a possible completed prefix in both copy
directions, after validating the entire request with `UserCopy.validate`. It proves
that rejected requests and zero progress change no state, that the source memory domain
and mapping authority remain unchanged, and that destination bytes outside the
completed prefix retain their original values. Full progress agrees with the
existing complete-copy models, and excessive progress counts saturate at the
requested length. Tests interrupt a two-page copy at the page boundary and
reject a request whose second page is unmapped before writing its first byte.

This model describes possible partial effects. It neither authorizes resumption
nor proves actual instruction ordering, root closure, or exception cleanup.
The runtime refinement must establish those obligations separately.

`LeanOS/UserCopyTransaction.lean` composes those effects with an abstract
termination contract. After successful validation, only an exactly completed
transfer, a finished stop and a verified-closed cleanup report permit a normal
return. Interruptions, faults, incomplete or excessive progress, and unverified
cleanup terminate. Termination retains partial effects rather than rolling
back. Rejected validation leaves memory unchanged under the initial closed
root, without opening a window or consulting a subsequent cleanup report.

The cleanup report is an explicit trusted-boundary assumption. These proofs do
not establish that hardware translations are closed. The runtime must produce
that report from the full root publication and invalidation contract; a CR3
address comparison alone is insufficient. Tests cover both directions across
all three stop kinds, both cleanup reports and four progress counts (48 cases),
including partial effects after faults and unsuccessful cleanup.

### Bounded alias planner

`LeanOS/UserCopyAliases.lean` derives distinct physical frames from the complete
validated location list and admits at most two. It rejects noncanonical or
occupied reserved slots, frames outside the supplied protected inventory, and
unrepresentable frame numbers. It constructs only supervisor/NX leaves, writable
only for a request validated with write permission. Proofs connect every added
alias to a validated location and preserve all mappings outside the two slots.
The modeled walker denies execution and user-mode reads through these aliases.

The planner assumes that its supplied kernel table is already closed; it does
not certify that premise or install the root. Aliases expose whole pages while
open. The transfer stub's validated count and offsets must constrain byte
accesses inside those pages. Connecting those operands to the progress model,
publishing translations, and proving actual cleanup remain runtime obligations.

`LeanOS/UserCopyOperands.lean` connects accepted plans to byte-level operands.
Each operand selects a reserved alias slot that maps the exact validated frame
and preserves its bounded physical offset. The sequence has one operand per
requested byte, in validated order, and its prefixes match the location prefixes
used by the partial-copy model. A buffer starting in a later user page still
uses the first alias slot; the operand does not reuse its original virtual page.
Tests cover zero and maximum lengths, single-page offsets, cross-page ordering,
and partial prefixes. Actual transfer instructions must refine this operand
sequence under the established root and stable authority assumptions.

### Root publication and stale translations

`LeanOS/KernelRootPublication.lean` models cached hits without revalidating them
against current page tables. Its negative example preserves a usable protected
frame after table replacement alone. An accepted publication requires PCID and
PGE disabled and returns a mandatory root-reload effect plus the post-flush
state. Even reuse of the same root requires that effect. Protected-frame denial
then follows from the closed-root projection with arbitrary prior cache entries.
Unsupported controls reject without mutation; rejection does not imply closure.

As with the existing invalidation model, the machine must actually execute the
returned effect before publishing the returned logical state. The target's
construction, control readback, instruction execution and processor invalidation
remain trusted runtime obligations. The model does not turn a CR3 comparison or
a desired post-flush state into evidence of completed hardware cleanup.

### Generated-C model replay

The test-only `leanos-copy-roots-replay` executable runs the composed alias,
operand, partial-copy, transaction and root-publication models after Lake
compiles them to C. Its 28 checks include all 48 transaction outcomes. The same
corpus also reduces to success in Lean's kernel. It covers cross-page operands,
read/write and execution permissions, partial-copy suffix preservation,
whole-request rejection, zero length, missing inventory, occupied slots, stale
cached authority and required reloads. The repository check script builds and
runs the executable.

This is generated-C replay of the models, not a production boundary ABI, a
freestanding runtime test or execution evidence for CR3/copy instructions.

### Isolated root-reload primitive

`experiments/copy-roots/reload.S` is an isolated assembly prototype for the
publication effect. It requires IF clear, PCID/PGE disabled, and a nonzero,
page-aligned trusted PML4 address inside the initial 16 MiB arena. It always
reloads CR3, including same-root transitions, then checks the root readback.
Invalid preconditions or a readback mismatch enter an assembly-only CLI/HLT
loop. The trusted caller must establish the target's full page-table contents,
shared code/stack mappings, authority and exception-entry requirements.

`scripts/check-copy-root-reload.py` checks the complete linked instruction
sequence, guard targets and terminal loop. Eleven assembled mutations exercise
missing reload/control/alignment/readback checks, an incorrect arena bound,
premature or terminal returns, unsupported STAC and undecodable trailing bytes.
These are static object checks. Integration with every entry/copy/return path remains required before linking
this into a production boot image.

`scripts/test-copy-root-reload-qemu.py` now executes that primitive in a small
Multiboot2 fixture with 4 KiB leaves, one CPU and SMAP disabled. The positive case
primes a translation, changes its PTE and reloads the same root, then switches
to a distinct root and verifies the observed backing frame in both cases.
Six rejection cases cover zero/unaligned/out-of-arena roots, PGE, PCID and IF.
They require QMP register evidence of a halted CPU inside the exact terminal
symbol; silence or elapsed time alone cannot pass. A missing-reload mutation
must fail the backing-frame test with its explicit failure marker and exit code.

The runner retains command lines, debug bytes, terminal registers and a summary
with ELF/object hashes and the QEMU version. All twelve cases run in the normal
repository checks. These isolated handlers do not establish production NMI/fault-entry integration,
CPL3, complete copy windows, physical Qotom behavior or production image policy.

Additional execution cases require page faults after closure through both the
temporary alias and the original identity address. For these cases, the target
root removes the test alias and the identity mappings of both backing frames.
The page-fault handler checks the exact faulting RIP, CR2, not-present supervisor
read error code and selected root before reporting success. A readback-mismatch
mutation must reach the primitive's terminal loop.

The NMI case primes the permissive mapping, then the runner injects an actual
NMI through QMP. Its fixture handler selects the fixed closed root before any C
call and attempts the protected read, which must reach the same checked
page-fault path. It terminates the fixture rather than resuming the interrupted
context. The test uses a shared trusted CPL0 stack and does not establish the
production IST/TSS, nesting, double-fault or CPL3 return contracts. GCC and pinned
Clang 18 pass all twelve execution cases with SMAP disabled.

### Bounded operand-transfer prototype

`experiments/copy-roots/transfer.S` consumes a trusted immutable sequence of
at most sixteen source/destination byte-address pairs. These must already be
admitted `UserCopyOperands` results, with stable ownership and mappings. The
assembly interface itself does not validate user buffers or manufacture copy
authority. Code, stack, operands and exception data must remain mapped under
both supplied roots.

The helper first reloads the closed root. Zero length returns without opening
the copy root; excessive length terminates. For a nonempty request it reloads
the copy root, transfers the pairs in order, and reloads the closed root before
normal return. Reload guards and readback use the existing primitive. The helper
contains no STAC/CLAC and does not set CR4.SMAP. A linked-instruction checker
verifies its complete body, direct branch/call destinations and reload/terminal
callees. Twelve mutations challenge bounds, transfer width and stride, branch
conditions, missing reloads, cleanup operands, unsupported instructions and
premature return; the eleven original reload mutations remain separate.

The QEMU driver tests both directions at lengths zero, one, eight and sixteen,
including two-page transfers. The closed root omits all test-frame aliases;
the copy root exposes only the two dedicated supervisor/NX aliases. Destination
sentinels and copy-out source bytes are checked. An actual post-return read must
fault under the already closed root; that probe handler does not repair closure.

Oversized requests and zero, unaligned or out-of-arena copy-root arguments must
halt before changing either memory domain. A missing second alias faults after
eight completed bytes. A separate instrumented helper pauses at the same prefix
so QMP can inject NMI after confirming the checkpoint's halted instruction
pointer. These fixture handlers first select the fixed closed root, then halt
without resumption. Physical memory dumps verify the exact completed prefix,
unchanged source and unchanged destination surroundings. This samples one NMI
checkpoint, not every possible interruption window.

A mutated final cleanup operand must halt after the full transfer while the copy
root remains selected. Its report explicitly marks closure as false; terminal
behavior must not be mistaken for successful cleanup or rollback. The runner
records QMP terminal state, memory dumps/hashes, exact commands, ELF/transfer-object
hashes, source and driver hashes, and compiler/QEMU versions. It distinguishes
normal exits from observed halted guests.

The normal repository checks run the instruction audit and all 22 execution
cases. `LEANOS_CC=clang-18 python3 scripts/test-copy-root-transfer-qemu.py`
selects the second compiler; compiler-specific output directories preserve both
runs. The NMI cases install a 64-bit TSS and select IST1: a dedicated supervisor,
NX stack retained in both roots, with absent guard pages below and above it.
The handler first reloads the closed root, then checks its five-qword hardware
frame and the saved ordinary-stack pointer. The QMP observer independently
requires the halted stack pointer at the IST frame and reads both roots' leaf
entries to verify the guarded NX mapping. Other fixture paths still use the
trusted ordinary CPL0 stack.

This is one injected NMI at a known copy checkpoint. It does not establish
safe entry at every instruction, nested-exception handling, stack-exhaustion
recovery, or double-fault handling. Production IST/TSS, validation-to-operand
binding, actual root construction and protected-frame inventory publication
still require integration. This
prototype does not enable production or physical CPL3 admission.

### Checked indispensable leaf construction

`KernelUserRoot.closeChecked` checks the selected scenario's exact indispensable
leaf list against the supplied source table and rejects any listed leaf whose
physical frame is protected. It returns no candidate for absent or stale leaves,
permission drift, or protected/kernel overlap. An accepted candidate is exactly
the existing closed projection; its required leaves are preserved and refer to
unprotected frames. Replay includes two supervisor aliases of one protected
frame, both removed together, and the rejection cases above.

This checks the supplied leaves, not inventory completeness or ancestor access
permissions. The caller must establish the full required mapping inventory,
valid ancestors and live protected frames for the selected scenario. Publication,
TLB invalidation and production entry/copy/return integration remain separate
obligations; this model does not authorize Qotom CPL3.

### Return preparation under the closed root

`KernelRootReturn.prepare` composes the existing `Interrupt.validateUserReturn`
with root publication planning. The currently active root must equal the trusted
closed-root identity, with interrupts, PCID and global pages disabled. The
pending subject-root identity is independently validated by the existing return
request, must be nonzero and aligned, and must resolve in the trusted immutable
root registry. The resulting plan retains the exact request and original state,
and requires a root reload with an empty modeled cache.

The tail has only awaiting-reload, awaiting-IRET, user and terminal phases. A
verified reload must precede IRET completion; interruption, failed reload and
out-of-order events terminate. Tail steps preserve the exact plan and accept no
replacement request. This is a sequential effect protocol, not proof of hardware
interrupt timing or atomic IRET. The verified-reload event must come from the
checked machine primitive. Terminal cleanup must use the separately established
entry path; the model does not claim that a terminal state itself closes roots.

Root registry provenance, protected-frame exclusion, subject-table ownership,
lifetime stability, full saved-register preservation and actual instructions
remain implementation obligations. The 16 replay cases use an empty toy table
to exercise selection and sequencing; they do not establish executable user
mappings. Production return integration must validate under the closed root,
then perform the final switch without intervening C callbacks. The current q35
return path still runs C under the subject root and retains its existing checks.

### First Qotom entry/return checkpoint

The next lab-only checkpoint installs one DPL3 `INT 0x80` gate plus terminal
NMI, invalid-opcode, double-fault, general-protection and page-fault gates. The
ordinary entry assembly saves all fifteen general-purpose registers before
using scratch state, records the incoming subject root, reloads and reads back
the published closed root, and only then calls the C dispatcher. The existing
audited return primitive performs the final subject-root reload, restores the
complete saved bank and executes `IRETQ` without another C call.

A CPL3 probe enters twice with IF disabled because this synchronous checkpoint
has not admitted asynchronous interrupt routing. The first call returns a fixed result; user code
checks that result and every other saved register before the second call. The
second dispatcher validates both hardware frames, both incoming-root reports,
the active closed root and the full register bank before publishing the bounded
checkpoint. Terminal exception gates reload and read back the closed root and
halt without resuming. The linked-object audit checks those instruction shapes,
the existing return primitive and ten unsafe mutations. No path contains
STAC/CLAC, and the scalar Lean boundary continues to publish zero general CPL3
authority.

This checkpoint exercises one synchronous entry and one completed return on the
Qotom. Its scalar boundary remains deliberately nonauthorizing. The later
terminal `#UD` experiment and blocking-IPC profile are separate opt-in images,
so evidence from either cannot silently promote this checkpoint.

### Fixed Qotom blocking-IPC profile

The next selected profile adds a distinct writable copy-out root, two complete
saved-context banks, one recoverable CPL3 page-fault path, and bindings to the
existing generated blocking-IPC and capability-reuse adapters. It admits only
the eight-syscall, two-subject trace in
`scripts/expectations/blocking-ipc.transcript`. The page fault is synchronous;
vector 32 remains absent, both PIC masks remain `0xff`, IF remains clear, and no
PIT setup is admitted.

Successful completion emits the canonical structured PASS record and halts
with `cli; hlt`. The physical profile does not retain the q35 debug-exit path.
The external watchdog resets the board and returns to FreeBSD, which provides a
bounded recovery mechanism rather than a kernel scheduling event. Linked audits
check entry/root transitions, the exact retained model-call counts, absence of
timer programming, and the terminal loop. The capture decoder derives the
semantic suffix from the q35 expectation template and separately requires the
loaded ELF digest, quiet interval, boot-epoch change, consumed request, and SSH
recovery. The complete machine path and q35 comparison are in
[Qotom blocking IPC integration](../qotom-blocking-ipc-integration.md).
