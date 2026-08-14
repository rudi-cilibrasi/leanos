# Model-oracle replay

`LeanOS.Oracle` is the version-one, bounded corpus for every currently exported
freestanding adapter: `KernelTransition.bootTransition` and
`Syscall.syscallDemo`, `IPCSyscall.ipcDemo`, and
`Preemption.preemptionDemo`, `Preemption.resumableDemo`, and
`BootAllocation.check`, `Interrupt.userReturnDemo`,
`InterruptEntry.entryDemo`, `BlockingIPC.blockingIpcDemo`,
`CapabilityReuse.capabilityReuseDemo`, `ExtendedState.denialDispatchDemo`,
`PrivilegeEntryControl.controlDemo`, `FaultDispatch.faultDispatchDemo`, and
`DirectPortIO.directPortIODemo`, `InterruptEntry.nmiDemo`,
`InterruptEntry.bootPhaseDemo`, and
`StaleTranslation.staleTranslationDemo`, and
`InterruptEntry.pageFaultDemo`, plus the stateful
`CompositeDispatcher.dispatch`. Its stable
380-vector order covers accepted calls,
typed decoding failures, invalid state and permission encodings, boot-handoff
and publication-order failures, both bounded A/B preemption directions, and
maximum `UInt64` boundary words, plus accepted initial/syscall/scheduler returns
and adversarial return frames and contexts. The fault-dispatch records include
typed kernel-origin and malformed-frame fail-stop cases, stale authoritative
bindings, empty dispatch, and an accepted peer-context/resource witness. The
accepted word independently attests B's complete saved frame/register canaries,
capability slot, owned memory and frame, mapping, and endpoint provenance after
A's cleanup. The containment guest retains that exact adapter word across B's
checked context copy, CR3 switch, and common validated return instead of
maintaining a parallel C live/runnable/queue/context/resource projection. The
composite corpus includes an accepted page-7 unmap whose typed reply requires
the kernel-derived address-space-2/page-7 invalidation effect, plus an absent-page
rejection that preserves the canonical state and requests no effect. Both are
derived from the same authoritative replay used by the scalar dispatcher; the
C harness stores no mapping or TLB shadow state. The
32 entry-control records cover the canonical denial tuple, every modeled
CPU/MSR/boot-evidence mutation, return authorization, user and kernel denial
events, stale bindings, alternate-target/stack separation, and post-fatal
absorption. The 18 boot-interrupt-phase records cover every orderly and wrong
table publication, missing runtime prerequisites, bootstrap NMI and
representative error-code shapes in both bootstrap phases, the typed unowned
inherited window, runtime delegation, repeated terminal events, attempted
progress after the latch, malformed phase codes, and an opaque business token
that must round-trip unchanged. The Lean checks evaluate every expected result
from the adapter definition and connect the accepted and rejected examples to
the source models.

The final fifty-six composite-dispatch records are the version-one traces
for the shared stateful boundary. Six input words carry a canonical state token,
command tag, and four scalar arguments. The seven positive sequence edges create
one subject, observe typed unknown-syscall and malformed-map rejections, run
the scheduler observation, terminate the subject, enter a fatal kernel
page-fault state, and verify that a subsequent scheduler request is rejected
by the absorbing fatal latch. Each state token materializes the complete
`FailStop.CompositeState` by replaying the exact
`FailStop.authoritativeGate`; it is not a reduced transition or a C shadow
state. Ten negative records reject stale replay, cross-trace splicing,
nonzero reserved arguments, forged context arguments, wrong versions, reserved
state or command bits, maximum words, and unknown commands before policy
evaluation. Lean proves canonical complete-state, command, and reply round
trips and injectivity over this bounded domain, one-step equality with the
authoritative gate for every successful scalar result, and the exact predecessor
relation for the seven-edge sequence. The general finite-list theorem
additionally proves that every accepted command list materializes to the exact
result of
`FailStop.runAuthoritativeOperations` over the same normalized operations.
Its append-continuity corollary requires every prefix and suffix to share one
canonical intermediate state token, so stale replay or cross-trace splicing
cannot be accepted between adjacent steps.

The next twenty records form one positive mixed trace rooted in a
kernel-owned, complete two-subject state. In order, it offers and accepts a
sealed endpoint descendant, revokes its send-only generation, rejects the
stale handle, copies a fresh generation into the reused slot, accepts both
syscall-mediated and direct mapping, rejects an unknown syscall without
mutation, completes nonblocking send/receive, blocks and wakes the receiver,
switches back to it on a timer entry, contains its user page fault with
complete subject cleanup, enters a fatal kernel fault, and rejects a
post-fatal scheduler attempt. Independent edges from the same complete
direct-mapped pre-state accept a writable-to-read-only protection reduction
with exact page effect and reject a later write-amplification attempt without
mutation. Lean checks the exact typed result at each named boundary, including
the timer-selected subject and the faulting subject's retired identity. The
scalar export remains allocation-free; generated C and its calling convention
remain trusted hosted-test boundaries.

The final twenty-two records are the stateful invalidation-publication corpus.
Nineteen canonical edges cover an independent accepted unmap and exact
page-effect acknowledgement, an independently ticketed switch-away/back round
trip, plus wrong-owner protection rejection, an accepted writable-to-read-only
protection reduction, accepted release and destruction, stale-release
rejection, root switch, and bounded post-retirement reuse. Both
protection and release include a mismatched-effect stutter before the exact
acknowledgement. The three final negatives reject a malformed effect encoding,
a valid page acknowledgement paired with the wrong pending state, and an old
release-flush ticket replayed against the later switch flush. Pending state
tokens retain the complete published pre-state: `prepare_retains_published` and
`release_not_published_before_ack` prevent early retirement publication,
`acknowledge_accepted_exact` requires the fresh ticket and exact effect before
publishing the recorded successor, and
`reuse_publication_requires_retirement_ack` requires acknowledged release and
destruction with no pending effect. The switch round trip additionally checks
that the first flush ticket cannot acknowledge the return switch and that the
published active root returns to address space 1 only after ticket 1. The
object-11 reuse remains the existing
finite fixture; it adds no authoritative quota or reclamation policy.

The final 24 records are the frame-budget corpus. Eleven accepted edges encode
the complete A-allocation, state-preserving exhaustion, kernel-selected B
handoff, peer allocation, checked A termination, fresh B publication,
stale-handle denial, and completion trace plus the checked release branch.
Thirteen hostile records cover
repeated retry and cleanup, occupied-slot ordering, aggregate/global and
malformed state tokens, caller/charge-owner forgery, stale generation,
state replay and cross-trace splicing, unknown/reserved operations, and maximum
words. `FrameBudgetScenario.step_refinement` connects every accepted edge to
the exact admitted-budget transition, while the hosted generated-C harness
reports the first mismatching operation and reply.

The same hosted boundary exercises
`leanos_frame_budget_invalidation_effect`. Exact canonical
`bAllocated/terminateA` and `aAllocated/releaseA` pairs return distinct
transition-bound tokens whose typed meaning is `RetirementEffect.flush`; cross-pair,
stale, and malformed inputs return zero. The QEMU frame-reuse path consumes
the termination token before retiring A's PTE or publishing released capacity.

Five additional Phase 2 records invoke that same dispatcher for a canonical
generation-bound map handle, nonblocking IPC, capability copy, blocking
cancellation, and deferred cancellation drain. The handle word `0x10000` is
proved to round-trip through `CapabilityHandle` as slot 0, generation 1;
trusted caller and address-space identity still come only from the reconstructed
composite state. `CanonicalCompositeState` is the decoded ABI object and
contains the full state plus its exact materialization equality.
`CanonicalTypedStep` retains the literal `AuthoritativeGateResult` and
post-state returned by the sole `authoritativeGate` invocation rather than
manufacturing a generic success result. These five probes remain independently
proved one-step rejections. The positive mixed sequence covers the accepted
mapping, IPC, transfer/reuse, timer, and cleanup paths without weakening those
negative fixtures.

Every boot image retains that same generated `leanos_composite_dispatch` symbol
and routes adapter 18 through it during the ordered oracle replay. Unknown
adapter identifiers fail closed rather than falling through to another witness.

The hosted replay also compiles eight deliberately invalid harness variants.
They truncate the composite record arity, corrupt the generated dispatcher's
result word, route the record through the old stateless syscall witness, or
corrupt the ABI version, reserved bits, predecessor state, forged context
argument, or canonical capability handle.
Each variant must stop at the first malformed record or mismatch. Unknown
adapter identifiers fail closed instead of falling through to the composite
export. Every mismatch names the first operation and divergent reply field.
Buffer aliasing, alignment, and partial-write fixtures do not apply to this
six-scalar-input, one-scalar-result ABI, which owns no caller buffer or
generated state cell.

The proof job preserves a reviewable `leanos-oracle-<commit>` artifact for this
boundary. It contains the generated `CompositeDispatcher.c`, the public
version-one scalar ABI header, the versioned corpus, exact per-step hosted
results and negative-fixture diagnostics, compiler flags and tool versions,
and a SHA-256 manifest tied to the source revision. The manifest records
reproducible differential evidence, not verified compilation: Lean code
generation, the C compiler, the scalar calling convention, and the hosted
harness remain explicit trusted boundaries.

The interrupt-entry corpus also includes the user-only vector-13 hardware-error
shape and its broad general-protection purpose. The live handler refines that
class to direct-port denial only after checking `#GP(0)`, the reviewed RIP, and
the saved instruction operands.

The 36 page-fault provenance records cover user read/write/execute,
non-present and protection classes, kernel origin, RSVD, PK, shadow-stack and
SGX rejection, a changed CR2 page, wrong vector/stub/error shape, truncated and
nested entry, privilege mismatch, and lower/upper canonical plus noncanonical
boundaries. Seven accepted mutation rows independently vary subject, address
space, CR3, WP, NXE, SMEP, and SMAP; each must change the generated authority
attestation. Expected values come from `normalizePageFault`; hosted generated C
and every boot image call the same `leanos_page_fault_demo`. The compact result
is executable differential evidence only. The independent 19-word canonical
codec carries all authoritative fields and is the object of the Lean
roundtrip/injectivity and exact-binding theorems.

The final 28 direct-port records cover the selected live-control snapshot,
every named control mutation, stale read-back, all input/output width classes,
the four reviewed kernel purposes, wrong-purpose and wrong-port requests,
malformed scalar encodings including maximum-word stored/live controls and port,
byte normalization, and a validate-then-relax attempt. The scalar adapter packs
a byte-bounded device projection for corpus
comparison; it does not claim to serialize arbitrary device state.

The final 17 NMI records use an abstract normalized interval and its
`stackPastLast - 40` five-word frame address for accepted user-running,
kernel-handling, and kernel-halted normalization, followed by every rejection
selectable through the generated scalar boundary, including reserved bounds
and mode codes. These `0x900000..0x904000` model coordinates are deliberately
not linker virtual addresses. The final-ELF policy independently checks the
live `__nmi_ist_stack_start`/`end` interval and its `end - 40` frame relation;
snapshot construction remains an unproved machine-to-model boundary. The
halted record is accepted only by this normalization corpus: `dispatchNmi`
short-circuits an already-halted execution before normalization and preserves
the original terminal record. Their ordered identifiers and codes are proved
against `NmiRejectReason.runtimeInventory`; the compile-time-only invalid
terminal manifest and a dropped stateful trace class are separate semantic
negative fixtures. Hosted and boot replay both call the same generated
`leanos_nmi_demo` symbol. Separately, the terminal probe image installs vector
2 on IST2 and uses QEMU monitor injection to observe real non-maskable delivery
at an IF-clear CPL0 handling boundary; that machine observation does not turn
the generated classifier agreement into a hardware-refinement proof.

The resumable adapter executes both composite context-bank legs and packs the
restored owner/address-space, logical stack marker, and r12 marker together
with the outgoing saved owner/stack/r12 markers. Target and outgoing
descriptors combine kernel-owned bank metadata with each frame's actual saved
RSP; r12 markers also come from the two concrete buffers. The boot path thus
rejects a corrupted outgoing stack or exchanged bank before the success
transcript. B is restored from a kernel-owned complete initial image and checks
all fifteen distinct GPR values before its first authorized syscall, so the
boot protocol also fails if any A register is inherited. The kernel validates
the exact initial RIP/CS/RFLAGS/RSP/SS before restore, and a live-image negative
mutates RFLAGS to a different valid user value and requires rejection. Exact kernel-owned
RIP/RSP/RFLAGS snapshots additionally guard the
full saved return-frame words that are intentionally too large for the compact
oracle descriptor, so exchanging A and B is rejected by the same generated-code
witness rather than only by a
serial symptom check. `./scripts/generate-oracle.sh` emits `corpus.tsv` and a C header from that one
Lean executable. The file records its schema and source revision. The complete
proof gate replays it against hosted Lean-generated C. Image construction embeds
the same generated header; QEMU must report an ordered result for every vector
before its guest success signal. The runner constructs its expected transcript
from `corpus.tsv`, so a summary PASS cannot replace a missing, changed, or
reordered vector. The corpus is finite, deterministic, contains only scalar
words, and performs no allocation at the freestanding entry points.

These comparisons test encoders, exported entry points, result decoding, ABI
glue, and the bounded emulator path for the listed cases. They are reproducible
integration evidence, not exhaustive exploration, semantic refinement,
verified compilation, or proof about the final binary. Corpus extraction, Lean
code generation, the C compiler, ABI, C/assembly glue, linker, serial checker,
QEMU, firmware, and hardware semantics remain trusted. New boot-reachable
adapters must extend the versioned corpus and its model-agreement checks. The
blocking-IPC vectors are also consumed by the guest's block, send/wake,
dispatch, and delivery gates, so payload words cannot select the trusted caller
or active address space. The capability-reuse vectors cover initial authority,
clear, stale and fresh generations, wrong caller and object kind, malformed and
exhausted generations, and maximum payload words. The guest consumes the same
results while exercising same-slot replacement; ordered serial checks and
negative fixtures establish reproducible integration evidence for stale denial
and fresh success, not a proof of the boot binary.

The repository-owned
`scripts/hosted-generated-boundaries.tsv` is the authoritative inventory for
host-runnable generated-C replays. Both the ordinary optimized replay and the
additional AddressSanitizer/UndefinedBehaviorSanitizer replay consume that
inventory, so a new hosted boundary (including the future stateful composite
dispatcher) must declare its generated modules, real harness, and per-result
assertion there. The gate also compares that inventory with every generated
module named by image construction, so a new boot-reachable generated adapter
cannot silently bypass the hosted lane. The sanitizer configuration is fixed in
`scripts/hosted-sanitizer-config.sh`, applies to every generated object and C
harness, aborts on the first finding, and records its compiler, flags, source
revision, and runtime options under `build/hosted-sanitizer-negatives/`.
Controlled heap-overflow and invalid-shift fixtures demonstrate that both
sanitizer classes are active; separate negatives reject an uninstrumented
generated-object surrogate and a link that omits the sanitizer runtime.

This is finite dynamic implementation-boundary evidence. It does not prove
memory safety, remove generated C or the compiler from the TCB, or turn a
sanitizer report into a modeled rejection. The allocation-free boot-handoff
stream still builds and executes as a freestanding static ELF with no hosted
runtime, retaining its undefined-symbol and complete text-symbol inventory.
The same C fixture and generated stream objects additionally execute as a
hosted sanitizer process; that replay does not instrument the freestanding
artifact. Privileged instructions, physical-memory reads, MMIO/PIO, interrupt
stubs, QEMU devices, and firmware remain outside the hosted process.

The independent Clang image lane also consumes this same hosted-boundary
manifest in ordinary mode. Its selected compiler builds the direct oracle,
each listed generated root object, every C harness, and the freestanding stream
fixture before the canonical image is built and booted. Each replay retains
the manifest, corpus, typed results, compiler record, and boundary-coverage
evidence. This is compiler-diverse semantic evidence over the sanitizer
corpus; it is not a Clang sanitizer run, a cross-compiler byte-identity claim,
or a reduction of the generated-C/ABI trusted boundary.

The return adapter uses one bounded synthetic subject/address-space fixture.
Its five scalar words encode a kernel-owned purpose/context mode, RIP, RSP,
packed CS/SS selectors, and RFLAGS. The negative matrix covers noncanonical and
out-of-region addresses, wrong selectors and origin, IOPL/NT/VM/AC/DF/IF,
stale subject/address-space/CR3 bindings, fatal and diagnostic modes, and a
validate-then-mutate attempt. The exported scalar path remains allocation-free;
the richer Lean transition still returns the complete accepted request as its
attestation.

The `StaleTranslation.scalar` block evaluates the canonical
`StaleTranslation.step` over one reviewed cache fixture (subject 0 owning
address spaces 1 and 2, page 7 caching live object 10). Its six scalar words
encode a request kind, actor, address space, page, an auxiliary
permission/slot, and a filled/post-reuse state selector; the packed result
carries the accepted bit, the affected-absence bit, and the effect tag with its
address space and page. The block covers accepted unmap/protect, wrong-owner
rejections, release/destroy/switch effects, an unmapped page, a post-release
reuse whose old page stays absent, permission amplification, and a malformed
encoding. Attacker words cannot select the invalidation target: ownership and
lifetime are checked by `step`, so a non-owner or post-reuse request packs no
effect. `stale_translation_adapter_agrees_with_model` proves the exported scalar
matches the authoritative `step` on every vector.

The canonical composite accepted-unmap reply is also consumed by the boot
image's runtime-mutable page-7 window. Source and final-ELF policy checks bind
the reply to address space B and enforce PTE-store, `invlpg`/CR3, publication
order; QEMU observes the distinct kernel-read before/replacement-frame values
and restoration of the boot-plan leaf. The dedicated stale-translation image
then consumes both the composite reply and the scalar block's generated
post-reuse selector in one phase-checked machine sequence: real CPL3 prefill,
active-root clear/`invlpg`/publication, full scrub and same-frame fresh-lifetime
canary publication into A/page 7, a real CPL3 denial through the now-absent
B/page 7, and a real CPL3 A read of the replacement canary.
The scalar selector establishes the named model's accepted fresh-object
allocation and old-page absence; C sequencing and QEMU do not prove that the
binary refines that model.

Run the complete local evidence path with:

```sh
./scripts/check.sh
./scripts/check-markdown.sh
./scripts/build-image.sh
./scripts/run-image.sh
```
