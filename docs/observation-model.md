# Observer-relative one-step isolation

`LeanOS.Observation` defines the first information-flow claim for the abstract,
sequential core. It is a scoped unwinding model, not a claim about the booted
binary or all kernel behavior.

## Claim vocabulary

An observer sees its live identity bit, capability slots and attenuated rights,
authorized actor-local byte contents, explicitly shared byte contents, owned virtual-page permissions, syscall reply,
declared endpoint deliveries, and the current scheduler selection. Raw kernel
object and physical-frame identifiers are deliberately absent: a subject sees
only its local capability handle and the permissions relevant to its own view.

Two states are **low-equivalent** for a subject exactly when these complete
views are equal. A step is **silent** for that subject when its footprint cannot
change any component of the view. `silent_steps_lowEquiv` proves that two
independently chosen silent steps applied to low-equivalent states preserve low
equivalence; `silent_steps_equal_reply` additionally states equality of the
next visible reply. Thus secret-dependent high behavior need not choose the
same operation or arguments in both runs.

The supported operation classes mirror the deterministic sequential models:
map, unmap, access check, bounded copy, capability delegation and revocation,
typed rejection, endpoint send/receive, allocation, and scheduler selection.
The theorem covers unrelated actor-local, non-aliased memory, mapping, access, copy, rejection,
receive, delegation, revocation, and sends whose sender and recipient are both
unrelated to the observer. The endpoint abstraction is capacity one: send
reports full without changing the queued delivery, and receive reports empty
or returns and removes the unique delivery, including its sender provenance and
two payload words in the visible reply. It assumes
the trusted caller and active address space were selected by the kernel, as in
the syscall and user-copy models.

## Explicit channels and counterexamples

The kernel-reduced paired-state examples distinguish theorem scope from
channels:

- delegation into, or revocation from, the observer's capability slots is an
  authorized sharing channel;
- an explicitly shared/aliased-memory write changes `sharedBytes` in the
  observer view and is demonstrated as a non-silent channel; private-write and
  bounded-copy steps are scoped to actor-local, non-aliased memory;
- endpoint delivery to the observer is intentional declassification, including
  sender provenance and the two payload words;
- global allocation exhaustion can change a reply and is a resource channel;
- queue fullness changes the sender reply between `accepted` and `ipcFull` in
  the capacity-one abstraction and is demonstrated as a resource channel; and
- scheduler selection is explicitly visible, so scheduling differences are not
  silently abstracted away.

Shared-memory capabilities likewise end privacy: aliased bytes authorized to
the observer belong in its low view. The model deliberately separates these
from the disjoint actor-local region covered by silent writes and includes a
paired counterexample where another subject changes a shared byte. It never claims confidentiality
for shared objects, endpoint messages, or these resource and scheduler channels.

## Scope and evidence

Lean proves the observer-relative projection theorem and equal-reply corollary.
Definitional-reduction examples evaluate paired states that differ only in
another subject's secret, exercise every modeled private operation class, and
demonstrate deliberate divergence through capability, shared-memory, IPC, resource-exhaustion,
and scheduler channels.
Existing modules separately prove authorization, state-preserving rejection,
mapping confinement, bounded-copy footprints, endpoint provenance, and
lifecycle cleanup; this module does not restate those integrity results as
confidentiality.

The claim is termination-insensitive, single-step, deterministic, and
sequential. It excludes timing, caches, speculation, probabilistic behavior,
SMP, covert-channel elimination, full trace equivalence, and liveness. Lean
compilation proves the model theorem only. The compiler, generated code, boot
assembly, QEMU, hardware, trusted entry context, and correspondence between this
unwinding model and the booted artifact remain trusted or unproved boundaries.

The follow-on [finite scheduled observer model](scheduled-observation.md)
composes this vocabulary with `LeanOS.Scheduler`, derives accepted actor
context from its authoritative current subject/address space, and lifts the
scoped result to paired finite prefixes with matching declared public-event
projections and silent-step stuttering.

## Composite-state unwinding

`LeanOS.CompositeObservation` lifts the same unwinding structure from these
separate models to the authoritative `FailStop.CompositeState`, executed
through the published `FailStop.authoritativeGate`. The scheduled model and
the composite model are both instances of `LeanOS.ReplayUnwinding`, which
states the replay obligation and the finite-trace theorem once;
`ScheduledObservation.finite_trace_lowEquiv_of_replay` re-derives the
scheduled theorem from it.

**Low equivalence.** For an observing subject `S`, `CompositeObservation.observe`
contains:

- the public scheduler choice (`lifecycle.current`);
- S's authority: its liveness, slot capacity, and complete finite capability
  row (`Capability.capabilitySpace`, including object, kind, rights, and
  generation of each capability); for every capability in that row, the
  named object's liveness and kind, its endpoint mailbox, its pending sealed
  transfer, its blocking mailbox, its blocking waiter queue, and its frame
  backing (whether it is bound to a frame the allocator still records as its
  own);
- S's IPC observations: the messages above, the endpoint S waits on, and S's
  blocking completion (the delivered sender and reply words); and
- which address spaces S owns, and their mappings.

Frame backing and space ownership are exactly what S's own `map` reads
beyond its capability. They are in the view so that step and output
consistency hold for S's own memory operations.

**Unwinding conditions.**

- *Local respect*: `isSilent S state op` is a decidable classification. It
  holds only when another subject is the actor and the operation is one of:
  `nmi`, `selectUserReturn`, `userReturn`, or `restart`, whose declared
  footprints write no projection the view reads (proved with the footprint
  frame rule); `capabilityCopy` to a destination other than S;
  `capabilityRevoke` of a victim other than S; `map`, `unmap`, or a memory
  `syscall`, which may only change spaces the actor owns; or data-only `ipc`
  whose resolved endpoint S's row does not name.
  `authoritativeGate_silent_observe` proves that each silent step leaves S's
  view unchanged, including busy and halted stutters.
- *Local respect under a trace invariant*
  (`LeanOS.CompositeUnwinding`): `AuthoritativeRuntimeWellFormed` is preserved
  by every authoritative operation, so it can be threaded through a trace
  (`ReplayUnwinding.finite_trace_lowEquiv_on`). Under it,
  `isSilentCoherent` also classifies as silent, for another actor:
  - `protect` (coherence makes the TLB's virtual-memory copy the published
    one);
  - `createSubject` of a subject other than S (coherence makes the published
    capability store the lifecycle's);
  - blocking `send` to an endpoint S does not name and on which S does not
    wait;
  - blocking `receive` on an endpoint S does not name that does not block
    (the caller has a reserved completion or the mailbox holds a message),
    since blocking changes the public scheduler choice;
  - blocking `cancel` of a subject other than S that waits on no endpoint S
    names.

  `authoritativeGate_silentCoherent_observe` proves local respect for all of
  them, using frame lemmas over the raw blocking store.
- *Step consistency*: `step_consistent_of_untouched` proves that an operation
  whose footprint misses the view's projections preserves low equivalence
  whoever performs it, S included. `silent_steps_lowEquiv` covers paired
  silent steps. For S's own operations, `CompositeUnwinding.own_step_consistent`
  assumes two runtime-well-formed, low-equivalent states in which S is
  scheduled and the fail-stop latch is in the same mode (`OwnStep`). Under
  those premises it proves step consistency for `ipc`, `map`, `unmap`,
  `protect`, `syscall`, `capabilityRevoke`, `capabilityCopy` to another
  subject, `createSubject` of another subject, and the frame-rule families.
  Every other step is visible: its event carries S's resulting view, so equal
  events give equal views.
- *Output consistency*: a visible event is S's view (plus the gate result when
  S is the actor). `CompositeUnwinding.own_output_consistent` proves that,
  under the same premises, the gate returns equal results for S's `ipc`,
  `map`, `unmap`, `protect`, `syscall` (including access checks),
  `capabilityCopy` into S's own row, `capabilityRevoke` of S's own slot, and
  `restart`. `ipc_output_consistent` is the IPC case, including the delivered
  sender and words.

**Conclusion.** `CompositeObservation.finite_trace_lowEquiv` and its
invariant-relative form `CompositeUnwinding.finite_trace_lowEquiv_coherent`:
two finite runs from S-low-equivalent states with equal S-event projections
end S-low-equivalent. These theorems assume equal projections. For runs in
which only S acts, `CompositeUnwinding.own_run_noninterference` concludes the
equality instead of assuming it. Step and output consistency compose, so the
same finite run of S's operations that are in both families:

- returns the same gate result at every step; and
- ends S-low-equivalent.

SC-COMPOSITE-OBSERVER-ISOLATION restates all of these together with the
unwinding conditions and the channel theorems.

**Channels stated as theorems.** Where step or output consistency fails, the
model has a real channel. Each failure is proved on the canonical
runtime-well-formed dispatcher seed (`FailStop.compositeDispatcherInitial`),
paired with the state after S's own delegation to another subject. That
delegation leaves S's view unchanged, so the pair satisfies every `OwnStep`
premise.

- **The global capability-identity counter breaks step consistency.**
  `Capability.copy` takes the new capability's identity, which is its handle
  generation, from the global `nextIdentity`. S's own delegation into its own
  row therefore yields distinguishable rows
  (`Channels.identity_counter_step_inconsistent`).
  - The channel cannot be closed by abstracting identities in the view: S
    must present the exact generation in every later handle word, and handle
    resolution checks it.
  - The executable witness `Evidence.identity_counter_projection_witness`
    shows the same effect through a silent delegation between two other
    subjects.
  - Transfer offers allocate identities the same way
    (`CompositeChannels.offer_counter_step_inconsistent`). Receipt allocates
    none; it installs the identity the offer reserved.
  - The negative fixture `tests/negative/IdentityCounterStepConsistency.lean`
    shows that the step-consistency theorem cannot be instantiated for S's
    delegation into its own row.
- **A delegation's destination breaks output consistency.** The reply to S's
  delegation to another subject reveals whether the destination slot is
  occupied, and by the same check whether that subject is live
  (`Channels.copy_destination_output_inconsistent`).

**The identity counter as a declared public input.** The counter channel
cannot be closed in the view, and closing it in the model (for example with
per-subject identity namespaces) would change the handle generations that the
generated dispatcher (`LeanOS.CompositeDispatcher`) and its replay fix. The
extended theorems therefore treat the counter like the scheduler choice and
the fail-stop mode: `CompositeOwnSteps.OwnStepCounter` adds agreement on
`nextIdentity` to `OwnStep`. This is a declared channel, not a claimed
absence: S learns how many identities the whole system has issued. The two
counter channel theorems show that the premise is necessary, and the negative
fixture `tests/negative/CompositeChannelOverclaims.lean` shows that
`OwnStepCounter` cannot be built for states with different counters.

**Local respect for more of other subjects' operations**
(`LeanOS.CompositeLocalRespect`). Under the same trace invariant,
`isSilentExtended` also classifies as silent, for another actor:

- `scheduleNext`, `scheduleYield`, and `scheduleTick`, which the composite
  never applies (selection goes through the resumable switch), and
  `scheduleAdd`, which writes only scheduler queues;
- `scheduleRemove` of a subject that is not the scheduled one;
- transfer offer and receipt on an endpoint S does not name;
- an interrupt that contains no scheduled subject (timer, syscall, rejected
  and fatal entries, and contained faults of an unscheduled identity);
- a resumable switch that fails (it rejects or latches the halt);
- a deferred-cancellation drain of a subject other than S.

`authoritativeGate_silentExtended_observe` is local respect and
`finite_trace_lowEquiv_extended` the trace theorem.

**Step and output consistency for the rest of S's operations.**

- `CompositeOwnSteps.own_step_consistent_counter`: under `OwnStepCounter`,
  also S's delegation into its own row, its transfer offers, creation of any
  subject (itself included), and `scheduleAdd`, `scheduleRemove`,
  `scheduleNext`, `scheduleYield`, `scheduleTick`.
- `CompositeOwnSteps.own_output_consistent_counter`: also transfer offer and
  receipt (`CapabilityTransfer.WellFormed` makes the carried object's checks
  succeed), subtree revocation of S's own slot (rights attenuate along every
  derivation edge, so the runtime-safety check reads only the revoked
  capability), creation and termination of S itself, `scheduleNext`, and
  `terminateCurrent`.
- `CompositeOwnSteps.own_output_consistent_scheduler`: `scheduleYield`,
  `scheduleTick`, and `scheduleRemove`, when the two states also agree on the
  ready queue and its capacity (`SchedulerPublic`, the scheduler's choice as a
  public input).
- `CompositeOwnSteps.own_step_accept_gate`: transfer receipt, given agreement
  on the objects that sealed transfers pending on S's endpoints carry
  (`CarriedAgree`). Receipt adds the carried object to S's authority; that is
  the information flow the sender's offer authorizes.
- `CompositeLocalRespect.own_step_drain` and `own_output_drain_self`: every
  deferred drain is step consistent, and S's drain of itself (always rejected
  while S is scheduled) is output consistent.
- `CompositeOwnTermination`: S's own termination (`terminateSubject` of
  itself or `terminateCurrent`) and interrupts are step consistent, since S's
  view after its termination depends only on its slot capacity and blocking
  completion (`deadView`); interrupts and NMIs are output consistent, since
  their classification reads only the frame, the mode, and the scheduled
  subject. These need `AuthoritativeRuntimeWellFormed` (S waits on nothing).
- `CompositeOwnSteps.own_run_noninterference_counter` composes the extended
  families: the same run of S's operations that are in both returns the same
  results and ends low-equivalent, now including its own delegations, offers,
  creation of itself, and `scheduleNext`.

**More channels stated as theorems.** Every exclusion below has a
counterexample whose two states satisfy `OwnStepCounter` (so the counter
agrees too).

- From S's own operations on the dispatcher seed
  (`LeanOS.CompositeChannels`):
  - creating, terminating, or admitting another subject to the queue replies
    with its liveness and issuance (`create_output_inconsistent`,
    `terminate_output_inconsistent`, `scheduleAdd_output_inconsistent`);
  - an accepted termination of another subject cancels every pending sealed
    offer, including S's own offer on S's endpoint
    (`terminate_step_inconsistent`);
  - delegation to, and direct or subtree revocation of, another subject's
    slot replies with that slot's occupancy
    (`copy_destination_output_inconsistent_counter`,
    `revoke_other_output_inconsistent`,
    `revokeSubtree_other_output_inconsistent`).
- With subject 1 running between authoritative timer switches, evaluated by
  the kernel on the canonical sample boot plan
  (`LeanOS.CompositeSwitchedChannels`):
  - subtree revocation of S's own or another subject's capability cancels the
    sealed transfer pending on S's endpoint exactly when a derivation S cannot
    see links it to the revoked root
    (`revokeSubtree_own_step_inconsistent`,
    `revokeSubtree_other_step_inconsistent`).

The replies of S's timer switch, of its blocking send that wakes a waiter,
and of its cancellation of a wait used to carry another subject's saved
registers. That channel is closed; see the 2026-10-10 amendment below.

The negative fixture `tests/negative/CompositeChannelOverclaims.lean` shows
that the extended families cannot be instantiated for termination of another
subject, S's subtree revocation of its own slot, or S's timer switch.

**Remaining gaps.** No theorem and no counterexample yet covers:

- output consistency of `selectUserReturn` and `userReturn`, whose replies
  read the boot return plan and the physical frames behind S's code and stack
  mappings (the canonical seed's return plan is not live, so it gives no
  counterexample);
- step consistency of S's timer switch (`resumePreempt`) and of S's blocking
  send, receive, and cancel; output consistency of S's blocking receive; and
  general output consistency of S's timer switch, blocking send, and wait
  cancellation (their replies no longer carry registers, but the general
  proof is not yet done);
- output consistency of a drain of another subject;
- step consistency of transfer receipt without `CarriedAgree` (in the
  canonical seed every object a transfer can carry is already named by S, so
  it gives no counterexample).

These operations stay visible, so they are part of the compared projection
rather than a claimed absence.

The claim is termination-insensitive and excludes timing, caches, device
reads, and refinement to the generated C or the binary. The executable
evidence also shows the shared-capability channel: subtree revocation by
another subject clears S's derived capability, although the operation names
neither S nor its slots (`Evidence.shared_capability_revocation_visible`, and
the negative fixture `tests/negative/SharedCapabilityConfidentiality.lean`).

## Amendments

### 2026-10-10: saved-register replies closed (#479)

`#542` proved three output channels: the replies of S's timer switch
(`resumePreempt`), of its blocking send that wakes a waiter, and of its
cancellation of another subject's wait each carried that other subject's
complete saved context, frame and registers included.

**Model artifact, not a binary leak.** The booted kernel never returned
those contexts to the caller. Every path in `boot/boot.S` that resumes a
different subject (the timer gate `isr32`, the `isr80` send, block, report
and server paths, fault delivery and the peer-restore paths of the fault
families) overwrites all twenty words of the return frame. It copies either
the incoming subject's own saved or initial context, or fifteen zero
registers and a fresh `iretq` frame. The only words another subject
contributes are values that subject passed as arguments (send payload words,
call and reply words), values the kernel computes (subject numbers, answers,
delivery flags, expiry bits), and, by design, the faulting instruction
pointer in the fault-handler record. A subject that returns to itself gets
only its own frame with the reply word in `rax`. The leak was in the model's
typed reply, which recorded the restored context as if it were returned.

`isr80` chooses its switch path by comparing the reply word with fixed
values. A few replies carry a word a subject chose, so a chosen word equal to
one of them would select another path. Each such path then fails closed
(`switch_complete` or `validate_user_return` stops the machine before
`iretq`), so nothing leaks. Separating the path selector from the reply word
would remove the coincidence altogether.

**Decision.** The replies now name a subject and nothing else:

- `OperationReply.resume next error`, where `next` is the subject the switch
  restored;
- `CompositeBlockingSendReply.woke receiver`;
- `CompositeBlockingCancelReply.cancelled subject`.

The restored context stays in the composite state (the resumable bank) and,
for the kernel's own proofs, in the dispatch outcome's `restored` field. The
named subject is public. After a switch it is the scheduled subject of the
post-state, which every view contains
(`CompositeRegisterChannels.resume_reply_names_scheduled`). A wake names the
receiver it released, and a cancellation names the subject it was asked to
cancel. The generated dispatcher's scalar reply words are unchanged; only the
typed meaning of its switch and wake selectors (`timerSwitched` and
`blockingReceiverWoken`, the in-flight revocation family's
`subjectTwoRestored`, and the capability-transfer boot family's switch) lost
the context.

**Adversarial record.** `CompositeRegisterChannels.legacyResume`,
`legacySend` and `legacyCancel` compute the payload the old replies carried,
from the same transitions. `legacy_replies_leaked` proves, by kernel
evaluation on the canonical sample plan, that those payloads differ on
`#542`'s pairs (states that satisfy every `OwnStepCounter` premise).
`register_channel_closed_on_pairs` proves that the new replies on the same
pairs are equal. The negative fixture
`tests/negative/CompositeRegisterChannelReopened.lean` restates the old
channel theorems for the new replies; the kernel rejects both.

### 2026-10-10: cross-subject requests refused (#479)

`#542` proved that every request of S naming another subject was a channel.
The affected requests are:

- creation, termination and queue admission of another subject, whose
  replies reveal its liveness and issuance;
- delegation into, and direct and subtree revocation of, another subject's
  slot, whose replies reveal its occupancy;
- termination of another subject, which cancels S's pending offer;
- subtree revocation of another subject's capability, which depends on a
  hidden derivation.

S's cancellation of another subject's wait and its drain of another subject
read that subject's wait and retained state in the same way.

**Decision ([ADR 0025](adr/0025-subject-gate-cross-subject-refusal.md)).**
`FailStop.authoritativeGate` stays the kernel's transition engine: boot, the
spawn family, contained-fault cleanup and the issued lifecycle family use it
without a caller. `FailStop.subjectGate` is the gate a scheduled subject asks
through. When the latch is running, a subject is scheduled and the request
names another subject (`AuthoritativeOperation.target`), the gate refuses
with one fixed result, `crossSubjectRefused`. It decides this before
anything of the target is read and changes nothing. Otherwise it is exactly
`authoritativeGate`. Authorized cross-subject management goes through
sealed transfer, subtree revocation of the caller's own lineage root, the
spawn family and the fault-handler binding.

**The unwinding over the subject gate** (`LeanOS.CompositeSubjectGate`):

- Refusal reads only the latch mode, the scheduled subject and the request.
  Another subject's refused request is therefore silent
  (`subjectGate_silent_observe`), and finite-trace noninterference holds over
  the subject gate (`finite_trace_lowEquiv_subject`).
- When S names another subject, both states of an `OwnStep` pair refuse, or,
  with the latch busy or halted, reject from the latch alike
  (`own_cross_stutter`). S's cross-subject requests are step and output
  consistent with no further premise (`own_step_cross`, `own_output_cross`).
- Every other request is `authoritativeGate` on both sides
  (`subjectGate_own`), so the families proved for the authoritative gate
  carry over (`own_step_consistent_subject`,
  `own_output_consistent_subject`).

**Adversarial record.** The channel theorems over `authoritativeGate` in
`LeanOS.CompositeChannels` and `LeanOS.CompositeSwitchedChannels` stay: they
show that the raw transitions leaked when exposed to a subject.
`cross_subject_channels_closed` and `revokeSubtree_other_closed` re-evaluate
the same pairs through the subject gate and find equal replies and
low-equivalent states. The negative fixture
`tests/negative/CompositeCrossSubjectReopened.lean` restates three of the old
channels for the subject gate; the kernel rejects all three.

Still open after this amendment:

- step consistency of S's subtree revocation of its own slot (a hidden
  derivation);
- transfer receipt without `CarriedAgree`;
- the gaps listed above: the outputs of `selectUserReturn` and `userReturn`;
  the timer switch; blocking send, receive and S's cancellation of itself.
