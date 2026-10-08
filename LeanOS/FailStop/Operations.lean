import LeanOS.FailStop.BlockingIPC

/-!
# Fail-stop composite: typed operations

Scheduler, resumable, transfer, termination, and mapping publication helpers,
the typed `Operation` family, and its exact composite post-state
`applyOperation`.  Each operation's footprint and frame theorem live in
`LeanOS.FailStop.Footprint`; its reply and the ordinary gate live in
`LeanOS.FailStop.Gate`.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- Publish a queue-only admission without invoking lifecycle cleanup.  An
accepted `Scheduler.add` retains the lifecycle exactly, so the only consumers
that must observe the new ready queue are the scheduler, legacy preemption,
and authoritative resumable-context bank. -/
def installSchedulerAdmission (state : CompositeState)
    (scheduler : Scheduler.State) : CompositeState :=
  { state with
    scheduler
    preemption := { state.preemption with scheduler }
    resumable := { state.resumable with scheduler }
    blockingIPC := { state.blockingIPC with scheduler } }

/-- Admit a runnable subject only when its kernel-owned initial context is
already staged and no retained cancellation awaits its capacity-checked drain.
The raw scheduler owns queue policy; this composite wrapper owns the additional
context-bank and deferred-cancellation obligations needed by
`AuthoritativeRuntimeWellFormed`. -/
def schedulerAdmission (state : CompositeState)
    (subject : Scheduler.SubjectId) : Scheduler.Outcome :=
  match state.deferredCancels.retained subject with
  | some _ => Scheduler.reject state.scheduler .undrainedCancellation
  | none =>
      match Scheduler.add state.scheduler subject with
      | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
      | { state := scheduler, result := .accepted context } =>
          match ResumablePreemption.contextFor state.resumable.contexts subject with
          | none => Scheduler.reject state.scheduler .noResumableContext
          | some _ => { state := scheduler, result := .accepted context }

/-- Raw scheduler selection has no context-restore payload.  Empty selection
is a genuine no-op success, but selecting a subject must be performed through
the resumable switch operation that consumes its kernel-owned context. -/
def schedulerDispatch (state : CompositeState) : Scheduler.Outcome :=
  match Scheduler.selectNext state.scheduler with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { state := scheduler, result := .accepted none } =>
      { state := scheduler, result := .accepted none }
  | { result := .accepted (some _), .. } =>
      Scheduler.reject state.scheduler .noResumableContext

/-- Voluntary yield cannot cross the composite boundary without an outgoing
register/frame payload.  The resumable preemption operation owns that atomic
save/select/restore step. -/
def schedulerYield (state : CompositeState) : Scheduler.Outcome :=
  match Scheduler.yield state.scheduler with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { result := .accepted _, .. } =>
      Scheduler.reject state.scheduler .noResumableContext

/-- A raw tick has the same missing-save obligation as raw yield. -/
def schedulerTick (state : CompositeState) : Scheduler.Outcome :=
  match Scheduler.tick state.scheduler with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { result := .accepted _, .. } =>
      Scheduler.reject state.scheduler .noResumableContext

theorem schedulerDispatch_rejected_unchanged state reason
    (hrejected : (schedulerDispatch state).result = .rejected reason) :
    (schedulerDispatch state).state = state.scheduler := by
  unfold schedulerDispatch at hrejected ⊢
  generalize hselect : Scheduler.selectNext state.scheduler = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected actual => simp [Scheduler.reject]
      | accepted context =>
          cases context with
          | none => simp at hrejected
          | some selected => simp [Scheduler.reject]

theorem schedulerDispatch_accepted_none_unchanged state
    (haccepted : (schedulerDispatch state).result = .accepted none) :
    (schedulerDispatch state).state = state.scheduler := by
  unfold schedulerDispatch at haccepted ⊢
  generalize hselect : Scheduler.selectNext state.scheduler = outcome at haccepted ⊢
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason => simp [Scheduler.reject] at haccepted
      | accepted context =>
          cases context with
          | some selected => simp [Scheduler.reject] at haccepted
          | none =>
              have hraw : scheduler = state.scheduler := by
                simp only [Scheduler.selectNext] at hselect
                split at hselect <;> simp_all [Scheduler.reject]
                next => split at hselect <;> simp_all [Scheduler.reject]
              exact hraw

theorem schedulerDispatch_accepted_is_none state context
    (haccepted : (schedulerDispatch state).result = .accepted context) :
    context = none := by
  unfold schedulerDispatch at haccepted
  generalize hselect : Scheduler.selectNext state.scheduler = outcome at haccepted
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason => simp [Scheduler.reject] at haccepted
      | accepted actual => cases actual <;> simp_all [Scheduler.reject]

theorem schedulerYield_rejected_unchanged state reason
    (hrejected : (schedulerYield state).result = .rejected reason) :
    (schedulerYield state).state = state.scheduler := by
  unfold schedulerYield at hrejected ⊢
  generalize hyield : Scheduler.yield state.scheduler = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerYield_ne_accepted state context :
    (schedulerYield state).result ≠ .accepted context := by
  unfold schedulerYield
  generalize hyield : Scheduler.yield state.scheduler = outcome
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerTick_rejected_unchanged state reason
    (hrejected : (schedulerTick state).result = .rejected reason) :
    (schedulerTick state).state = state.scheduler := by
  unfold schedulerTick at hrejected ⊢
  generalize htick : Scheduler.tick state.scheduler = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerTick_ne_accepted state context :
    (schedulerTick state).result ≠ .accepted context := by
  unfold schedulerTick
  generalize htick : Scheduler.tick state.scheduler = outcome
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerAdmission_rejected_unchanged state subject reason
    (hrejected : (schedulerAdmission state subject).result = .rejected reason) :
    (schedulerAdmission state subject).state = state.scheduler := by
  unfold schedulerAdmission at hrejected ⊢
  split <;> try simp [Scheduler.reject]
  generalize hadd : Scheduler.add state.scheduler subject = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected actual => simp [Scheduler.reject]
      | accepted context =>
          cases hcontext : ResumablePreemption.contextFor
              state.resumable.contexts subject <;>
            simp_all [Scheduler.reject]

theorem schedulerAdmission_accepted_exact state subject context next
    (haccepted : schedulerAdmission state subject =
      { state := next, result := .accepted context }) :
    state.deferredCancels.retained subject = none ∧
      Scheduler.add state.scheduler subject =
        { state := next, result := .accepted context } ∧
      ∃ saved, saved ∈ state.resumable.contexts ∧ saved.owner = subject := by
  unfold schedulerAdmission at haccepted
  cases hretained : state.deferredCancels.retained subject with
  | some saved => simp [hretained, Scheduler.reject] at haccepted
  | none =>
      simp only [hretained] at haccepted
      refine ⟨rfl, ?_⟩
      generalize hadd : Scheduler.add state.scheduler subject = outcome at haccepted
      cases outcome with
      | mk scheduler result =>
          cases result with
          | rejected reason => simp [Scheduler.reject] at haccepted
          | accepted actual =>
              cases hcontext : ResumablePreemption.contextFor
                  state.resumable.contexts subject with
              | none => simp [hcontext, Scheduler.reject] at haccepted
              | some saved =>
                  simp only [hcontext] at haccepted
                  injection haccepted with hnext hresult
                  subst next
                  cases hresult
                  refine ⟨rfl, saved, ?_, ?_⟩
                  · exact List.mem_of_find?_eq_some hcontext
                  · exact ResumablePreemption.contextFor_owner
                      state.resumable.contexts subject saved hcontext

theorem schedulerAdmission_eq_add_of_staged state subject saved
    (hsaved : saved ∈ state.resumable.contexts ∧ saved.owner = subject)
    (hnotRetained : state.deferredCancels.retained subject = none) :
    schedulerAdmission state subject = Scheduler.add state.scheduler subject := by
  have hsome : ResumablePreemption.contextFor state.resumable.contexts subject ≠ none := by
    intro hnone
    rw [ResumablePreemption.contextFor, List.find?_eq_none] at hnone
    exact hnone saved hsaved.1 (by simp [hsaved.2])
  unfold schedulerAdmission
  simp only [hnotRetained]
  generalize hadd : Scheduler.add state.scheduler subject = outcome
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason =>
          have hstate := Scheduler.add_rejected_unchanged state.scheduler subject reason
            (by simp [hadd])
          have hscheduler : scheduler = state.scheduler := by
            rw [← hstate, hadd]
          simp [hadd, hscheduler, Scheduler.reject]
      | accepted context =>
          cases hcontext : ResumablePreemption.contextFor
              state.resumable.contexts subject with
          | none => exact False.elim (hsome hcontext)
          | some actual => simp [hadd, hcontext]

/-- Installing an authoritative scheduler retains its queue and capacity
exactly; only the lifecycle shared with the other projections is republished. -/
@[simp] theorem installScheduler_scheduler state scheduler :
    (installScheduler state scheduler).scheduler = scheduler := by
  simp [installScheduler, installLifecycle]

/-- The legacy preemption projection observes the same scheduler that was
installed by the composite scheduler step. -/
@[simp] theorem installScheduler_preemption_scheduler state scheduler :
    (installScheduler state scheduler).preemption.scheduler = scheduler := by
  simp [installScheduler, installLifecycle]

/-- Scheduler installation publishes the scheduler's lifecycle as the unique
authoritative lifecycle projection. -/
@[simp] theorem installScheduler_lifecycle state scheduler :
    (installScheduler state scheduler).lifecycle = scheduler.lifecycle := by
  simp [installScheduler, installLifecycle]

/-- Scheduler publication is one synchronization step: execution,
preemption, and resumable-context consumers all observe the exact installed
scheduler lifecycle and queue state. -/
theorem installScheduler_synchronizes_consumers state scheduler :
    let next := installScheduler state scheduler
    next.execution.core.lifecycle = scheduler.lifecycle ∧
      next.scheduler = scheduler ∧
      next.preemption.scheduler = scheduler ∧
      next.resumable.scheduler = scheduler := by
  simp [installScheduler, installLifecycle]

/-- Publish the exact #74 context-bank state through every legacy projection.
The context list, TLB entries, and terminal latch are retained verbatim. -/
def installResumable (state : CompositeState)
    (resumable : ResumablePreemption.State) : CompositeState :=
  let lifecycle := resumable.scheduler.lifecycle
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  let virtualMemory := resumable.translations.virtual
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler := resumable.scheduler
    preemption := { state.preemption with scheduler := resumable.scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable
    blockingIPC := { state.blockingIPC with scheduler := resumable.scheduler } }

/-- Publish a resumable-aware scheduler removal without rebuilding unrelated
resource projections.  `ResumablePreemption.remove` changes only runnable/current
scheduler fields, the removed saved context, and the active translation. -/
def installSchedulerRemoval (state : CompositeState)
    (resumable : ResumablePreemption.State) : CompositeState :=
  let lifecycle := resumable.scheduler.lifecycle
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler := resumable.scheduler
    preemption := { state.preemption with scheduler := resumable.scheduler }
    lifecycle
    resumable
    blockingIPC := { state.blockingIPC with scheduler := resumable.scheduler } }

/-- Publish the exact #71 capability/mailbox state through every consumer of
the shared capability registry.  Pending sealed descendants and their trace
remain owned solely by `CapabilityTransfer.State`. -/
def installTransfers (state : CompositeState)
    (transfers : CapabilityTransfer.State) : CompositeState :=
  let capabilities := transfers.capabilities
  let lifecycle := { state.lifecycle with capabilities }
  let scheduler := { state.scheduler with lifecycle }
  let virtualMemory := { state.virtualMemory with
    memory := { state.virtualMemory.memory with capabilities } }
  let endpoints := transfers.toEndpointState
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers
    blockingIPC := { state.blockingIPC with scheduler } }

/-- Publish an accepted transitive revocation atomically.  The revoked
capability store and the cancellation of every sealed descendant of `root`
reach every capability, mailbox, and in-flight consumer in one step.  Clearing
installed slots while leaving a sealed descendant receivable would let
authority survive its own revocation, so this is the only publication path for
an accepted subtree revocation. -/
def installRevokedSubtree (state : CompositeState) (root : Nat)
    (capabilities : Capability.State) : CompositeState :=
  installTransfers state
    (CapabilityTransfer.publishSubtreeRevocation state.transfers root capabilities)

/-- Publish authoritative subject cleanup and discard every sealed transfer
that could retain a retired sender, endpoint, or carried object.  The final
`installTransfers` call republishes the canceled mailbox together with the
empty in-flight store, so IPC and transfer consumers cannot drift. -/
def installTerminatedResumable (state : CompositeState)
    (resumable : ResumablePreemption.State) : CompositeState :=
  let lifecycle := resumable.scheduler.lifecycle
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  let endpoints := { state.ipc.endpoints with
    capabilities := lifecycle.capabilities
    mailbox := restrictMailboxes lifecycle state.ipc.endpoints.mailbox }
  let transfers := CapabilityTransfer.cancelAllOffers
    { state.transfers with toEndpointState := endpoints }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler := resumable.scheduler
    preemption := { state.preemption with scheduler := resumable.scheduler }
    virtualMemory := resumable.translations.virtual
    ipc := { state.ipc with
      virtualMemory := resumable.translations.virtual
      endpoints := transfers.toEndpointState }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable
    transfers
    blockingIPC := { state.blockingIPC with scheduler := resumable.scheduler } }

/-- Publish one explicit subject termination through every authoritative
cleanup store.  The blocking transition runs against the live pre-state, so it
can remove the exact waiter/context pair before the resumable/resource
publisher installs the same terminated lifecycle everywhere else.  Waiters on
endpoints owned by the terminated subject are detached with their exact saved
contexts for a later capacity-checked cancellation drain, and mailboxes for
those retired endpoints are cleared in the same mutation.  A quiescent context
retained by contained cleanup is also retired here: a dead subject must not
remain eligible for a later deferred-cancellation drain. -/
def installTerminatedSubject (state : CompositeState)
    (subject : BlockingIPC.SubjectId)
    (resumable : ResumablePreemption.State) : CompositeState :=
  let cleaned := installTerminatedResumable state resumable
  let selfRemoved := BlockingIPCContext.terminate state.blockingIPCContext subject
  let detached := BlockingIPCContext.detachInvalidated selfRemoved
    state.deferredCancels resumable.scheduler
  { cleaned with
    blockingIPC := { detached.1.ipc with
      mailbox := fun endpoint =>
        if resumable.scheduler.lifecycle.capabilities.objects endpoint then
          detached.1.ipc.mailbox endpoint
        else none }
    blockingContexts := detached.1.blocked
    deferredCancels :=
      BlockingIPCContext.setRetained detached.2 subject none }

@[simp] theorem installTerminatedSubject_deferred_self state subject resumable :
    (installTerminatedSubject state subject resumable).deferredCancels.retained subject =
      none := by
  simp [installTerminatedSubject, BlockingIPCContext.setRetained]

/-- Remove only the retiring identity's waiter/context/deferred source
attachments, without changing its still-live lifecycle projection.  This
normal form lets the shared termination/detachment proof reason uniformly
about current, blocked, and already-deferred subjects. -/
def detachTerminationSource (state : CompositeState)
    (subject : BlockingIPC.SubjectId) : CompositeState :=
  let deferred := BlockingIPCContext.setRetained state.deferredCancels subject none
  match state.blockingIPC.waiterEndpoint subject with
  | none => { state with deferredCancels := deferred }
  | some _ =>
      { state with
        blockingIPC := { state.blockingIPC with
          waiters := BlockingIPC.removeWaiter state.blockingIPC.waiters subject
          waiterEndpoint :=
            BlockingIPC.setWaiterEndpoint state.blockingIPC.waiterEndpoint subject none
          completion :=
            BlockingIPC.setCompletion state.blockingIPC.completion subject
              (some .cancelled) }
        blockingContexts :=
          BlockingIPCContext.setBlocked state.blockingContexts subject none
        deferredCancels := deferred }

/-- Publish interrupt-driven subject cleanup through the same authoritative
resumable/resource path as explicit termination, then close the kernel copy
window as required by every completed inbound entry. -/
def publishInterruptCleanup (state : CompositeState)
    (subject : Interrupt.SubjectId) : CompositeState :=
  let resumable := ResumablePreemption.cleanupSubject state.resumable subject
  let cleaned := installTerminatedResumable state resumable
  let selfRemoved := BlockingIPCContext.terminate state.blockingIPCContext subject
  let detached := BlockingIPCContext.detachInvalidated selfRemoved
    state.deferredCancels resumable.scheduler
  { cleaned with
    execution := { cleaned.execution with copyOverride := false }
    blockingIPC := { detached.1.ipc with
      mailbox := fun endpoint =>
        if resumable.scheduler.lifecycle.capabilities.objects endpoint then
          detached.1.ipc.mailbox endpoint
        else none }
    blockingContexts := detached.1.blocked
    deferredCancels := detached.2 }

/-- Publish a mapping-only transition without running the general lifecycle
synchronizer.  Map and unmap preserve the memory registry and address-space
owners, so rebuilding those projections would be both unnecessary and capable
of hiding an invalid pre-state. -/
def installVirtualMemory (state : CompositeState)
    (virtualMemory : VirtualMapping.State) (translations : TLB.State) : CompositeState :=
  let lifecycle := { state.lifecycle with
    mapping := fun space page => (virtualMemory.mappings space page).map (·.object) }
  let scheduler := { state.scheduler with lifecycle }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory }
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { translations with virtual := virtualMemory } }
    blockingIPC := { state.blockingIPC with scheduler } }

theorem installLifecycle_coherent state lifecycle :
    (installLifecycle state lifecycle).Coherent := by
  simp [installLifecycle, CompositeState.Coherent, restrictMailboxes, synchronizeMemory]
  constructor
  · intro subject hcurrent
    simp [hcurrent]
  constructor
  · intro object hdead
    split <;> simp_all
  · intro object envelope hmailbox
    cases hsource : state.ipc.endpoints.mailbox object with
    | none => simp [hsource] at hmailbox
    | some actual =>
        simp [hsource] at hmailbox
        rw [← hmailbox.2]
        exact hmailbox.1.2

theorem installVirtualMemory_preserves_runtimeWellFormed state virtualMemory translations
    (hstate : RuntimeWellFormed state)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory)
    (howner : virtualMemory.owner = state.virtualMemory.owner)
    (hvirtual : VirtualMapping.LifecycleWellFormed virtualMemory)
    (htlb : TLB.Coherent translations)
    (hactive : translations.active = state.resumable.translations.active) :
    RuntimeWellFormed (installVirtualMemory state virtualMemory translations) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, _hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent,
      hipcVirtualCoherent, hipcCapabilitiesCoherent,
      hresumableSchedulerCoherent, hresumableVirtualCoherent,
      htransfersCoherent, hauthorityCoherent, hdeadMailbox, hliveSender⟩
  have hcapabilitiesVirtual : virtualMemory.memory.capabilities = state.lifecycle.capabilities := by
    rw [hmemory, hvirtualCapabilitiesCoherent]
  have hownerLifecycle : virtualMemory.owner = state.lifecycle.addressOwner := by
    have hold := hresumable.2.2.2.2.2.2.1.1
    rw [hresumableVirtualCoherent, hresumableSchedulerCoherent,
      hschedulerCoherent] at hold
    rw [howner]
    exact hold
  rcases hexecution with ⟨_hcore, hbound, hmode⟩
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with
        mapping := fun space page => (virtualMemory.mappings space page).map (·.object) } := by
    simpa [SubjectLifecycle.WellFormed] using hlifecycle
  rcases hscheduler with ⟨_hschedulerLifecycle, hreadyNodup, hreadyCapacity,
    hreadyValid, hcurrentValid⟩
  simp only [Scheduler.ownsAddressSpace] at hreadyValid hcurrentValid
  rw [hschedulerCoherent] at hreadyValid hcurrentValid
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with
          mapping := fun space page => (virtualMemory.mappings space page).map (·.object) } } := by
    refine ⟨hlifecycle', hreadyNodup, hreadyCapacity, ?_, ?_⟩
    · simpa [Scheduler.ownsAddressSpace] using hreadyValid
    · simpa [Scheduler.ownsAddressSpace] using hcurrentValid
  refine ⟨?_, ?_, ?_, hcapabilities, hvirtual, ?_, ?_, ?_, ?_, htransfers, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, hcapabilitiesCoherent, ?_, rfl, ?_, rfl, rfl,
      htransfersCoherent, ?_, hdeadMailbox, hliveSender⟩
    · exact hcapabilitiesVirtual
    · exact hipcCapabilitiesCoherent
    · exact hauthorityCoherent
  · exact ⟨hlifecycle', by simp [installVirtualMemory], hmode⟩
  · exact hlifecycle'
  · exact ⟨hvirtual, hipc.2⟩
  · exact hscheduler'
  · rcases hpreemption with ⟨_, hticks⟩
    exact ⟨hscheduler', hticks⟩
  · rcases hresumable with
      ⟨_, hcapacity, hunique, hvalid, habsent, hagreement,
        htranslation, _hvirtualAgreement, hkinds, _htlb⟩
    simp only [ResumablePreemption.validContext] at hvalid
    simp only [ResumablePreemption.ReadyContextAgreement] at hagreement
    simp only [ResumablePreemption.TranslationAgreement] at htranslation
    rw [hresumableSchedulerCoherent, hschedulerCoherent] at hvalid habsent htranslation
    rw [hresumableSchedulerCoherent] at hagreement
    simp only [ResumablePreemption.ResourceKindAgreement] at hkinds
    rw [hresumableSchedulerCoherent, hschedulerCoherent] at hkinds
    refine ⟨?_, hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, htlb⟩
    · exact hscheduler'
    · simpa [installVirtualMemory, ResumablePreemption.validContext,
        hownerLifecycle] using hvalid
    · simpa [installVirtualMemory] using habsent
    · simpa [installVirtualMemory, ResumablePreemption.ReadyContextAgreement] using hagreement
    · refine ⟨hownerLifecycle, ?_⟩
      simpa [installVirtualMemory, hactive] using htranslation.2
    · exact ⟨hcapabilitiesVirtual, hvirtual⟩
    · simpa [installVirtualMemory, ResumablePreemption.ResourceKindAgreement] using hkinds
  · simpa [installVirtualMemory] using hhalted
  · simp [installVirtualMemory, CompositeState.BlockingIPCCoherent,
      hlive.2.1, hlive.2.2, hlive.2.2.2, hschedulerCoherent]
    exact hlive.2.2.2

/-- Mapping publication changes only the lifecycle mapping projection in the
blocking scheduler.  Every field used to validate waiters, mailboxes, and
saved contexts is retained literally, so the complete blocking invariant can
be carried across the same publication step as the virtual-memory/TLB proof. -/
theorem installVirtualMemory_preserves_blockingRuntimeWellFormed
    state virtualMemory translations (hstate : BlockingRuntimeWellFormed state)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory)
    (howner : virtualMemory.owner = state.virtualMemory.owner)
    (hvirtual : VirtualMapping.LifecycleWellFormed virtualMemory)
    (htlb : TLB.Coherent translations)
    (hactive : translations.active = state.resumable.translations.active) :
    BlockingRuntimeWellFormed
      (installVirtualMemory state virtualMemory translations) := by
  have hpost := installVirtualMemory_preserves_runtimeWellFormed
    state virtualMemory translations hstate.1 hmemory howner hvirtual htlb hactive
  refine ⟨hpost, ?_⟩
  have hscheduler := hpost.2.2.2.2.2.2.1
  have hschedulerLifecycle := hstate.1.1.2.1
  simpa [installVirtualMemory, CompositeState.blockingIPCContext,
      hstate.1.blockingScheduler, hschedulerLifecycle] using
    (blockingIPCContext_wellFormed_replaceScheduler state
      { state.scheduler with
        lifecycle := { state.lifecycle with
          mapping := fun space page => (virtualMemory.mappings space page).map (·.object) } }
      hstate.2 hscheduler (by simp [hstate.1.blockingScheduler, hschedulerLifecycle])
      (by simp [hstate.1.blockingScheduler, hschedulerLifecycle])
      (by simp [hstate.1.blockingScheduler, hschedulerLifecycle])
      (by simp [hstate.1.blockingScheduler, hschedulerLifecycle])
      (by simp [hstate.1.blockingScheduler, hschedulerLifecycle]))

theorem installLifecycle_clears_retired_mailbox state lifecycle object
    (hdead : lifecycle.capabilities.objects object ≠ true) :
    (installLifecycle state lifecycle).ipc.endpoints.mailbox object = none := by
  simp [installLifecycle, restrictMailboxes]
  cases state.ipc.endpoints.mailbox object <;> simp [hdead]

theorem installLifecycle_clears_dead_sender state lifecycle object envelope
    (hdead : lifecycle.capabilities.subjects envelope.sender ≠ true) :
    (installLifecycle state lifecycle).ipc.endpoints.mailbox object ≠ some envelope := by
  simp [installLifecycle, restrictMailboxes]
  cases hmailbox : state.ipc.endpoints.mailbox object with
  | none => simp
  | some actual =>
      by_cases hlive : lifecycle.capabilities.objects object = true ∧
          lifecycle.capabilities.subjects actual.sender = true
      · simp [hlive]
        intro heq
        subst actual
        exact hdead hlive.2
      · simp [hlive]

theorem installLifecycle_releases_retired_memory state lifecycle object frame
    (_hbinding : state.virtualMemory.memory.binding object = some frame)
    (howned : state.virtualMemory.memory.allocator.status frame = .owned object)
    (hretired : lifecycle.ownedMemory object = none) :
    (installLifecycle state lifecycle).virtualMemory.memory.binding object = none ∧
      (installLifecycle state lifecycle).virtualMemory.memory.allocator.status frame = .free := by
  simp [installLifecycle, synchronizeMemory, howned, hretired]

/-- Typed inputs to the actual subsystem transitions.  This is deliberately not
a tag paired with a caller-supplied post-state. -/
inductive Operation where
  | interrupt (frame : Interrupt.HardwareFrame)
  | nmi (raw : InterruptEntry.RawNmiEntry) (context : InterruptEntry.NmiContext)
  | selectUserReturn (purpose : Interrupt.ReturnPurpose)
  | userReturn (request : Interrupt.UserReturnRequest)
  | syscall (call : Syscall.UntrustedCall)
  | ipc (call : IPCSyscall.Call)
  | resumePreempt (frame : Interrupt.HardwareFrame)
      (registers : ResumablePreemption.Registers)
  | transferOffer (endpointWord sourceWord : UInt64)
      (sourceKind : Capability.ObjectKind) (payload : EndpointIPC.Payload)
      (rights : Capability.Rights)
  | transferAccept (endpointWord : UInt64) (destinationSlot : Nat)
  | capabilityCopy (source destination destinationSlot : Nat)
      (rights : Capability.Rights)
  | capabilityRevoke (authoritySlot victim victimSlot : Nat)
  | capabilityRevokeSubtree (authoritySlot victim victimSlot : Nat)
  | map (slot page : Nat) (permissions : VirtualMapping.Permissions)
  | unmap (page : Nat)
  | protect (page : Nat) (permissions : VirtualMapping.Permissions)
  | createSubject (subject : Nat)
  | terminateSubject (subject : Nat)
  | scheduleAdd (subject : Nat)
  | scheduleRemove (subject : Nat)
  | scheduleNext | scheduleYield | scheduleTick | terminateCurrent | restart

inductive UserReturnReply where
  | accepted
  | fatal (record : HaltRecord)
  | alreadyHalted (record : HaltRecord)
  deriving DecidableEq, Repr

/-- Composite IPC observation.  A data-only receive must not consume a
mailbox that carries a sealed capability descendant; that mailbox is reserved
for `transferAccept`, which installs the descendant atomically. -/
inductive CompositeIPCReply where
  | syscall (reply : IPCSyscall.Reply)
  | sealedTransferPending
  deriving DecidableEq, Repr

inductive OperationReply where
  | interrupt (action : EntryAction)
  | interruptIdentityRejected (subject : Interrupt.SubjectId)
  | nmi (action : EntryAction)
  | returnSelection (armed : Bool)
  | userReturn (reply : UserReturnReply)
  | syscall (reply : Syscall.Reply)
  | ipc (reply : CompositeIPCReply)
  | resume (restored : Option ResumablePreemption.Context)
      (error : Option ResumablePreemption.Error)
  | transferOffer (result : CapabilityTransfer.Result CapabilityTransfer.OfferError)
  | transferAccept (result : CapabilityTransfer.AcceptResult)
      (deliveredWord : Option UInt64)
  | capability (result : Capability.Result)
  | map (result : VirtualMapping.Result VirtualMapping.MapError)
  | unmap (result : VirtualMapping.Result VirtualMapping.UnmapError)
  | protect (result : VirtualMapping.Result TLB.ProtectError)
  | createSubject (result : SubjectLifecycle.Result SubjectLifecycle.CreateError)
  | terminateSubject (result : SubjectLifecycle.Result SubjectLifecycle.TerminateError)
  | scheduleRemove (result : ResumablePreemption.RemoveResult)
  | scheduler (result : Scheduler.Result)
  | restarted
  deriving DecidableEq, Repr

/-- Total classification of ordinary, nonfatal composite rejections.  This is
defined on the public reply itself, so a refinement boundary can decide the
class without manufacturing an operation-specific proof witness.  Entry and
user-return failures are excluded: they are transactional or fatal results,
not state-preserving subsystem rejections. -/
def OperationReply.isNonfatalRejection : OperationReply → Bool
  | .interruptIdentityRejected _ => true
  | .syscall (.rejected _) => true
  | .ipc (.syscall (.sendHandleRejected _)) => true
  | .ipc (.syscall (.sendRejected _)) => true
  | .ipc (.syscall (.receiveHandleRejected _)) => true
  | .ipc (.syscall (.receiveRejected _)) => true
  | .ipc .sealedTransferPending => true
  | .resume _ (some .fatalEntry) => false
  | .resume _ (some _) => true
  | .transferOffer (.rejected _) => true
  | .transferAccept (.rejected _) _ => true
  | .capability (.rejected _) => true
  | .map (.rejected _) => true
  | .unmap (.rejected _) => true
  | .protect (.rejected _) => true
  | .createSubject (.rejected _) => true
  | .terminateSubject (.rejected _) => true
  | .scheduleRemove (.rejected _) => true
  | .scheduler (.rejected _) => true
  | _ => false

inductive GateResult where
  | completed (reply : OperationReply)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure GateOutcome where
  state : CompositeState
  result : GateResult

/-- The public operation vocabulary carries only untrusted scalar call data.
Privileged identity is projected from the authoritative execution latch. -/
def CompositeState.syscallContext (state : CompositeState) : Syscall.TrustedContext :=
  { caller := state.execution.core.context.currentSubject
    activeAddressSpace := state.execution.core.context.activeAddressSpace }

def CompositeState.ipcContext (state : CompositeState) : IPCSyscall.TrustedContext :=
  { caller := state.execution.core.context.currentSubject
    activeAddressSpace := state.execution.core.context.activeAddressSpace }

@[simp] theorem syscallContext_caller (state : CompositeState) :
    state.syscallContext.caller = state.execution.core.context.currentSubject := rfl

@[simp] theorem syscallContext_addressSpace (state : CompositeState) :
    state.syscallContext.activeAddressSpace =
      state.execution.core.context.activeAddressSpace := rfl

@[simp] theorem ipcContext_caller (state : CompositeState) :
    state.ipcContext.caller = state.execution.core.context.currentSubject := rfl

@[simp] theorem ipcContext_addressSpace (state : CompositeState) :
    state.ipcContext.activeAddressSpace =
      state.execution.core.context.activeAddressSpace := rfl

structure CompositeIPCOutcome where
  state : CompositeState
  reply : CompositeIPCReply

def installIPC (state : CompositeState) (ipc : IPCSyscall.State) : CompositeState :=
  { state with
    ipc
    transfers := { state.transfers with toEndpointState := ipc.endpoints } }

/-- Invoke data-only IPC through the sealed-transfer authority boundary.  A
receive aimed at a tagged mailbox is rejected before the embedded endpoint
transition can consume either the envelope or its attachment metadata. -/
def dispatchIPC (state : CompositeState) (call : IPCSyscall.Call) :
    CompositeIPCOutcome :=
  match call with
  | .send handleWord word0 word1 =>
      let outcome := IPCSyscall.dispatch state.ipc state.ipcContext
        (.send handleWord word0 word1)
      { state := installIPC state outcome.state, reply := .syscall outcome.reply }
  | .receive handleWord =>
      match CapabilityHandle.resolveCurrent state.transfers.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint with
      | .ok endpoint =>
          match state.transfers.pending endpoint.capability.object with
          | some _ => { state, reply := .sealedTransferPending }
          | none =>
              let outcome := IPCSyscall.dispatch state.ipc state.ipcContext
                (.receive handleWord)
              { state := installIPC state outcome.state, reply := .syscall outcome.reply }
      | .error _ =>
          let outcome := IPCSyscall.dispatch state.ipc state.ipcContext
            (.receive handleWord)
          { state := installIPC state outcome.state, reply := .syscall outcome.reply }

/-- Public observation of IPC after the composite sealed-transfer guard and
authoritative caller/address-space projection have been applied. -/
def authoritativeIPCReply (state : CompositeState) (call : IPCSyscall.Call) :
    CompositeIPCReply :=
  (dispatchIPC state call).reply

/-- Exact composite post-state selected by one typed operation.  This is public
so refinement layers can state that their adapter agrees with the gate. -/
def applyOperation (state : CompositeState) : Operation → CompositeState
  | .interrupt frame =>
      let entry := dispatchHardware state.execution frame
      match entry.action with
      | .contained subject =>
          if state.lifecycle.current = some subject then
            publishInterruptCleanup state subject
          else state
      | .fatal _ =>
          installResumable { state with execution := entry.state }
            { state.resumable with halted := true }
      | .timer | .syscall | .rejected _ => { state with execution := entry.state }
      | .alreadyHalted _ => state
  | .nmi raw context =>
      let entry := dispatchNmi state.execution raw context
      match state.execution.mode with
      | .halted _ => state
      | .running | .handling _ =>
          { state with
            execution := entry.state
            resumable := { state.resumable with halted := true } }
  | .selectUserReturn purpose =>
      selectLiveReturnAuthority state purpose
  | .userReturn request =>
      let execution :=
        if state.ReturnPlanLive then state.execution
        else { state.execution with returnAuthorityArmed := false }
      let outcome := completeUserReturn execution request
      match outcome.action with
      | .fatal _ =>
          { state with
            execution := outcome.state
            resumable := { state.resumable with halted := true } }
      | .accepted _ | .alreadyHalted _ => { state with execution := outcome.state }
  | .syscall call =>
      let outcome := Syscall.dispatch state.virtualMemory state.syscallContext call
      match outcome.reply with
      | .rejected _ => state
      | .accepted =>
          match Syscall.decode call with
          | .ok (.access _ _) =>
              -- Translation checks do not mutate virtual memory; do not run a
              -- synchronization helper that could mask an invalid pre-state.
              selectLiveReturnAuthority state .syscallResume
          | .ok (.unmap page) =>
              let translations := TLB.invalidatePage
                { state.resumable.translations with virtual := outcome.state }
                state.execution.core.context.activeAddressSpace page
              let installed := installVirtualMemory state outcome.state translations
              selectLiveReturnAuthority installed .syscallResume
          | _ =>
              let translations := { state.resumable.translations with virtual := outcome.state }
              let installed := installVirtualMemory state outcome.state translations
              selectLiveReturnAuthority installed .syscallResume
  | .ipc call =>
      let outcome := dispatchIPC state call
      match outcome.reply with
      | .sealedTransferPending => state
      | .syscall (.sendHandleRejected _) => state
      | .syscall (.sendRejected _) => state
      | .syscall (.receiveHandleRejected _) => state
      | .syscall (.receiveRejected _) => state
      | .syscall .sent => outcome.state
      | .syscall (.delivered _ _ _) => outcome.state
  | .resumePreempt frame registers =>
      let outcome := ResumablePreemption.switch state.resumable state.execution.core
        frame registers
      match outcome.error with
      | some .fatalEntry =>
          if outcome.state.halted then
            let entry := dispatchHardware state.execution frame
            installResumable { state with execution := entry.state } outcome.state
          else state
      | some _ => state
      | none => installResumable state outcome.state
  | .transferOffer endpointWord sourceWord sourceKind payload rights =>
      let outcome := CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights
      match outcome.result with
      | .rejected _ => state
      | .accepted => installTransfers state outcome.state
  | .transferAccept endpointWord destinationSlot =>
      let outcome := CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot
      match outcome.result with
      | .rejected _ => state
      | .delivered _ => installTransfers state outcome.state
  | .capabilityCopy source destination destinationSlot rights =>
      let outcome := Capability.copy state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCopiedCapabilities state outcome.state
  | .capabilityRevoke authoritySlot victim victimSlot =>
      let outcome := Capability.revokeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCopiedCapabilities state outcome.state
  | .capabilityRevokeSubtree authoritySlot victim victimSlot =>
      let outcome := Capability.revokeSubtreeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          match Capability.lookup state.capabilities victim victimSlot with
          | .found target =>
              installRevokedSubtree state target.identity outcome.state
          | _ =>
              -- Unreachable: acceptance located the lineage root
              -- (`Capability.revokeSubtree_accepted_target`).  Publishing
              -- nothing is the fail-closed choice.
              state
  | .map slot page permissions =>
      let outcome := VirtualMapping.map state.virtualMemory
        state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          installVirtualMemory state outcome.state
            { state.resumable.translations with virtual := outcome.state }
  | .unmap page =>
      let outcome := VirtualMapping.unmap state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          let translations := TLB.invalidatePage
            { state.resumable.translations with virtual := outcome.state }
            state.execution.core.context.activeAddressSpace page
          installVirtualMemory state outcome.state translations
  | .protect page permissions =>
      let outcome := TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          installVirtualMemory state outcome.state.virtual outcome.state
  | .createSubject subject =>
      let outcome := SubjectLifecycle.create state.lifecycle subject
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCreatedSubject state subject
  | .terminateSubject subject =>
      let outcome := SubjectLifecycle.terminate state.lifecycle subject
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          installTerminatedSubject state subject
            (ResumablePreemption.cleanupSubject state.resumable subject)
  | .scheduleAdd subject =>
      let outcome := schedulerAdmission state subject
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installSchedulerAdmission state outcome.state
  | .scheduleRemove subject =>
      let outcome := ResumablePreemption.remove state.resumable subject
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installSchedulerRemoval state outcome.state
  | .scheduleNext =>
      let outcome := schedulerDispatch state
      match outcome.result with
      | .rejected _ => state
      | .accepted none => state
      | .accepted (some _) => installScheduler state outcome.state
  | .scheduleYield =>
      let outcome := schedulerYield state
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .scheduleTick =>
      let outcome := schedulerTick state
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .terminateCurrent =>
      let outcome := Scheduler.terminateCurrent state.scheduler
      match outcome.result with
      | .rejected _ => state
      | .accepted _ =>
          match state.scheduler.lifecycle.current with
          | none => state
          | some subject =>
              installTerminatedSubject state subject
                (ResumablePreemption.cleanupSubject state.resumable subject)
  | .restart => state

end LeanOS.FailStop
