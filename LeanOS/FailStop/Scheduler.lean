import LeanOS.FailStop.OperationRegistry

/-!
# Fail-stop composite: termination cleanup and scheduler families

Accepted termination publishes the authoritative resumable cleanup, and the
scheduler admission, removal, dispatch, yield, and tick families are
registered as complete runtime-preserving operations.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ### Accepted termination cleanup

Subject termination is published through the authoritative resumable cleanup,
not through lifecycle synchronization alone.  Consequently the accepted gate
step removes every scheduler and saved-context reference in the same mutation
that retires the subject identity. -/

/-- Typed acceptance of subject termination exposes the cleanup facts needed
by every future operation-family preservation proof: the subject is dead,
cannot remain current or queued, has no blocking, resumable, or deferred
context, and no in-flight sealed descendant survives the lifecycle teardown. -/
theorem terminateSubject_accepted_cleans_runtime_references state subject lifecycle
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.terminate state.lifecycle subject =
      { state := lifecycle, result := .accepted }) :
    (gate state (.terminateSubject subject)).result =
        .completed (.terminateSubject .accepted) ∧
      (gate state (.terminateSubject subject)).state.lifecycle.capabilities.subjects
          subject = false ∧
      subject ∉ (gate state (.terminateSubject subject)).state.scheduler.ready ∧
      (gate state (.terminateSubject subject)).state.scheduler.lifecycle.current ≠
          some subject ∧
      ResumablePreemption.contextFor
          (gate state (.terminateSubject subject)).state.resumable.contexts subject = none ∧
      (gate state (.terminateSubject subject)).state.blockingIPC.waiterEndpoint subject = none ∧
      (gate state (.terminateSubject subject)).state.blockingContexts subject = none ∧
      (gate state (.terminateSubject subject)).state.deferredCancels.retained subject = none ∧
      (∀ endpoint,
        (gate state (.terminateSubject subject)).state.transfers.pending endpoint = none) := by
  have hdead := ResumablePreemption.cleanup_terminates_subject
    state.resumable subject
  have hscheduler := ResumablePreemption.cleanup_removes_scheduler_membership
    state.resumable subject
  have hcontext := ResumablePreemption.cleanup_removes_context
    state.resumable subject
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    simp [haccepted]
  have hblockingClean := BlockingIPCContext.terminate_accepted_cleans_self
    state.blockingIPCContext subject hblockingAccepted
  have hdetachedClean :
      let detached := BlockingIPCContext.detachInvalidated
        (BlockingIPCContext.terminate state.blockingIPCContext subject)
        state.deferredCancels
        (ResumablePreemption.cleanupSubject state.resumable subject).scheduler
      detached.1.ipc.waiterEndpoint subject = none ∧
        detached.1.blocked subject = none := by
    simp [BlockingIPCContext.detachInvalidated,
      hblockingClean.1, hblockingClean.2]
  simp only [gate, hmode, operationReply, applyOperation, haccepted]
  simp only [installTerminatedSubject, hblockingAccepted,
    installTerminatedResumable, installTransfers,
    installResumable, installLifecycle]
  exact ⟨trivial, hdead, hscheduler.1, hscheduler.2, hcontext,
    hdetachedClean.1, hdetachedClean.2, by
      simp [installTerminatedSubject, BlockingIPCContext.setRetained],
    CapabilityTransfer.cancelAllOffers_pending _⟩

/-- Accepted subject termination removes every address-space ownership entry
for that subject in the same published lifecycle that retires its identity.
This exposes the lifecycle fact needed by outer authority publishers without
requiring them to unfold the private cleanup installer. -/
theorem terminateSubject_accepted_removes_owned_address_spaces
    state subject lifecycle
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.terminate state.lifecycle subject =
      { state := lifecycle, result := .accepted })
    addressSpace
    (howner : state.lifecycle.addressOwner addressSpace = some subject) :
    (gate state (.terminateSubject subject)).state.lifecycle.addressOwner
        addressSpace = none := by
  simp only [gate, hmode, operationReply, applyOperation, haccepted]
  simp only [installTerminatedSubject, installTerminatedResumable,
    installResumable, installLifecycle]
  rcases hstate.1 with
    ⟨_, hschedulerLifecycle, _, _, _, _, _, hresumableScheduler,
      _, _, _, _, _⟩
  apply ResumablePreemption.cleanup_removes_owned_address_space
  simpa [hresumableScheduler, hschedulerLifecycle] using howner

/-- Terminating an endpoint owner cannot strand a peer waiter on the retired
endpoint.  The peer's exact saved context moves from the waiter/context pair to
the quiescent deferred-cancellation bank, and the dead endpoint's modeled
mailbox is cleared in the same accepted composite transition. -/
theorem terminateSubject_accepted_defers_invalidated_waiter
    state owner lifecycle peer endpoint saved
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.terminate state.lifecycle owner =
      { state := lifecycle, result := .accepted })
    (hpeer : peer ≠ owner)
    (hendpoint :
      (BlockingIPCContext.terminate state.blockingIPCContext owner).ipc.waiterEndpoint peer =
        some endpoint)
    (hsaved :
      (BlockingIPCContext.terminate state.blockingIPCContext owner).blocked peer = some saved)
    (hretired :
      (ResumablePreemption.cleanupSubject state.resumable owner).scheduler.lifecycle.capabilities.objects
        endpoint = false) :
    let next := (gate state (.terminateSubject owner)).state
    (gate state (.terminateSubject owner)).result =
        .completed (.terminateSubject .accepted) ∧
      next.blockingIPC.waiterEndpoint peer = none ∧
      next.blockingContexts peer = none ∧
      next.deferredCancels.retained peer = some saved ∧
      next.blockingIPC.mailbox endpoint = none := by
  have hexact := BlockingIPCContext.detachInvalidated_invalidated_exact
    (BlockingIPCContext.terminate state.blockingIPCContext owner)
    state.deferredCancels
    (ResumablePreemption.cleanupSubject state.resumable owner).scheduler
    peer endpoint saved hendpoint hsaved hretired
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject] using
        hexact.1
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject] using
        hexact.2.1
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        BlockingIPCContext.setRetained, hpeer] using hexact.2.2
    · simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        hretired]

/-- Accepted termination preserves both scheduler projections, including when
cleanup leaves a lone current subject with no queued peer.  Such a state is
well formed because the next resumable timer operation rejects atomically. -/
theorem gate_terminateSubject_accepted_preserves_schedulerWellFormed
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    Scheduler.WellFormed
        (gate state (.terminateSubject subject)).state.scheduler ∧
      Preemption.WellFormed
        (gate state (.terminateSubject subject)).state.preemption := by
  have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
    state.resumable subject hstate.2.2.2.2.2.2.2.2.1
  have hscheduler := hcleanup.1
  have hpreemption := hstate.2.2.2.2.2.2.2.1
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    exact haccepted
  refine ⟨?_, ?_⟩
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using hscheduler
  · rcases hpreemption with ⟨_, hticks⟩
    refine ⟨?_, ?_⟩
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
        installTransfers, installResumable, installLifecycle] using hscheduler
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
        installTerminatedResumable] using hticks

/-- Accepted termination preserves the saved-context bank's capacity,
uniqueness, validity, current-subject exclusion, and ready-queue agreement,
including cleanup of the final queued peer.  These are the context-specific
components of `ResumablePreemption.WellFormed`; the virtual-memory projection
is deliberately left to the resource-cleanup integration slice. -/
theorem gate_terminateSubject_accepted_preserves_resumableContextBank
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    let next := (gate state (.terminateSubject subject)).state.resumable
    next.contexts.length ≤ next.capacity ∧
      next.contexts.Pairwise (fun first second => first.owner ≠ second.owner) ∧
      (∀ context, context ∈ next.contexts →
        ResumablePreemption.validContext next context) ∧
      (∀ candidate, next.scheduler.lifecycle.current = some candidate →
        ResumablePreemption.contextFor next.contexts candidate = none) ∧
      ResumablePreemption.ReadyContextAgreement next := by
  have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
    state.resumable subject hstate.2.2.2.2.2.2.2.2.1
  rcases hcleanup with
    ⟨_, hcapacity, hunique, hvalid, habsent, hready, _, _, _, _⟩
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    exact haccepted
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using hcapacity
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using hunique
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle,
      ResumablePreemption.validContext] using hvalid
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using habsent
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle,
      ResumablePreemption.ReadyContextAgreement] using hready

/-- The authoritative resumable cleanup publisher preserves the full runtime
invariant for every subject identifier.  This common boundary is used by both
explicit termination and interrupt-contained user faults. -/
theorem installTerminatedResumable_cleanup_preserves_runtimeWellFormed
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running) :
    RuntimeWellFormed
      (installTerminatedResumable state
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  let cleaned := ResumablePreemption.cleanupSubject state.resumable subject
  have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
    state.resumable subject hstate.2.2.2.2.2.2.2.2.1
  change ResumablePreemption.WellFormed cleaned at hcleanup
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  let endpoints : EndpointIPC.State :=
    { state.ipc.endpoints with
      capabilities := cleaned.scheduler.lifecycle.capabilities
      mailbox := restrictMailboxes cleaned.scheduler.lifecycle state.ipc.endpoints.mailbox }
  have hcleanVirtual := hcleanup.2.2.2.2.2.2.2.1
  have hcleanCapabilities : Capability.WellFormed
      cleaned.scheduler.lifecycle.capabilities := by
    rw [← hcleanVirtual.1]
    exact hcleanVirtual.2.2.1
  have hendpoint : EndpointIPC.WellFormed endpoints := by
    rcases hipc.2 with ⟨_oldCapabilities, hissued, hmailbox, _hdead, hhistory⟩
    refine ⟨by simpa [endpoints] using hcleanCapabilities, ?_, ?_, ?_, hhistory⟩
    · intro object hlive hkind
      have holdLive := ResumablePreemption.cleanup_live_object_was_live
        state.resumable subject object hlive
      have holdKind := ResumablePreemption.cleanup_object_kind_was_kind
        state.resumable subject object .endpoint hkind
      rw [hresumableSchedulerCoherent, hschedulerCoherent,
        ← hipcCapabilitiesCoherent] at holdLive holdKind
      exact hissued object holdLive holdKind
    · intro object envelope hnext
      cases hold : state.ipc.endpoints.mailbox object with
      | none => simp [endpoints, restrictMailboxes, hold] at hnext
      | some actual =>
          have hfacts := hnext
          have holdMailbox := hmailbox object actual hold
          simp [endpoints, restrictMailboxes, hold] at hfacts
          rcases hfacts with ⟨⟨hlive, _hliveSender⟩, rfl⟩
          obtain ⟨_holdLive, holdKind, hendpoint, hhistoryMember⟩ := holdMailbox
          exact ⟨by simpa [endpoints] using hlive,
            ResumablePreemption.cleanup_live_object_preserves_kind
              state.resumable subject object .endpoint hlive (by
                rw [hresumableSchedulerCoherent, hschedulerCoherent,
                  ← hipcCapabilitiesCoherent]
                exact holdKind),
            hendpoint, hhistoryMember⟩
    · intro object hretired
      by_cases hlive : cleaned.scheduler.lifecycle.capabilities.objects object = true
      · exact False.elim (hretired (by simpa [endpoints] using hlive))
      · cases hmail : state.ipc.endpoints.mailbox object <;>
          simp [endpoints, restrictMailboxes, hlive, hmail]
  let transferBase : CapabilityTransfer.State :=
    { state.transfers with toEndpointState := endpoints }
  let transfers := CapabilityTransfer.cancelAllOffers transferBase
  have htransfer : CapabilityTransfer.WellFormed transfers := by
    apply CapabilityTransfer.cancelAllOffers_preserves_wellFormed
    exact hendpoint
  have hfinalDead : ∀ object,
      cleaned.scheduler.lifecycle.capabilities.objects object ≠ true →
        transfers.mailbox object = none := by
    intro object hretired
    exact htransfer.1.2.2.2.1 object (by simpa [transfers, transferBase, endpoints] using hretired)
  have hfinalSender : ∀ object envelope, transfers.mailbox object = some envelope →
      cleaned.scheduler.lifecycle.capabilities.subjects envelope.sender = true := by
    intro object envelope hmail
    cases hpending : state.transfers.pending object with
    | some transfer =>
        simp [transfers, transferBase, CapabilityTransfer.cancelAllOffers,
          CapabilityTransfer.cancelWhere, hpending] at hmail
    | none =>
        cases hold : state.ipc.endpoints.mailbox object with
        | none =>
            simp [transfers, transferBase, endpoints, CapabilityTransfer.cancelAllOffers,
              CapabilityTransfer.cancelWhere, restrictMailboxes, hpending, hold] at hmail
        | some actual =>
            simp [transfers, transferBase, endpoints, CapabilityTransfer.cancelAllOffers,
              CapabilityTransfer.cancelWhere, restrictMailboxes, hpending, hold] at hmail
            rcases hmail with ⟨⟨_hlive, hsender⟩, heq⟩
            cases heq
            exact hsender
  have hfinalAuthority : ∀ candidate, cleaned.scheduler.lifecycle.current = some candidate →
      (installTerminatedResumable state cleaned).execution.core.context.currentSubject =
          candidate ∧
        (installTerminatedResumable state cleaned).execution.core.context.activeAddressSpace =
          candidate := by
    intro candidate hcurrent
    simp [installTerminatedResumable, hcurrent]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [installTerminatedResumable, CompositeState.Coherent,
      transfers, transferBase, endpoints] using
        And.intro hcleanVirtual.1
          (And.intro hfinalAuthority (And.intro hfinalDead hfinalSender))
  · rcases hexecution with ⟨_hexecutionCore, _hbound, hmodeWellFormed⟩
    refine ⟨hcleanup.1.1, by simp [installTerminatedResumable], ?_⟩
    simp [hmode] at hmodeWellFormed
    simp only [installTerminatedResumable, hmode]
    change (match cleaned.scheduler.lifecycle.current with
      | some subject => { state.execution.core.context with
          currentSubject := subject, activeAddressSpace := subject }
      | none => state.execution.core.context).entryActive = false
    cases hcurrent : cleaned.scheduler.lifecycle.current <;>
      simpa [hcurrent] using hmodeWellFormed
  · simpa [installTerminatedResumable] using hcleanup.1.1
  · simpa [installTerminatedResumable] using hcleanCapabilities
  · simpa [installTerminatedResumable] using hcleanVirtual.2
  · exact ⟨by simpa [installTerminatedResumable] using hcleanVirtual.2,
      by simpa [installTerminatedResumable, transfers, transferBase, endpoints] using htransfer.1⟩
  · simpa [installTerminatedResumable] using hcleanup.1
  · exact ⟨by simpa [installTerminatedResumable] using hcleanup.1, hpreemption.2⟩
  · simpa [installTerminatedResumable] using hcleanup
  · simpa [installTerminatedResumable, transfers, transferBase, endpoints] using htransfer
  · simpa [installTerminatedResumable, cleaned,
      ResumablePreemption.cleanupSubject] using hhalted
  · exact ⟨by simp [installTerminatedResumable], ⟨⟨rfl, rfl⟩, hlive.2.2⟩⟩

/-- Accepted subject termination is one complete runtime operation family:
authoritative lifecycle/resource/context cleanup and sealed-offer cancellation
are published atomically through every duplicated consumer. -/
theorem gate_terminateSubject_accepted_preserves_runtimeWellFormed
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    RuntimeWellFormed (gate state (.terminateSubject subject)).state := by
  have hpreserved := installTerminatedResumable_cleanup_preserves_runtimeWellFormed
    state subject hstate hmode
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    exact haccepted
  unfold RuntimeWellFormed at hpreserved ⊢
  rcases hpreserved with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive, hblocking,
      hportControls⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, CompositeState.Coherent] using hcoherent
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, WellFormed] using hexecution
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hlifecycle
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hcapabilities
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hvirtual
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hipc
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hscheduler
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hpreemption
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hresumable
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using htransfers
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hhalted
  · simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, hlive]
  · simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, BlockingIPCContext.detachInvalidated,
      CompositeState.BlockingIPCCoherent, hblocking]
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hportControls

/-- Accepted authoritative termination is also the global release/destruction
cache boundary.  Cleanup can retire memory visible through several roots, so
the globally well-formed successor carries the reviewed complete flush before
that retired capacity can be reused. -/
theorem gate_terminateSubject_accepted_flushes_translations
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    RuntimeWellFormed (gate state (.terminateSubject subject)).state ∧
      (gate state (.terminateSubject subject)).state.resumable.translations.entries = [] ∧
      ∀ key context,
        TLB.lookup
          (gate state (.terminateSubject subject)).state.resumable.translations.entries
          key context = none := by
  refine ⟨gate_terminateSubject_accepted_preserves_runtimeWellFormed
    state subject hstate hmode haccepted, ?_, ?_⟩
  · simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      installTerminatedResumable]
  · intro key context
    rw [show (gate state (.terminateSubject subject)).state.resumable.translations.entries =
        [] by
      simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        installTerminatedResumable]]
    simp [TLB.lookup]

/-- Every public subject-termination request preserves the global invariant:
never-issued/already-dead subjects reject atomically, while acceptance performs
the complete lifecycle, resource, context, mailbox, and transfer cleanup. -/
theorem terminateSubject_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.terminateSubject subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hterminate : SubjectLifecycle.terminate state.lifecycle subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.terminateSubject subject) (.terminateSubject (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hterminate])
              (.terminateSubject subject reason (by simp [hterminate]))).1
        | accepted =>
            exact gate_terminateSubject_accepted_preserves_runtimeWellFormed
              state subject hstate hmode (by simp [hterminate])
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.terminateSubject subject) hstate hmode

/-! ### Scheduler rejection preservation

The raw accepted dispatch/yield/tick operations do not yet own the resumable
context-bank update needed to satisfy `RuntimeWellFormed`.  Their typed
rejections, however, are complete operation-level slices: the scheduler
transition is literally unchanged, and the composite gate publishes no
synchronization repair.  Stating these facts at the public gate boundary keeps
the accepted context-publication obligation explicit while allowing rejected
scheduler traces to compose with the already-covered operation families. -/

/-- Empty dispatch is the accepted scheduler case that needs no resumable
context publication: `selectNext` returns `accepted none` only when it retains
the exact scheduler state.  The composite gate therefore reports the typed
success while preserving every runtime projection byte-for-byte. -/
theorem scheduleNext_accepted_none_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (schedulerDispatch state).result = .accepted none) :
    RuntimeWellFormed (gate state .scheduleNext).state ∧
      (gate state .scheduleNext).state = state ∧
      (gate state .scheduleNext).result =
        .completed (.scheduler (.accepted none)) := by
  have hunchanged := schedulerDispatch_accepted_none_unchanged state haccepted
  simp [gate, hmode, applyOperation, operationReply, haccepted, hunchanged, hstate]

theorem scheduleNext_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (schedulerDispatch state).result = .rejected reason) :
    RuntimeWellFormed (gate state .scheduleNext).state ∧
      (gate state .scheduleNext).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := schedulerDispatch_rejected_unchanged state reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .scheduleNext hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

theorem scheduleYield_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (schedulerYield state).result = .rejected reason) :
    RuntimeWellFormed (gate state .scheduleYield).state ∧
      (gate state .scheduleYield).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := schedulerYield_rejected_unchanged state reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .scheduleYield hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

theorem scheduleTick_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (schedulerTick state).result = .rejected reason) :
    RuntimeWellFormed (gate state .scheduleTick).state ∧
      (gate state .scheduleTick).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := schedulerTick_rejected_unchanged state reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .scheduleTick hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

theorem terminateCurrent_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (Scheduler.terminateCurrent state.scheduler).result = .rejected reason) :
    RuntimeWellFormed (gate state .terminateCurrent).state ∧
      (gate state .terminateCurrent).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := Scheduler.terminateCurrent_rejected_unchanged
      state.scheduler reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .terminateCurrent hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

/-- Current-subject termination is the scheduler-selected spelling of the
authoritative subject-cleanup operation.  On a coherent runtime both select
the same live subject and publish the same lifecycle, resource, mailbox,
translation, and saved-context cleanup; busy and halted modes remain absorbed
by the outer gate. -/
theorem terminateCurrent_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .terminateCurrent := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hcurrent : state.scheduler.lifecycle.current with
    | none =>
        have hrejected : (Scheduler.terminateCurrent state.scheduler).result =
            .rejected .noCurrent := by
          simp [Scheduler.terminateCurrent, hcurrent, Scheduler.reject]
        exact (terminateCurrent_rejected_preserves_runtimeWellFormed
          state .noCurrent hstate hrejected).1
    | some subject =>
        have hschedulerLifecycle : state.scheduler.lifecycle = state.lifecycle :=
          hstate.1.2.1
        have hlifecycleCurrent : state.lifecycle.current = some subject := by
          rw [← hschedulerLifecycle]
          exact hcurrent
        have hsame :
            (gate state .terminateCurrent).state =
              (gate state (.terminateSubject subject)).state := by
          cases hterminate : SubjectLifecycle.terminate state.lifecycle subject with
          | mk lifecycle result =>
              cases result <;>
                simp [gate, hmode, applyOperation, Scheduler.terminateCurrent,
                  Scheduler.reject, hcurrent, hschedulerLifecycle, hlifecycleCurrent,
                  hterminate]
        rw [hsame]
        exact terminateSubject_operationPreservesRuntimeWellFormed subject state hstate
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .terminateCurrent hstate hmode

/-- Resumable-aware scheduler removal closes the cleanup obligation exposed by
the raw scheduler transition.  Saved context and active translation cleanup
are published with the scheduler post-state, while the no-peer case is a typed,
state-preserving rejection. -/
theorem scheduleRemove_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.scheduleRemove subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hremove : ResumablePreemption.remove state.resumable subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.scheduleRemove subject) (.scheduleRemove (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hremove])
              (.scheduleRemove subject reason (by simp [hremove]))).1
        | accepted context =>
            rcases hstate with
              ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
                hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
            rcases hcoherent with
              ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
                hcapabilitiesCoherent, hvirtualCapabilitiesCoherent,
                hipcVirtualCoherent, hipcCapabilitiesCoherent,
                hresumableSchedulerCoherent, hresumableVirtualCoherent,
                htransfersCoherent, hauthorityCoherent, hdeadMailbox, hliveSender⟩
            have hresumable' := ResumablePreemption.remove_preserves_wellFormed
              state.resumable subject hresumable
            rw [hremove] at hresumable'
            rcases ResumablePreemption.remove_accepted_exact state.resumable subject context
                (by simp [hremove]) with
              ⟨scheduler, hschedulerRemove, hnext, hpeer⟩
            rw [hremove] at hnext
            change next = ResumablePreemption.removeState
              state.resumable subject scheduler at hnext
            subst next
            have hschedulerRemove' : Scheduler.remove state.scheduler subject =
                { state := scheduler, result := .accepted context } := by
              rw [← hresumableSchedulerCoherent]
              exact hschedulerRemove
            have hschedulerCapabilities :
                scheduler.lifecycle.capabilities = state.lifecycle.capabilities := by
              simp only [Scheduler.remove] at hschedulerRemove'
              split at hschedulerRemove'
              · rcases hschedulerRemove' with ⟨rfl, rfl⟩
                exact hschedulerCoherent ▸ rfl
              · simp_all [Scheduler.reject]
            have hvirtualProjection :
                (ResumablePreemption.removeState state.resumable subject scheduler).translations.virtual =
                  state.virtualMemory := by
              simpa [ResumablePreemption.removeState] using hresumableVirtualCoherent
            have hcoherent' :
                (installSchedulerRemoval state
                  (ResumablePreemption.removeState state.resumable subject scheduler)).Coherent := by
              refine ⟨rfl, rfl, rfl, ?_, ?_, hipcVirtualCoherent, ?_, rfl,
                hvirtualProjection, htransfersCoherent, ?_, ?_, ?_⟩
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hcapabilitiesCoherent, hschedulerCapabilities]
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hvirtualCapabilitiesCoherent, hschedulerCapabilities]
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hipcCapabilitiesCoherent, hschedulerCapabilities]
              · intro current hcurrent
                simp only [installSchedulerRemoval, ResumablePreemption.removeState] at hcurrent ⊢
                cases hschedulerCurrent : scheduler.lifecycle.current with
                | none => simp [hschedulerCurrent] at hcurrent
                | some actual =>
                    simp [hschedulerCurrent] at hcurrent
                    subst current
                    simp [hschedulerCurrent]
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hschedulerCapabilities]
                exact hdeadMailbox
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hschedulerCapabilities]
                exact hliveSender
            simp only [gate, hmode, applyOperation, hremove]
            refine ⟨hcoherent', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hresumable', ?_, ?_, ?_⟩
            · rcases hexecution with ⟨hexecutionCore, _hbound, hmodeWellFormed⟩
              refine ⟨?_, by simp [installSchedulerRemoval], ?_⟩
              · simpa [Interrupt.WellFormed, installSchedulerRemoval] using
                  hresumable'.1.1
              · cases hschedulerCurrent : scheduler.lifecycle.current <;>
                  simpa [installSchedulerRemoval, ResumablePreemption.removeState,
                    hschedulerCurrent] using hmodeWellFormed
            · exact hresumable'.1.1
            · exact hcapabilities
            · exact hvirtual
            · exact hipc
            · exact hresumable'.1
            · rcases hpreemption with ⟨_, hticks⟩
              exact ⟨hresumable'.1, hticks⟩
            · exact htransfers
            · simpa [installSchedulerRemoval, ResumablePreemption.removeState] using hhalted
            · exact ⟨by simp [installSchedulerRemoval],
                ⟨⟨rfl, rfl⟩, hlive.2.2⟩⟩
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.scheduleRemove subject) hstate hmode

/-- Accepted capability revocation composes with authoritative resumable-aware
scheduler removal.  In particular, the scheduler/lifecycle cleanup step starts
from the exact globally well-formed capability post-state rather than a stale
pre-revocation projection. -/
theorem capabilityRevoke_then_scheduleRemove_preserves_runtimeWellFormed state authoritySlot
    victim victimSlot capabilities subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := capabilities, result := .accepted }) :
    RuntimeWellFormed (runOperations state
      [.capabilityRevoke authoritySlot victim victimSlot, .scheduleRemove subject]) := by
  simp only [runOperations]
  apply scheduleRemove_operationPreservesRuntimeWellFormed subject
  exact (gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state authoritySlot victim
    victimSlot capabilities hstate hmode haccepted).1

/-- Transitive lineage revocation has the same scheduler/lifecycle composition
boundary: all capability consumers observe the accepted subtree post-state
before resumable context and active-translation cleanup executes. -/
theorem capabilityRevokeSubtree_then_scheduleRemove_preserves_runtimeWellFormed state
    authoritySlot victim victimSlot capabilities subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := capabilities, result := .accepted }) :
    RuntimeWellFormed (runOperations state
      [.capabilityRevokeSubtree authoritySlot victim victimSlot, .scheduleRemove subject]) := by
  simp only [runOperations]
  apply scheduleRemove_operationPreservesRuntimeWellFormed subject
  exact (gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state authoritySlot
    victim victimSlot capabilities hstate hmode haccepted).1

/-- Creating a fresh subject only promotes its monotonic lifecycle identity;
all existing resource, scheduler, context-bank, mailbox, and translation
facts remain valid when the new lifecycle is published to their projections. -/
theorem createSubject_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.createSubject subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hcreate : SubjectLifecycle.create state.lifecycle subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.createSubject subject) (.createSubject (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hcreate])
              (.createSubject subject reason (by simp [hcreate]))).1
        | accepted =>
            have hcreateDef := hcreate
            simp only [SubjectLifecycle.create] at hcreateDef
            split at hcreateDef <;> try simp_all [SubjectLifecycle.reject]
            split at hcreateDef <;> try simp_all [SubjectLifecycle.reject]
            next hlive hissued =>
              rcases hcreateDef with ⟨rfl, rfl⟩
              simp only [gate, hmode, applyOperation, hcreate]
              rcases hstate with
                ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
                  hscheduler, hpreemption, hresumable, htransfers, hhalted, hlivePlan⟩
              have hlifecycle' := SubjectLifecycle.create_preserves_wellFormed
                state.lifecycle subject hlifecycle
              rw [hcreate] at hlifecycle'
              have hcapabilitiesLifecycle :
                  Capability.WellFormed state.lifecycle.capabilities := by
                rw [← hcoherent.2.2.2.1]
                exact hcapabilities
              have hvirtualCapabilitiesCoherent :
                  state.virtualMemory.memory.capabilities =
                    state.lifecycle.capabilities := hcoherent.2.2.2.2.1
              have hipcCapabilitiesCoherent :
                  state.ipc.endpoints.capabilities =
                    state.lifecycle.capabilities := hcoherent.2.2.2.2.2.2.1
              have hcapabilities' : Capability.WellFormed
                  (SubjectLifecycle.create state.lifecycle subject).state.capabilities := by
                rw [hcreate]
                rcases hcapabilitiesLifecycle with
                  ⟨hslots, hderivations, hunique, hspaces⟩
                refine ⟨?_, hderivations, hunique, hspaces⟩
                intro holder slot capability hslot
                have hold := hslots holder slot capability hslot
                refine ⟨?_, hold.2⟩
                simp only [SubjectLifecycle.setBool]
                split <;> simp_all
              have hvirtual' : VirtualMapping.LifecycleWellFormed
                  (installCreatedSubject state subject).virtualMemory := by
                rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hvirtualCaps,
                  haddressSpaces, hownedSpaces⟩
                refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
                · intro addressSpace owner howner
                  have hold := hownerLive addressSpace owner (by
                    simpa [installCreatedSubject] using howner)
                  rw [hvirtualCapabilitiesCoherent] at hold
                  simpa [installCreatedSubject] using
                    createSubject_preserves_live state.lifecycle subject owner hold
                · intro addressSpace page mapping hmapping
                  obtain ⟨owner, frame, howner, hpermissions, hbinding, hframe,
                    hread, hwrite⟩ := hmappings addressSpace page mapping (by
                      simpa [installCreatedSubject] using hmapping)
                  refine ⟨owner, frame, ?_, hpermissions, ?_, hframe, ?_, ?_⟩
                  · simpa [installCreatedSubject] using howner
                  · simpa [installCreatedSubject] using hbinding
                  · intro hpermission
                    have hold := hread hpermission
                    rw [hvirtualCapabilitiesCoherent] at hold
                    simpa [installCreatedSubject, hcreate, Capability.HasAuthority] using hold
                  · intro hpermission
                    have hold := hwrite hpermission
                    rw [hvirtualCapabilitiesCoherent] at hold
                    simpa [installCreatedSubject, hcreate, Capability.HasAuthority] using hold
                · simpa [installCreatedSubject, hcreate] using hcapabilities'
                · intro addressSpace owner howner
                  have hold := haddressSpaces addressSpace owner (by
                    simpa [installCreatedSubject] using howner)
                  rw [hvirtualCapabilitiesCoherent] at hold
                  simpa [installCreatedSubject, hcreate, Capability.HasAuthority] using hold
                · intro addressSpace hlive hkind
                  have hliveOld :
                      state.virtualMemory.memory.capabilities.objects addressSpace = true := by
                    rw [hvirtualCapabilitiesCoherent]
                    simpa [installCreatedSubject, hcreate] using hlive
                  have hkindOld :
                      state.virtualMemory.memory.capabilities.kinds addressSpace =
                        some .addressSpace := by
                    rw [hvirtualCapabilitiesCoherent]
                    simpa [installCreatedSubject, hcreate] using hkind
                  obtain ⟨owner, howner⟩ := hownedSpaces addressSpace
                    hliveOld hkindOld
                  exact ⟨owner, by simpa [installCreatedSubject] using howner⟩
              have hipc' : IPCSyscall.WellFormed
                  (installCreatedSubject state subject).ipc := by
                rcases hipc with ⟨_virtual, hendpoints⟩
                rcases hendpoints with
                  ⟨_hendpointCaps, hissuedEndpoint, hmailbox, hdead, hhistory⟩
                rw [hipcCapabilitiesCoherent] at hissuedEndpoint hmailbox hdead
                refine ⟨hvirtual', ?_⟩
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simpa [installCreatedSubject, hcreate] using hcapabilities'
                · simpa [installCreatedSubject, hcreate] using hissuedEndpoint
                · simpa [installCreatedSubject, hcreate] using hmailbox
                · simpa [installCreatedSubject, hcreate] using hdead
                · simpa [installCreatedSubject] using hhistory
              have hscheduler' : Scheduler.WellFormed
                  (installCreatedSubject state subject).scheduler := by
                rcases hscheduler with
                  ⟨_hschedulerLifecycle, hreadyNodup, hreadyCapacity,
                    hreadyValid, hcurrentValid⟩
                simp only [Scheduler.ownsAddressSpace] at hreadyValid hcurrentValid
                rw [hcoherent.2.1] at hreadyValid hcurrentValid
                refine ⟨?_, hreadyNodup, hreadyCapacity, ?_, ?_⟩
                · simpa [installCreatedSubject, hcreate] using hlifecycle'
                · intro candidate hmember
                  obtain ⟨hliveCandidate, hrunnable, howner⟩ :=
                    hreadyValid candidate hmember
                  refine ⟨?_, ?_, ?_⟩
                  · exact createSubject_preserves_live state.lifecycle subject candidate
                      hliveCandidate
                  · simpa [installCreatedSubject, hcreate] using hrunnable
                  · simpa [Scheduler.ownsAddressSpace, installCreatedSubject,
                      hcreate] using howner
                · intro candidate hcurrent
                  obtain ⟨hliveCandidate, hrunnable, howner⟩ :=
                    hcurrentValid candidate (by
                      simpa [installCreatedSubject] using hcurrent)
                  refine ⟨?_, ?_, ?_⟩
                  · exact createSubject_preserves_live state.lifecycle subject candidate
                      hliveCandidate
                  · simpa [installCreatedSubject, hcreate] using hrunnable
                  · simpa [Scheduler.ownsAddressSpace, installCreatedSubject,
                      hcreate] using howner
              have hpreemption' : Preemption.WellFormed
                  (installCreatedSubject state subject).preemption := by
                rcases hpreemption with ⟨_hscheduler, hticks⟩
                refine ⟨hscheduler', ?_⟩
                change state.preemption.acceptedTicks =
                  if state.preemption.timerArmed then 0 else 1
                exact hticks
              have hresumableLifecycle :
                  state.resumable.scheduler.lifecycle = state.lifecycle := by
                rw [hcoherent.2.2.2.2.2.2.2.1, hcoherent.2.1]
              have hresumable' : ResumablePreemption.WellFormed
                  (installCreatedSubject state subject).resumable := by
                rcases hresumable with
                  ⟨_hscheduler, hcapacity, hunique, hvalid, habsent, hready,
                    htranslation, _hvirtualAgreement, hkinds, htlb⟩
                simp only [ResumablePreemption.ReadyContextAgreement] at hready
                simp only [ResumablePreemption.TranslationAgreement] at htranslation
                simp only [ResumablePreemption.ResourceKindAgreement] at hkinds
                rw [hcoherent.2.2.2.2.2.2.2.1] at habsent hready htranslation hkinds
                rw [hcoherent.2.2.2.2.2.2.2.2.1] at htranslation
                rw [hcoherent.2.1] at habsent htranslation hkinds
                refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro context hcontext
                  rcases hvalid context hcontext with
                    ⟨hframe, hspace, hliveOwner, hrunnable, howner⟩
                  rw [hresumableLifecycle] at hliveOwner hrunnable howner
                  refine ⟨hframe, hspace, ?_, ?_, ?_⟩
                  · exact createSubject_preserves_live state.lifecycle subject context.owner
                      hliveOwner
                  · simpa [installCreatedSubject, hcreate] using hrunnable
                  · simpa [installCreatedSubject, hcreate] using howner
                · simpa [installCreatedSubject] using habsent
                · simpa [ResumablePreemption.ReadyContextAgreement,
                    installCreatedSubject] using hready
                · simpa [ResumablePreemption.TranslationAgreement,
                    installCreatedSubject, hcreate] using htranslation
                · exact ⟨rfl, hvirtual'⟩
                · simpa [ResumablePreemption.ResourceKindAgreement,
                    installCreatedSubject, hcreate] using hkinds
                · simpa [TLB.Coherent, installCreatedSubject] using htlb
              have htransfers' : CapabilityTransfer.WellFormed
                  (installCreatedSubject state subject).transfers := by
                rcases htransfers with ⟨_hendpoints, hpending⟩
                refine ⟨hipc'.2, ?_⟩
                intro endpoint transfer hpendingNew
                have hpendingOld : state.transfers.pending endpoint = some transfer := by
                  simpa [installCreatedSubject] using hpendingNew
                have hold := hpending endpoint transfer hpendingOld
                rw [hcoherent.2.2.2.2.2.2.2.2.2.1] at hold
                rw [hipcCapabilitiesCoherent] at hold
                simpa [installCreatedSubject, hcreate] using hold
              refine ⟨installCreatedSubject_coherent _ _ hcoherent, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_⟩
              · rcases hexecution with ⟨_hexecutionCore, _hbound, hmodeWellFormed⟩
                refine ⟨?_, by simp [installCreatedSubject], ?_⟩
                · simpa [Interrupt.WellFormed, installCreatedSubject, hcreate] using hlifecycle'
                · simpa [installCreatedSubject, hmode] using hmodeWellFormed
              · simpa [installCreatedSubject, hcreate] using hlifecycle'
              · simpa [installCreatedSubject, hcreate] using hcapabilities'
              · exact hvirtual'
              · exact hipc'
              · exact hscheduler'
              · exact hpreemption'
              · exact hresumable'
              · exact htransfers'
              · simpa [installCreatedSubject] using hhalted
              · exact ⟨by simp [installCreatedSubject],
                  ⟨⟨rfl, rfl⟩, hlivePlan.2.2⟩⟩
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.createSubject subject) hstate hmode

/-- Composite queue admission can report success only when the inserted
subject's kernel-owned context was already staged in the pre-state. -/
theorem gate_scheduleAdd_accepted_runtimeWellFormed_requires_staged_context
    state subject context next
    (_hmode : state.execution.mode = .running)
    (haccepted : schedulerAdmission state subject =
      { state := next, result := .accepted context }) :
    ∃ saved, saved ∈ state.resumable.contexts ∧ saved.owner = subject := by
  exact (schedulerAdmission_accepted_exact state subject context next haccepted).2.2

/-- Queue admission retains the authoritative lifecycle and appends exactly
the admitted subject.  These small projections keep the composite proof from
depending on the validation order inside `Scheduler.add`. -/
theorem schedulerAdd_accepted_projections state subject context next
    (haccepted : Scheduler.add state subject =
      { state := next, result := .accepted context }) :
    next.lifecycle = state.lifecycle ∧ next.ready = state.ready ++ [subject] := by
  simp only [Scheduler.add] at haccepted
  split at haccepted <;> try simp_all [Scheduler.reject]
  split at haccepted <;> try simp_all [Scheduler.reject]
  split at haccepted <;> try simp_all [Scheduler.reject]
  next addressSpace hspace =>
    split at haccepted <;> try simp_all [Scheduler.reject]
    split at haccepted <;> try simp_all [Scheduler.reject]
    rcases haccepted with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Accepted queue admission preserves the complete runtime invariant when
the subject's kernel-owned initial context was staged before admission.  The
narrow publication step changes no lifecycle, resource, mailbox, translation,
or execution projection and adds the staged context owner to the ready queue
observed by both scheduler consumers. -/
theorem gate_scheduleAdd_accepted_preserves_runtimeWellFormed
    state subject context next saved
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context })
    (hsaved : saved ∈ state.resumable.contexts ∧ saved.owner = subject)
    (hnotRetained : state.deferredCancels.retained subject = none) :
    RuntimeWellFormed (gate state (.scheduleAdd subject)).state ∧
      (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.accepted context)) := by
  have hadmission : schedulerAdmission state subject =
      { state := next, result := .accepted context } := by
    rw [schedulerAdmission_eq_add_of_staged state subject saved hsaved hnotRetained,
      haccepted]
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  obtain ⟨hlifecycleNext, hreadyNext⟩ :=
    schedulerAdd_accepted_projections state.scheduler subject context next haccepted
  have hscheduler' : Scheduler.WellFormed next := by
    have hold := Scheduler.add_preserves_wellFormed state.scheduler subject hscheduler
    simpa [haccepted] using hold
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with scheduler := next } := by
    rcases hresumable with
      ⟨_hscheduler, hcapacity, hunique, hvalid, habsent,
        ⟨hreadyContexts, hsuspendedReady⟩,
        htranslation, hvirtualAgreement, hkinds, htlb⟩
    rw [hresumableSchedulerCoherent] at hreadyContexts hsuspendedReady
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, htlb⟩
    · intro candidate hcandidate
      have hold := hvalid candidate hcandidate
      simpa [ResumablePreemption.validContext, hlifecycleNext,
        hresumableSchedulerCoherent] using hold
    · intro current hcurrent
      apply habsent current
      simpa [hlifecycleNext, hresumableSchedulerCoherent] using hcurrent
    · refine ⟨?_, ?_⟩
      · intro candidate hmember
        rw [hreadyNext] at hmember
        rcases List.mem_append.mp hmember with hold | hold
        · exact hreadyContexts candidate hold
        · simp only [List.mem_singleton] at hold
          subst candidate
          exact ⟨saved, hsaved.1, hsaved.2⟩
      · intro candidate hcandidate hsuspended
        rw [hreadyNext]
        exact List.mem_append_left _ (hsuspendedReady candidate hcandidate hsuspended)
    · rcases htranslation with ⟨howner, hactive⟩
      refine ⟨?_, ?_⟩
      · simpa [hlifecycleNext, hresumableSchedulerCoherent] using howner
      · simpa [hlifecycleNext, hresumableSchedulerCoherent] using hactive
    · rcases hvirtualAgreement with ⟨hcapabilities, hwellFormed⟩
      exact ⟨by simpa [hlifecycleNext, hresumableSchedulerCoherent] using hcapabilities,
        hwellFormed⟩
    · rcases hkinds with ⟨hmemory, hendpoint⟩
      refine ⟨?_, ?_⟩
      · intro object owner frame howned
        have hold := hmemory object owner frame (by
          simpa [hlifecycleNext, hresumableSchedulerCoherent] using howned)
        simpa [hlifecycleNext, hresumableSchedulerCoherent] using hold
      · intro object owner howned
        have hold := hendpoint object owner (by
          simpa [hlifecycleNext, hresumableSchedulerCoherent] using howned)
        simpa [hlifecycleNext, hresumableSchedulerCoherent] using hold
  have hcoherent' : (installSchedulerAdmission state next).Coherent := by
    simp only [installSchedulerAdmission, CompositeState.Coherent]
    refine ⟨hexecutionCoherent, ?_, trivial, hcapabilitiesCoherent,
      hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, trivial, hresumableVirtualCoherent,
      htransfersCoherent, hauthorityCoherent, hdeadMailbox, hliveSender⟩
    rw [hlifecycleNext, hschedulerCoherent]
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler := next } :=
    ⟨hscheduler', hpreemption.2⟩
  constructor
  · simp only [gate, hmode, applyOperation, hadmission]
    exact ⟨hcoherent', hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler', hpreemption', hresumable', htransfers, hhalted,
      hlive.1, by simp [installSchedulerAdmission,
        CompositeState.BlockingIPCCoherent, hlifecycleNext, hschedulerCoherent],
      hlive.2.2⟩
  · simp [gate, hmode, operationReply, hadmission]

/-- Negative admission regression: an otherwise accepted raw insertion cannot
cross the composite gate without its kernel-owned resumable context. -/
theorem scheduleAdd_missing_context_rejected_atomic state subject context next
    (hmode : state.execution.mode = .running)
    (hadd : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context })
    (hnotRetained : state.deferredCancels.retained subject = none)
    (hmissing : ResumablePreemption.contextFor state.resumable.contexts subject = none) :
    (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.rejected .noResumableContext)) ∧
      (gate state (.scheduleAdd subject)).state = state := by
  simp [gate, hmode, operationReply, applyOperation, schedulerAdmission,
    hnotRetained, hadd, hmissing, Scheduler.reject]

/-- Queue admission is a complete public operation family: raw scheduler
rejections and missing-context integration failures are atomic, while every
reported success publishes the exact staged context owner to both scheduler
consumers and preserves the complete runtime invariant. -/
theorem scheduleAdd_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.scheduleAdd subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hadmission : schedulerAdmission state subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.scheduleAdd subject) (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hadmission])
              (.scheduleAdd subject reason (by simp [hadmission]))).1
        | accepted context =>
            obtain ⟨hnotRetained, hadd, saved, hmember, howner⟩ :=
              schedulerAdmission_accepted_exact state subject context next hadmission
            exact (gate_scheduleAdd_accepted_preserves_runtimeWellFormed
              state subject context next saved hstate hmode hadd ⟨hmember, howner⟩
                hnotRetained).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.scheduleAdd subject) hstate hmode

/-- Raw dispatch is a complete operation family at the composite boundary:
empty selection succeeds without mutation, while a selection that would need
context restoration is rejected atomically. -/
theorem scheduleNext_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .scheduleNext := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hdispatch : schedulerDispatch state with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              .scheduleNext (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hdispatch])
              (.scheduleNext reason (by simp [hdispatch]))).1
        | accepted context =>
            have hnone := schedulerDispatch_accepted_is_none state context (by
              simp [hdispatch])
            subst context
            exact (scheduleNext_accepted_none_preserves_runtimeWellFormed
              state hstate hmode (by simp [hdispatch])).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .scheduleNext hstate hmode

/-- Raw yield cannot mutate without the outgoing saved context, so every
running result is a typed atomic rejection and every non-running result is
absorbed by the outer gate. -/
theorem scheduleYield_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .scheduleYield := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hyield : schedulerYield state with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              .scheduleYield (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hyield])
              (.scheduleYield reason (by simp [hyield]))).1
        | accepted context =>
            exact False.elim ((schedulerYield_ne_accepted state context) (by
              simp [hyield]))
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .scheduleYield hstate hmode

/-- Raw tick is confined to the same atomic missing-save rejection as yield;
timer-driven switching is provided by `resumePreempt`. -/
theorem scheduleTick_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .scheduleTick := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases htick : schedulerTick state with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              .scheduleTick (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, htick])
              (.scheduleTick reason (by simp [htick]))).1
        | accepted context =>
            exact False.elim ((schedulerTick_ne_accepted state context) (by
              simp [htick]))
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .scheduleTick hstate hmode

end LeanOS.FailStop
