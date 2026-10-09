import LeanOS.FailStop.Faults

/-!
# Fail-stop composite: runtime trace inventory and deferred blocking

The complete runtime operation inventory, and the preservation of the
deferred-cancellation blocking runtime invariant by every ordinary operation
family.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ### Complete runtime operation inventory

The constructors below inventory every operation family whose accepted and
rejected results have complete global-preservation proofs.  The legacy
scheduler-only preemption constructor has been retired in favor of
`resumePreempt`, whose input carries the outgoing frame/register payload needed
to update the authoritative context bank atomically. -/

inductive RuntimeTraceOperation : Operation → Prop where
  | nmi raw context : RuntimeTraceOperation (.nmi raw context)
  | interrupt frame : RuntimeTraceOperation (.interrupt frame)
  | selectUserReturn purpose : RuntimeTraceOperation (.selectUserReturn purpose)
  | userReturn request : RuntimeTraceOperation (.userReturn request)
  | syscall call : RuntimeTraceOperation (.syscall call)
  | ipc call : RuntimeTraceOperation (.ipc call)
  | resumePreempt frame registers :
      RuntimeTraceOperation (.resumePreempt frame registers)
  | transferOffer endpointWord sourceWord sourceKind payload rights :
      RuntimeTraceOperation
        (.transferOffer endpointWord sourceWord sourceKind payload rights)
  | transferAccept endpointWord destinationSlot :
      RuntimeTraceOperation (.transferAccept endpointWord destinationSlot)
  | capabilityCopy source destination destinationSlot rights :
      RuntimeTraceOperation
        (.capabilityCopy source destination destinationSlot rights)
  | capabilityRevoke authoritySlot victim victimSlot :
      RuntimeTraceOperation (.capabilityRevoke authoritySlot victim victimSlot)
  | capabilityRevokeSubtree authoritySlot victim victimSlot :
      RuntimeTraceOperation (.capabilityRevokeSubtree authoritySlot victim victimSlot)
  | map slot page permissions : RuntimeTraceOperation (.map slot page permissions)
  | unmap page : RuntimeTraceOperation (.unmap page)
  | protect page permissions : RuntimeTraceOperation (.protect page permissions)
  | createSubject subject : RuntimeTraceOperation (.createSubject subject)
  | terminateSubject subject : RuntimeTraceOperation (.terminateSubject subject)
  | scheduleAdd subject : RuntimeTraceOperation (.scheduleAdd subject)
  | scheduleRemove subject : RuntimeTraceOperation (.scheduleRemove subject)
  | scheduleNext : RuntimeTraceOperation .scheduleNext
  | scheduleYield : RuntimeTraceOperation .scheduleYield
  | scheduleTick : RuntimeTraceOperation .scheduleTick
  | terminateCurrent : RuntimeTraceOperation .terminateCurrent
  | restart : RuntimeTraceOperation .restart

/-- Every operation admitted to the registered mixed-trace surface has a
complete one-step preservation proof for all of its typed results. -/
theorem runtimeTraceOperation_preserves_runtimeWellFormed operation
    (hoperation : RuntimeTraceOperation operation) :
    OperationPreservesRuntimeWellFormed operation := by
  cases hoperation with
  | nmi raw context =>
      intro state hstate
      cases hmode : state.execution.mode <;>
        simpa [gate, hmode, applyOperation] using
          applyNmi_preserves_runtimeWellFormed state raw context hstate
  | interrupt frame => exact interrupt_operationPreservesRuntimeWellFormed frame
  | selectUserReturn purpose =>
      exact selectUserReturn_operationPreservesRuntimeWellFormed purpose
  | userReturn request =>
      exact userReturn_operationPreservesRuntimeWellFormed request
  | syscall call => exact syscall_operationPreservesRuntimeWellFormed call
  | ipc call => exact ipc_operationPreservesRuntimeWellFormed call
  | resumePreempt frame registers =>
      exact resumePreempt_operationPreservesRuntimeWellFormed frame registers
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact transferOffer_operationPreservesRuntimeWellFormed endpointWord sourceWord
        sourceKind payload rights
  | transferAccept endpointWord destinationSlot =>
      exact transferAccept_operationPreservesRuntimeWellFormed endpointWord destinationSlot
  | capabilityCopy source destination destinationSlot rights =>
      exact capabilityCopy_operationPreservesRuntimeWellFormed
        source destination destinationSlot rights
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact capabilityRevoke_operationPreservesRuntimeWellFormed
        authoritySlot victim victimSlot
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact capabilityRevokeSubtree_operationPreservesRuntimeWellFormed
        authoritySlot victim victimSlot
  | map slot page permissions =>
      exact map_operationPreservesRuntimeWellFormed slot page permissions
  | unmap page => exact unmap_operationPreservesRuntimeWellFormed page
  | protect page permissions =>
      exact protect_operationPreservesRuntimeWellFormed page permissions
  | createSubject subject => exact createSubject_operationPreservesRuntimeWellFormed subject
  | terminateSubject subject =>
      exact terminateSubject_operationPreservesRuntimeWellFormed subject
  | scheduleAdd subject => exact scheduleAdd_operationPreservesRuntimeWellFormed subject
  | scheduleRemove subject => exact scheduleRemove_operationPreservesRuntimeWellFormed subject
  | scheduleNext => exact scheduleNext_operationPreservesRuntimeWellFormed
  | scheduleYield => exact scheduleYield_operationPreservesRuntimeWellFormed
  | scheduleTick => exact scheduleTick_operationPreservesRuntimeWellFormed
  | terminateCurrent => exact terminateCurrent_operationPreservesRuntimeWellFormed
  | restart => exact restart_operationPreservesRuntimeWellFormed

/-- The preservation inventory is complete: every public `Operation`
constructor is represented by `RuntimeTraceOperation`.  This exhaustiveness
lemma prevents a newly added operation from silently escaping the universal
gate theorem below. -/
theorem runtimeTraceOperation_complete operation :
    RuntimeTraceOperation operation := by
  cases operation with
  | nmi raw context => exact .nmi raw context
  | interrupt frame => exact .interrupt frame
  | selectUserReturn purpose => exact .selectUserReturn purpose
  | userReturn request => exact .userReturn request
  | syscall call => exact .syscall call
  | ipc call => exact .ipc call
  | resumePreempt frame registers => exact .resumePreempt frame registers
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact .transferOffer endpointWord sourceWord sourceKind payload rights
  | transferAccept endpointWord destinationSlot =>
      exact .transferAccept endpointWord destinationSlot
  | capabilityCopy source destination destinationSlot rights =>
      exact .capabilityCopy source destination destinationSlot rights
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact .capabilityRevoke authoritySlot victim victimSlot
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact .capabilityRevokeSubtree authoritySlot victim victimSlot
  | map slot page permissions => exact .map slot page permissions
  | unmap page => exact .unmap page
  | protect page permissions => exact .protect page permissions
  | createSubject subject => exact .createSubject subject
  | terminateSubject subject => exact .terminateSubject subject
  | scheduleAdd subject => exact .scheduleAdd subject
  | scheduleRemove subject => exact .scheduleRemove subject
  | scheduleNext => exact .scheduleNext
  | scheduleYield => exact .scheduleYield
  | scheduleTick => exact .scheduleTick
  | terminateCurrent => exact .terminateCurrent
  | restart => exact .restart

/-- Every public operation preserves the global runtime invariant for every
typed result.  There is no registration premise and no excluded constructor. -/
theorem operation_preserves_runtimeWellFormed operation :
    OperationPreservesRuntimeWellFormed operation :=
  runtimeTraceOperation_preserves_runtimeWellFormed operation
    (runtimeTraceOperation_complete operation)

/-- The total composite gate preserves `RuntimeWellFormed` for an arbitrary
public operation, including attacker-controlled words and terminal modes. -/
theorem gate_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state operation).state :=
  operation_preserves_runtimeWellFormed operation state hstate

/-- Arbitrary finite interleavings of all currently registered runtime
families preserve the global invariant.  Calls and handles remain arbitrary,
so each family contributes both its accepted and typed-rejection paths; halted
suffixes are covered by the same theorem because the outer gate is absorbing. -/
theorem runRuntimeTrace_preserves_runtimeWellFormed state operations
    (hstate : RuntimeWellFormed state)
    (hoperations : ∀ operation, operation ∈ operations →
      RuntimeTraceOperation operation) :
    RuntimeWellFormed (runOperations state operations) := by
  apply runOperations_preserves_runtimeWellFormed state operations hstate
  intro operation hmember
  exact runtimeTraceOperation_preserves_runtimeWellFormed operation
    (hoperations operation hmember)

/-- Arbitrary finite operation sequences preserve the global invariant.  This
is the universal composite-gate preservation boundary: unlike the registered
trace lemma, it has no per-member side condition. -/
theorem runOperations_preserves_runtimeWellFormed_universally state operations
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (runOperations state operations) := by
  apply runOperations_preserves_runtimeWellFormed state operations hstate
  intro operation _hmember
  exact operation_preserves_runtimeWellFormed operation

/-- Removing a subject through the blocking dependency keeps its waiter index
and exact saved-context bank synchronized.  This projection law intentionally
does not require the scheduler-side blocking invariant. -/
theorem blockingIPCContext_terminate_preserves_contextAgreement
    (state : BlockingIPCContext.State) (subject : BlockingIPCContext.SubjectId)
    (hstate : BlockingIPCContext.ContextAgreement state) :
    BlockingIPCContext.ContextAgreement (BlockingIPCContext.terminate state subject) := by
  rcases hstate with ⟨hagreement, hvalid⟩
  unfold BlockingIPCContext.terminate
  split
  · exact ⟨hagreement, hvalid⟩
  next haccepted =>
    constructor
    · intro candidate
      by_cases heq : candidate = subject
      · subst candidate
        obtain ⟨hwaiter, hblocked⟩ :=
          BlockingIPCContext.terminate_accepted_cleans_self state subject haccepted
        have hblockedSome := congrArg Option.isSome hblocked
        have hwaiterSome := congrArg Option.isSome hwaiter
        simpa only [BlockingIPCContext.terminate, haccepted] using
          hblockedSome.trans hwaiterSome.symm
      · have hblocked : (BlockingIPCContext.terminate state subject).blocked candidate =
            state.blocked candidate := by
          simp [BlockingIPCContext.terminate, haccepted,
            BlockingIPCContext.setBlocked, heq]
        have hwaiter :
            (BlockingIPCContext.terminate state subject).ipc.waiterEndpoint candidate =
              state.ipc.waiterEndpoint candidate := by
          simp only [BlockingIPCContext.terminate, haccepted, BlockingIPC.terminate,
            BlockingIPC.cancelSubject]
          cases hindex : state.ipc.waiterEndpoint subject with
          | none => rfl
          | some endpoint =>
              simp only [hindex]
              split <;> simp [BlockingIPC.setWaiterEndpoint, heq]
        have hblockedSome := congrArg Option.isSome hblocked
        have hwaiterSome := congrArg Option.isSome hwaiter
        simpa only [BlockingIPCContext.terminate, haccepted] using
          hblockedSome.trans ((hagreement candidate).trans hwaiterSome.symm)
    · intro candidate saved hsaved
      by_cases heq : candidate = subject
      · subst candidate
        simp [BlockingIPCContext.setBlocked] at hsaved
      · apply hvalid candidate saved
        simpa [BlockingIPCContext.setBlocked, heq] using hsaved

private theorem publishInterruptCleanup_preserves_contextAgreement state subject
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    BlockingIPCContext.ContextAgreement
      (publishInterruptCleanup state subject).blockingIPCContext := by
  have hterminated := blockingIPCContext_terminate_preserves_contextAgreement
    state.blockingIPCContext subject hstate
  have hdetached := BlockingIPCContext.detachInvalidated_preserves_contextAgreement
    (BlockingIPCContext.terminate state.blockingIPCContext subject)
    state.deferredCancels
    (ResumablePreemption.cleanupSubject state.resumable subject).scheduler
    hterminated
  simpa [BlockingIPCContext.ContextAgreement, publishInterruptCleanup,
    CompositeState.blockingIPCContext] using hdetached

/-- Contained cleanup preserves exact waiter/saved-context agreement while
invalidated peers move into the disjoint deferred-cancel bank. -/
theorem interrupt_contained_preserves_contextAgreement state frame subject
    (hcurrent : state.lifecycle.current = some subject)
    (hcontained : (dispatchHardware state.execution frame).action = .contained subject)
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    BlockingIPCContext.ContextAgreement
      (applyOperation state (.interrupt frame)).blockingIPCContext := by
  simpa [applyOperation, hcontained, hcurrent] using
    publishInterruptCleanup_preserves_contextAgreement state subject hstate

/-- Readiness for a contained fault binds the trusted execution identity to
the authoritative lifecycle selection.  `CompositeState.Coherent` supplies
the forward implication from a selected lifecycle subject, but intentionally
does not claim that an arbitrary running execution context is selected.  This
small reverse equality is therefore required exactly at contained entry. -/
def ContainedFaultIdentityBound (state : CompositeState) : Prop :=
  state.lifecycle.current = some state.execution.core.context.currentSubject

/-- A contained result always names the trusted execution identity; combined
with the contained-entry binding, it therefore names `lifecycle.current`. -/
private theorem interrupt_contained_faulting_identity core frame faulting
    (hcontained :
      (Interrupt.dispatchHardware core frame).action = .contained faulting) :
    core.context.currentSubject = faulting := by
  unfold Interrupt.dispatchHardware at hcontained
  split at hcontained <;> try simp_all
  cases hvector : Interrupt.decodeVector frame.vector with
  | none => simp [hvector] at hcontained
  | some vector =>
      cases vector with
      | pageFault => cases horigin : frame.savedPrivilege <;> simp_all
      | timer => simp [hvector] at hcontained
      | syscall => cases horigin : frame.savedPrivilege <;> simp_all

theorem contained_faulting_identity_is_current state frame faulting
    (hbound : ContainedFaultIdentityBound state)
    (hcontained : (dispatchHardware state.execution frame).action = .contained faulting) :
    state.lifecycle.current = some faulting := by
  have hid : state.execution.core.context.currentSubject = faulting := by
    cases hmode : state.execution.mode with
    | handling active => simp [dispatchHardware, hmode, halt] at hcontained
    | halted record => simp [dispatchHardware, hmode] at hcontained
    | running =>
        simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hcontained
        generalize hd : Interrupt.dispatchHardware
          { state.execution.core with context :=
            { state.execution.core.context with entryActive := false } }
          frame = outcome at hcontained
        cases outcome with
        | mk next action =>
            cases action with
            | contained actual =>
                have hrawAction :
                    (Interrupt.dispatchHardware
                      { state.execution.core with context :=
                        { state.execution.core.context with entryActive := false } }
                      frame).action = .contained actual := by
                  rw [hd]
                have hraw := interrupt_contained_faulting_identity
                  { state.execution.core with context :=
                    { state.execution.core.context with entryActive := false } }
                  frame actual hrawAction
                have hactual : actual = faulting := by
                  simpa [activeEntry, hd] using hcontained
                simpa [hactual] using hraw
            | fatal reason => simp [activeEntry, hd, halt] at hcontained
            | timer => simp [activeEntry, hd] at hcontained
            | syscall => simp [activeEntry, hd] at hcontained
            | rejected reason => simp [activeEntry, hd] at hcontained
  simpa [ContainedFaultIdentityBound, hid] using hbound

/-- Source normalization preserves the complete deferred invariant.  The only
nontrivial branch removes one exact waiter/index/context triple; every peer
waiter, retained cancellation, and resumable-disjointness fact is inherited
pointwise. -/
private theorem detachTerminationSource_preserves_deferredBlockingRuntimeWellFormed
    state subject (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed (detachTerminationSource state subject) := by
  constructor
  · cases hendpoint : state.blockingIPC.waiterEndpoint subject
    · simpa [detachTerminationSource, hendpoint, RuntimeWellFormed,
        CompositeState.Coherent, CompositeState.ReturnPlanLive,
        CompositeState.BlockingIPCCoherent] using hstate.1
    · simpa [detachTerminationSource, hendpoint, RuntimeWellFormed,
        CompositeState.Coherent, CompositeState.ReturnPlanLive,
        CompositeState.BlockingIPCCoherent] using hstate.1
  · rcases hstate.2 with
      ⟨⟨⟨hipc, hagreement⟩, hblockedDeferred, hretained⟩,
        hblockedResumable, hretainedResumable⟩
    simp only [CompositeState.blockingIPCContext] at hipc hagreement
    simp only [CompositeState.blockingIPCContext] at hblockedDeferred hretained
    cases hendpoint : state.blockingIPC.waiterEndpoint subject with
    | none =>
        have hdetached :
            detachTerminationSource state subject =
              { state with deferredCancels :=
                  BlockingIPCContext.setRetained state.deferredCancels subject none } := by
          simp [detachTerminationSource, hendpoint]
        rw [hdetached]
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
        · simpa [detachTerminationSource, hendpoint,
            CompositeState.blockingIPCContext] using hipc
        · simpa [detachTerminationSource, hendpoint,
            CompositeState.blockingIPCContext] using hagreement
        · intro candidate hblocked
          change (state.blockingContexts candidate).isSome = true at hblocked
          change
            (BlockingIPCContext.setRetained state.deferredCancels subject none).retained
              candidate = none
          by_cases heq : candidate = subject
          · subst candidate
            simp [BlockingIPCContext.setRetained]
          · simpa [BlockingIPCContext.setRetained, heq] using
                hblockedDeferred candidate hblocked
        · intro candidate saved hsaved
          change
            (BlockingIPCContext.setRetained state.deferredCancels subject none).retained
              candidate = some saved at hsaved
          have hne : candidate ≠ subject := by
            intro heq
            subst candidate
            simp [BlockingIPCContext.setRetained] at hsaved
          exact hretained candidate saved (by
            simpa [BlockingIPCContext.setRetained, hne] using hsaved)
        · intro candidate saved hblocked
          change state.blockingContexts candidate = some saved at hblocked
          change
            ResumablePreemption.contextFor state.resumable.contexts candidate = none
          exact hblockedResumable candidate saved hblocked
        · intro candidate saved hsaved
          change
            (BlockingIPCContext.setRetained state.deferredCancels subject none).retained
              candidate = some saved at hsaved
          change
            ResumablePreemption.contextFor state.resumable.contexts candidate = none
          have hne : candidate ≠ subject := by
            intro heq
            subst candidate
            simp [BlockingIPCContext.setRetained] at hsaved
          exact hretainedResumable candidate saved (by
            simpa [BlockingIPCContext.setRetained, hne] using hsaved)
    | some endpoint =>
        let nextIPC : BlockingIPC.State :=
          { state.blockingIPC with
            waiters := BlockingIPC.removeWaiter state.blockingIPC.waiters subject
            waiterEndpoint :=
              BlockingIPC.setWaiterEndpoint state.blockingIPC.waiterEndpoint subject none
            completion :=
              BlockingIPC.setCompletion state.blockingIPC.completion subject
                (some .cancelled) }
        have hdetached :
            detachTerminationSource state subject =
              { state with
                blockingIPC := nextIPC
                blockingContexts :=
                  BlockingIPCContext.setBlocked state.blockingContexts subject none
                deferredCancels :=
                  BlockingIPCContext.setRetained state.deferredCancels subject none } := by
          simp [detachTerminationSource, hendpoint, nextIPC]
        rw [hdetached]
        rcases hipc with
          ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcapability⟩
        have hnewIPC : BlockingIPC.WellFormed
            nextIPC := by
          dsimp [nextIPC]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [detachTerminationSource, hendpoint] using hscheduler
          · intro candidate
            constructor
            · change
                (state.blockingIPC.waiters candidate).filter
                    (· ≠ subject) |>.Nodup
              exact (hqueues candidate).1.filter _
            · change
                ((state.blockingIPC.waiters candidate).filter
                    (· ≠ subject)).length ≤ state.blockingIPC.waiterCapacity
              exact Nat.le_trans
                (List.length_filter_le (· ≠ subject)
                  (state.blockingIPC.waiters candidate))
                (by simpa [detachTerminationSource, hendpoint] using
                  (hqueues candidate).2)
          · intro candidate waiter hmember
            have holdMember : waiter ∈ state.blockingIPC.waiters candidate := by
              change
                waiter ∈ (state.blockingIPC.waiters candidate).filter
                  (· ≠ subject) at hmember
              exact (List.mem_filter.mp hmember).1
            rcases hwaiters candidate waiter holdMember with
              ⟨hlive, hauthority, hsubjectLive, hrunnable, howns,
                hnotCurrent, hnotReady⟩
            simpa [BlockingIPC.authorizedReceive] using
              And.intro hlive (And.intro hauthority
                (And.intro hsubjectLive (And.intro hrunnable
                  (And.intro howns (And.intro hnotCurrent hnotReady)))))
          · intro first second waiter hfirst hsecond
            change
              waiter ∈ (state.blockingIPC.waiters first).filter
                (· ≠ subject) at hfirst
            change
              waiter ∈ (state.blockingIPC.waiters second).filter
                (· ≠ subject) at hsecond
            exact hunique first second waiter
              (List.mem_filter.mp hfirst).1
              (List.mem_filter.mp hsecond).1
          · intro candidate waiter
            by_cases heq : waiter = subject
            · subst waiter
              simp [detachTerminationSource, hendpoint,
                BlockingIPC.removeWaiter, BlockingIPC.setWaiterEndpoint]
            · simpa [detachTerminationSource, hendpoint,
                BlockingIPC.removeWaiter, BlockingIPC.setWaiterEndpoint, heq] using
                  hindex candidate waiter
          · intro candidate envelope hmail
            have hold := hmailbox candidate envelope (by
              change state.blockingIPC.mailbox candidate = some envelope at hmail
              exact hmail)
            rcases hold with ⟨hlive, hkind, henvelope, hempty⟩
            refine ⟨?_, ?_, henvelope, ?_⟩
            · simpa [detachTerminationSource, hendpoint] using hlive
            · simpa [detachTerminationSource, hendpoint] using hkind
            · change
                (state.blockingIPC.waiters candidate).filter
                    (· ≠ subject) = []
              simp [hempty]
          · simpa [detachTerminationSource, hendpoint] using hcapability
        have hnewAgreement : BlockingIPCContext.ContextAgreement
            { ipc := nextIPC
              blocked :=
                BlockingIPCContext.setBlocked state.blockingContexts subject none } := by
          dsimp [nextIPC]
          constructor
          · intro candidate
            by_cases heq : candidate = subject
            · subst candidate
              simp [detachTerminationSource, hendpoint,
                CompositeState.blockingIPCContext,
                BlockingIPC.setWaiterEndpoint, BlockingIPCContext.setBlocked]
            · simpa [detachTerminationSource, hendpoint,
                CompositeState.blockingIPCContext,
                BlockingIPC.setWaiterEndpoint, BlockingIPCContext.setBlocked, heq] using
                  hagreement.1 candidate
          · intro candidate saved hsaved
            have hne : candidate ≠ subject := by
              intro heq
              subst candidate
              simp [detachTerminationSource, hendpoint,
                CompositeState.blockingIPCContext,
                BlockingIPCContext.setBlocked] at hsaved
            exact hagreement.2 candidate saved (by
              simpa [detachTerminationSource, hendpoint,
                CompositeState.blockingIPCContext,
                BlockingIPCContext.setBlocked, hne] using hsaved)
        refine ⟨⟨⟨hnewIPC, hnewAgreement⟩, ?_, ?_⟩, ?_, ?_⟩
        · intro candidate hblocked
          by_cases heq : candidate = subject
          · subst candidate
            simp [detachTerminationSource, hendpoint,
              CompositeState.blockingIPCContext,
              BlockingIPCContext.setBlocked] at hblocked
          · simpa [detachTerminationSource, hendpoint,
              CompositeState.blockingIPCContext,
              BlockingIPCContext.setBlocked,
              BlockingIPCContext.setRetained, heq] using
                hblockedDeferred candidate (by
                  simpa [detachTerminationSource, hendpoint,
                    CompositeState.blockingIPCContext,
                    BlockingIPCContext.setBlocked, heq] using hblocked)
        · intro candidate saved hsaved
          have hne : candidate ≠ subject := by
            intro heq
            subst candidate
            simp [detachTerminationSource, hendpoint,
              BlockingIPCContext.setRetained] at hsaved
          simpa [nextIPC,
              CompositeState.blockingIPCContext,
              BlockingIPC.setWaiterEndpoint, hne] using
            hretained candidate saved (by
              simpa [detachTerminationSource, hendpoint,
                BlockingIPCContext.setRetained, hne] using hsaved)
        · intro candidate saved hblocked
          change
            (BlockingIPCContext.setBlocked state.blockingContexts subject none)
                candidate = some saved at hblocked
          change
            ResumablePreemption.contextFor state.resumable.contexts candidate = none
          have hne : candidate ≠ subject := by
            intro heq
            subst candidate
            simp [BlockingIPCContext.setBlocked] at hblocked
          exact hblockedResumable candidate saved (by
            simpa [BlockingIPCContext.setBlocked, hne] using hblocked)
        · intro candidate saved hsaved
          change
            (BlockingIPCContext.setRetained state.deferredCancels subject none).retained
                candidate = some saved at hsaved
          change
            ResumablePreemption.contextFor state.resumable.contexts candidate = none
          have hne : candidate ≠ subject := by
            intro heq
            subst candidate
            simp [BlockingIPCContext.setRetained] at hsaved
          exact hretainedResumable candidate saved (by
            simpa [BlockingIPCContext.setRetained, hne] using hsaved)

set_option maxHeartbeats 100000 in
/-- The shared current-subject cleanup publisher establishes the complete
deferred-cancellation post-state.  Current selection rules out the only
otherwise possible collision: a quiescent retained identity cannot
simultaneously be the subject retired by cleanup. -/
private theorem publishTerminationDetachment_preserves_deferredBlockingRuntimeWellFormed
    state faulting
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hliveFaulting :
      state.blockingIPC.scheduler.lifecycle.capabilities.subjects faulting = true)
    (hissuedFaulting :
      state.blockingIPC.scheduler.lifecycle.issuedSubjects faulting = true)
    (hwaiterSelf : state.blockingIPC.waiterEndpoint faulting = none)
    (hdeferredSelf : state.deferredCancels.retained faulting = none)
    (hmode : state.execution.mode = .running) :
    DeferredBlockingRuntimeWellFormed
      (publishInterruptCleanup state faulting) := by
  constructor
  · exact publishInterruptCleanup_preserves_runtimeWellFormed
      state faulting hstate.1 hmode
  ·
    rcases hstate.2 with
      ⟨⟨⟨hipcWellFormed, hcontextAgreement⟩, hblockedDisjoint,
        hretainedWellFormed⟩, hblockedResumableDisjoint,
        hresumableDisjoint⟩
    rcases hstate.1 with
      ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
        hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive,
        hblocking, hports⟩
    have hresumableScheduler : state.resumable.scheduler = state.scheduler :=
      hcoherent.2.2.2.2.2.2.2.1
    have hblockingScheduler : state.blockingIPC.scheduler = state.scheduler :=
      hblocking.1
    have hblockingLifecycle :
        state.blockingIPC.scheduler.lifecycle = state.lifecycle :=
      hblocking.2
    have hresumableBlocking :
        state.resumable.scheduler = state.blockingIPC.scheduler :=
      hresumableScheduler.trans hblockingScheduler.symm
    have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
      state.resumable faulting hresumable
    have hterminate :
        (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle faulting).result =
          .accepted := by
      simp [SubjectLifecycle.terminate, hliveFaulting, hissuedFaulting]
    have hterminatedBlocking :
        BlockingIPC.terminate state.blockingIPC faulting =
          { state.blockingIPC with
            scheduler := { state.blockingIPC.scheduler with
              lifecycle := SubjectLifecycle.terminateState
                state.blockingIPC.scheduler.lifecycle faulting
              ready := state.blockingIPC.scheduler.ready.filter (· ≠ faulting) } } := by
      simp [BlockingIPC.terminate, SubjectLifecycle.terminate, hliveFaulting,
        hissuedFaulting, BlockingIPC.cancelSubject, hwaiterSelf]
    have hpostWaiters (endpoint : BlockingIPC.ObjectId) :
        (publishInterruptCleanup state faulting).blockingIPC.waiters endpoint =
          (state.blockingIPC.waiters endpoint).filter
            (fun _ =>
              (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                endpoint) := by
      simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
        BlockingIPCContext.detachInvalidated,
        BlockingIPCContext.terminate, hterminate, hterminatedBlocking]
    have hpostWaiterCapacity :
        (publishInterruptCleanup state faulting).blockingIPC.waiterCapacity =
          state.blockingIPC.waiterCapacity := by
      simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
        BlockingIPCContext.detachInvalidated,
        BlockingIPCContext.terminate, hterminate, hterminatedBlocking]
    have cleanup_preserves_quiescent (subject : BlockingIPC.SubjectId)
        (hsubjectNe : subject ≠ faulting)
        (hsubjectLive :
          state.blockingIPC.scheduler.lifecycle.capabilities.subjects subject = true)
        (hsubjectRunnable :
          state.blockingIPC.scheduler.lifecycle.runnable subject = false)
        (hsubjectNotCurrent :
          state.blockingIPC.scheduler.lifecycle.current ≠ some subject)
        (hsubjectNotReady : subject ∉ state.blockingIPC.scheduler.ready)
        (hsubjectOwns :
          Scheduler.ownsAddressSpace state.blockingIPC.scheduler subject = some subject) :
        let scheduler :=
          (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler
        scheduler.lifecycle.capabilities.subjects subject = true ∧
          scheduler.lifecycle.runnable subject = false ∧
          scheduler.lifecycle.current ≠ some subject ∧
          subject ∉ scheduler.ready ∧
          Scheduler.ownsAddressSpace scheduler subject = some subject := by
      dsimp only
      have howns :
          state.blockingIPC.scheduler.lifecycle.addressOwner subject = some subject := by
        unfold Scheduler.ownsAddressSpace at hsubjectOwns
        split at hsubjectOwns
        · assumption
        · contradiction
      have hownsNe :
          state.blockingIPC.scheduler.lifecycle.addressOwner subject ≠ some faulting := by
        rw [howns]
        simp [hsubjectNe]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [ResumablePreemption.cleanupSubject,
          ResumablePreemption.retireOwnedAddressSpaces,
          SubjectLifecycle.terminateState,
          SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool,
          hresumableBlocking, hsubjectNe] using hsubjectLive
      · simpa [ResumablePreemption.cleanupSubject,
          SubjectLifecycle.terminateState, SubjectLifecycle.setBool,
          hresumableBlocking, hsubjectNe] using hsubjectRunnable
      · simp [ResumablePreemption.cleanupSubject,
          SubjectLifecycle.terminateState, hresumableBlocking,
          hsubjectNotCurrent]
      · intro hready
        have hready' : subject ∈ state.blockingIPC.scheduler.ready.filter
            (· != faulting) := by
          simpa [ResumablePreemption.cleanupSubject, hresumableBlocking] using hready
        exact hsubjectNotReady (List.mem_filter.mp hready').1
      · simp [Scheduler.ownsAddressSpace, ResumablePreemption.cleanupSubject,
          SubjectLifecycle.terminateState, hresumableBlocking, hownsNe, howns]
        exact hsubjectNe
    have cleanup_context_absent (subject : BlockingIPC.SubjectId)
        (habsent : ResumablePreemption.contextFor state.resumable.contexts subject = none) :
        ResumablePreemption.contextFor
            (ResumablePreemption.cleanupSubject state.resumable faulting).contexts subject = none := by
      by_cases hsubject : subject = faulting
      · subst subject
        exact ResumablePreemption.cleanup_removes_context state.resumable faulting
      · simpa [ResumablePreemption.cleanupSubject] using
          (ResumablePreemption.contextFor_erase_other
            state.resumable.contexts faulting subject hsubject).trans habsent
    clear hstate hcoherent hblocking hresumable hexecution hcapabilities hvirtual
      hipc hscheduler hpreemption htransfers hhalted hlive hports hlifecycle
    unfold CompositeState.DeferredCancellationWellFormed
    constructor
    · unfold BlockingIPCContext.DeferredWellFormed
      constructor
      · constructor
        · rcases hipcWellFormed with
            ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, hcapability⟩
          simp only [CompositeState.blockingIPCContext] at hqueues hwaiters hunique
          simp only [CompositeState.blockingIPCContext] at hindex hmailbox hcapability
          refine ⟨hcleanup.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro endpoint
            rw [show
              (publishInterruptCleanup state faulting).blockingIPCContext.ipc.waiters endpoint =
                (publishInterruptCleanup state faulting).blockingIPC.waiters endpoint by rfl,
              hpostWaiters, show
              (publishInterruptCleanup state faulting).blockingIPCContext.ipc.waiterCapacity =
                (publishInterruptCleanup state faulting).blockingIPC.waiterCapacity by rfl,
              hpostWaiterCapacity]
            refine ⟨?_, ?_⟩
            · exact (hqueues endpoint).1.filter _
            · exact Nat.le_trans (List.length_filter_le _ _) (hqueues endpoint).2
          · intro endpoint subject hmember
            have hkeep :
                (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                  endpoint = true := by
              cases hvalue :
                  (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                    endpoint with
              | false =>
                  simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                    hterminate, hterminatedBlocking, hvalue] at hmember
              | true => rfl
            have holdMember : subject ∈ state.blockingIPC.waiters endpoint := by
              simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, hkeep] using hmember
            rcases hwaiters endpoint subject holdMember with
              ⟨holdLive, holdAuthority, holdSubjectLive, holdRunnable,
                holdOwns, holdNotCurrent, holdNotReady⟩
            have hsubjectNe : subject ≠ faulting := by
              intro heq
              subst subject
              have hindexed := (hindex endpoint faulting).mp holdMember
              change state.blockingIPC.waiterEndpoint faulting = some endpoint at hindexed
              rw [hwaiterSelf] at hindexed
              simp at hindexed
            refine ⟨hkeep, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rcases holdAuthority with
                ⟨slot, capability, hslot, hobject, hkind, hrights, _⟩
              refine ⟨slot, capability, ?_, hobject, hkind, hrights, hkeep⟩
              have hkeepFacts := hkeep
              simp [ResumablePreemption.cleanupSubject,
                ResumablePreemption.retireOwnedAddressSpaces,
                SubjectLifecycle.terminateState,
                SubjectLifecycle.terminatedCapabilities, hresumableBlocking,
                hobject] at hkeepFacts
              rcases hkeepFacts with ⟨haddress, ⟨hmemory, hendpoint⟩, _⟩
              simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, ResumablePreemption.cleanupSubject,
                ResumablePreemption.retireOwnedAddressSpaces,
                SubjectLifecycle.terminateState,
                SubjectLifecycle.terminatedCapabilities, hresumableBlocking,
                hslot, hobject, hsubjectNe, haddress, hmemory, hendpoint]
            · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, ResumablePreemption.cleanupSubject,
                ResumablePreemption.retireOwnedAddressSpaces,
                SubjectLifecycle.terminateState,
                SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool,
                hresumableBlocking, hsubjectNe] using holdSubjectLive
            · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, ResumablePreemption.cleanupSubject,
                SubjectLifecycle.terminateState, SubjectLifecycle.setBool,
                hresumableBlocking, hsubjectNe] using holdRunnable
            · have howns :
                  state.blockingIPC.scheduler.lifecycle.addressOwner subject = some subject := by
                unfold Scheduler.ownsAddressSpace at holdOwns
                split at holdOwns
                · assumption
                · contradiction
              have hownsNe :
                  state.blockingIPC.scheduler.lifecycle.addressOwner subject ≠ some faulting := by
                rw [howns]
                simp [hsubjectNe]
              simp [Scheduler.ownsAddressSpace, publishInterruptCleanup,
                CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, ResumablePreemption.cleanupSubject,
                SubjectLifecycle.terminateState, hresumableBlocking,
                hownsNe, howns]
              exact hsubjectNe
            · simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, ResumablePreemption.cleanupSubject,
                SubjectLifecycle.terminateState, hresumableBlocking,
                holdNotCurrent]
            · intro hready
              apply holdNotReady
              have hready' : subject ∈ state.blockingIPC.scheduler.ready.filter
                  (· != faulting) := by
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, ResumablePreemption.cleanupSubject,
                hresumableBlocking] using hready
              exact (List.mem_filter.mp hready').1
          · intro first second subject hfirst hsecond
            apply hunique first second subject
            · have hold := hfirst
              simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking] at hold
              exact hold.1
            · have hold := hsecond
              simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking] at hold
              exact hold.1
          · intro endpoint subject
            simp only [publishInterruptCleanup, CompositeState.blockingIPCContext,
              BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
              hterminate, hterminatedBlocking, List.mem_filter]
            constructor
            · rintro ⟨hmember, hkeep⟩
              have hindexed := (hindex endpoint subject).mp hmember
              simp [hindexed, hkeep]
            · intro hindexed
              cases hold : state.blockingIPC.waiterEndpoint subject with
              | none => simp [hold] at hindexed
              | some actual =>
                  by_cases hlive :
                      (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                        actual = true
                  · simp [hold, hlive] at hindexed
                    subst actual
                    exact ⟨(hindex endpoint subject).mpr hold, hlive⟩
                  · simp [hold, hlive] at hindexed
          · intro endpoint envelope hmail
            by_cases hkeep :
                (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                  endpoint = true
            · have holdMail : state.blockingIPC.mailbox endpoint = some envelope := by
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  hterminate, hterminatedBlocking, hkeep] using hmail
              rcases hmailbox endpoint envelope holdMail with ⟨_, hkind, hend, hempty⟩
              refine ⟨hkeep, ?_, hend, ?_⟩
              · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                    hterminate, hterminatedBlocking] using
                  ResumablePreemption.cleanup_live_object_preserves_kind
                    state.resumable faulting endpoint .endpoint hkeep
                    (by simpa [hresumableBlocking] using hkind)
              · simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  hterminate, hterminatedBlocking, hkeep, hempty]
            · simp [publishInterruptCleanup, CompositeState.blockingIPCContext, hkeep] at hmail
          · have hcleanupVirtual := hcleanup.2.2.2.2.2.2.2.1
            have hcapabilityCleanup : Capability.WellFormed
                (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities := by
              rw [← hcleanupVirtual.1]
              exact hcleanupVirtual.2.2.1
            simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking] using hcapabilityCleanup
        · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext] using
            publishInterruptCleanup_preserves_contextAgreement
              state faulting hcontextAgreement
      · constructor
        · intro subject hblocked
          cases hendpoint : state.blockingIPC.waiterEndpoint subject with
          | none =>
              simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, hendpoint] at hblocked
          | some endpoint =>
              have hsubjectNe : subject ≠ faulting := by
                intro heq
                subst subject
                rw [hwaiterSelf] at hendpoint
                contradiction
              by_cases hkeep :
                  (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                    endpoint = true
              · have holdBlocked : (state.blockingContexts subject).isSome = true := by
                  simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                    BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                    hendpoint, hsubjectNe, hkeep] using hblocked
                have holdNone := hblockedDisjoint subject (by
                  simpa [CompositeState.blockingIPCContext] using holdBlocked)
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                  hendpoint, hsubjectNe, hkeep] using holdNone
              · simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                  hendpoint, hsubjectNe, hkeep] at hblocked
        · intro subject saved hretained
          cases hendpoint : state.blockingIPC.waiterEndpoint subject with
          | none =>
              have holdRetained : state.deferredCancels.retained subject = some saved := by
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  hterminate, hterminatedBlocking, hendpoint] using hretained
              rcases hretainedWellFormed subject saved holdRetained with
                ⟨hvalid, _, hlive, hrunnable, hnotCurrent, hnotReady, howns⟩
              simp only [CompositeState.blockingIPCContext] at hlive hrunnable hnotCurrent
              simp only [CompositeState.blockingIPCContext] at hnotReady howns
              have hsubjectNe : subject ≠ faulting := by
                intro heq
                subst subject
                rw [hdeferredSelf] at holdRetained
                contradiction
              have hquiescent := cleanup_preserves_quiescent subject hsubjectNe
                hlive hrunnable hnotCurrent hnotReady howns
              refine ⟨hvalid, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  hterminate, hterminatedBlocking, hendpoint]
              · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated] using hquiescent.1
              · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated] using hquiescent.2.1
              · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated] using hquiescent.2.2.1
              · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated] using hquiescent.2.2.2.1
              · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated] using hquiescent.2.2.2.2
          | some endpoint =>
              have hsubjectNe : subject ≠ faulting := by
                intro heq
                subst subject
                rw [hwaiterSelf] at hendpoint
                contradiction
              by_cases hkeep :
                  (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                    endpoint = true
              · have hblockedSome : (state.blockingContexts subject).isSome = true := by
                  have hagreement := hcontextAgreement.1 subject
                  simpa [CompositeState.blockingIPCContext, hendpoint] using hagreement
                have hnone := hblockedDisjoint subject (by
                  simpa [CompositeState.blockingIPCContext] using hblockedSome)
                have : state.deferredCancels.retained subject = some saved := by
                  simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                    BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                    hendpoint, hsubjectNe, hkeep] using hretained
                rw [hnone] at this
                contradiction
              · have hblocked : state.blockingContexts subject = some saved := by
                  simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                    BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                    hendpoint, hsubjectNe, hkeep] using hretained
                have hvalid := hcontextAgreement.2 subject saved (by
                  simpa [CompositeState.blockingIPCContext] using hblocked)
                have hmember := (hipcWellFormed.2.2.2.2.1 endpoint subject).mpr (by
                  simpa [CompositeState.blockingIPCContext] using hendpoint)
                rcases hipcWellFormed.2.2.1 endpoint subject hmember with
                  ⟨_, _, hlive, hrunnable, hownsSome, hnotCurrent, hnotReady⟩
                simp only [CompositeState.blockingIPCContext] at hlive hrunnable
                simp only [CompositeState.blockingIPCContext] at hownsSome hnotCurrent
                simp only [CompositeState.blockingIPCContext] at hnotReady
                have howns :
                    Scheduler.ownsAddressSpace state.blockingIPC.scheduler subject =
                      some subject := by
                  unfold Scheduler.ownsAddressSpace at hownsSome
                  split at hownsSome
                  · rename_i haddress
                    simp [Scheduler.ownsAddressSpace, haddress]
                  · contradiction
                have hquiescent := cleanup_preserves_quiescent subject hsubjectNe
                  hlive hrunnable hnotCurrent hnotReady howns
                refine ⟨hvalid, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                    hterminate, hterminatedBlocking, hendpoint, hsubjectNe, hkeep]
                · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated] using hquiescent.1
                · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated] using hquiescent.2.1
                · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated] using hquiescent.2.2.1
                · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated] using hquiescent.2.2.2.1
                · simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                    BlockingIPCContext.detachInvalidated] using hquiescent.2.2.2.2
    · constructor
      · intro subject saved hblocked
        cases hendpoint : state.blockingIPC.waiterEndpoint subject with
        | none =>
            simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
              BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
              hterminate, hterminatedBlocking, hendpoint] at hblocked
        | some endpoint =>
            have hsubjectNe : subject ≠ faulting := by
              intro heq
              subst subject
              rw [hwaiterSelf] at hendpoint
              contradiction
            by_cases hkeep :
                (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                  endpoint = true
            · have holdBlocked : state.blockingContexts subject = some saved := by
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                  hendpoint, hsubjectNe, hkeep] using hblocked
              have holdAbsent := hblockedResumableDisjoint subject saved holdBlocked
              simpa [publishInterruptCleanup, installTerminatedResumable,
                CompositeState.blockingIPCContext] using
                cleanup_context_absent subject holdAbsent
            · simp [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                hendpoint, hsubjectNe, hkeep] at hblocked
      · intro subject saved hretained
        cases hendpoint : state.blockingIPC.waiterEndpoint subject with
        | none =>
            have holdRetained : state.deferredCancels.retained subject = some saved := by
              simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                hterminate, hterminatedBlocking, hendpoint] using hretained
            have holdAbsent := hresumableDisjoint subject saved holdRetained
            simpa [publishInterruptCleanup, installTerminatedResumable,
              CompositeState.blockingIPCContext] using
              cleanup_context_absent subject holdAbsent
        | some endpoint =>
            have hsubjectNe : subject ≠ faulting := by
              intro heq
              subst subject
              rw [hwaiterSelf] at hendpoint
              contradiction
            by_cases hkeep :
                (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
                  endpoint = true
            · have hblockedSome : (state.blockingContexts subject).isSome = true := by
                have hagreement := hcontextAgreement.1 subject
                simpa [CompositeState.blockingIPCContext, hendpoint] using hagreement
              have hnone := hblockedDisjoint subject (by
                simpa [CompositeState.blockingIPCContext] using hblockedSome)
              have holdRetained : state.deferredCancels.retained subject = some saved := by
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                  hendpoint, hsubjectNe, hkeep] using hretained
              rw [hnone] at holdRetained
              contradiction
            · have holdBlocked : state.blockingContexts subject = some saved := by
                simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
                  BlockingIPCContext.detachInvalidated, BlockingIPCContext.terminate,
                  BlockingIPCContext.setBlocked, hterminate, hterminatedBlocking,
                  hendpoint, hsubjectNe, hkeep] using hretained
              have holdAbsent := hblockedResumableDisjoint subject saved holdBlocked
              simpa [publishInterruptCleanup, installTerminatedResumable,
                CompositeState.blockingIPCContext] using
                cleanup_context_absent subject holdAbsent

/-- Accepted termination may target a blocked, deferred, or otherwise
non-current identity.  Detaching that identity first gives the shared cleanup
publisher its source-absence normal form while preserving the complete
deferred invariant. -/
private theorem detachedAcceptedTermination_preserves_deferredBlockingRuntimeWellFormed
    state subject
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (haccepted :
      (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted)
    (hmode : state.execution.mode = .running) :
    DeferredBlockingRuntimeWellFormed
      (publishInterruptCleanup (detachTerminationSource state subject) subject) := by
  have hblockingLifecycle :
      state.blockingIPC.scheduler.lifecycle = state.lifecycle :=
    hstate.1.blockingLifecycle
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hblockingLifecycle]
    exact haccepted
  have hlive :
      state.blockingIPC.scheduler.lifecycle.capabilities.subjects subject = true := by
    cases hlive :
        state.blockingIPC.scheduler.lifecycle.capabilities.subjects subject
    · cases hissued :
          state.blockingIPC.scheduler.lifecycle.issuedSubjects subject <;>
        simp [SubjectLifecycle.terminate, SubjectLifecycle.reject, hlive, hissued]
          at hblockingAccepted
    · rfl
  have hissued :
      state.blockingIPC.scheduler.lifecycle.issuedSubjects subject = true := by
    cases hissued :
        state.blockingIPC.scheduler.lifecycle.issuedSubjects subject <;>
      simp [SubjectLifecycle.terminate, SubjectLifecycle.reject, hissued]
        at hblockingAccepted ⊢
  let detached := detachTerminationSource state subject
  have hdetached :
      DeferredBlockingRuntimeWellFormed detached := by
    exact detachTerminationSource_preserves_deferredBlockingRuntimeWellFormed
      state subject hstate
  have hliveDetached :
      detached.blockingIPC.scheduler.lifecycle.capabilities.subjects subject = true := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simpa [detached, detachTerminationSource, hendpoint] using hlive
  have hissuedDetached :
      detached.blockingIPC.scheduler.lifecycle.issuedSubjects subject = true := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simpa [detached, detachTerminationSource, hendpoint] using hissued
  have hwaiterDetached :
      detached.blockingIPC.waiterEndpoint subject = none := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simp [detached, detachTerminationSource, hendpoint,
        BlockingIPC.setWaiterEndpoint]
  have hdeferredDetached :
      detached.deferredCancels.retained subject = none := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simp [detached, detachTerminationSource, hendpoint,
        BlockingIPCContext.setRetained]
  have hmodeDetached : detached.execution.mode = .running := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simpa [detached, detachTerminationSource, hendpoint] using hmode
  have hpublished :=
    publishTerminationDetachment_preserves_deferredBlockingRuntimeWellFormed
      detached subject hdetached hliveDetached hissuedDetached
      hwaiterDetached hdeferredDetached hmodeDetached
  simpa [detached] using hpublished

/-- Explicit accepted termination publishes the same blocking, retained, and
resumable-context projections as source normalization followed by the shared
cleanup publisher.  The ordinary runtime projection is supplied by the
existing global termination theorem; the exact projection equality carries
the stronger deferred classification without reconstructing it. -/
private theorem installTerminatedSubject_accepted_preserves_deferredBlockingRuntimeWellFormed
    state subject
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (haccepted :
      (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted)
    (hmode : state.execution.mode = .running) :
    DeferredBlockingRuntimeWellFormed
      (installTerminatedSubject state subject
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  have hruntime :=
    gate_terminateSubject_accepted_preserves_runtimeWellFormed
      state subject hstate.1 hmode haccepted
  have hpublished :=
    detachedAcceptedTermination_preserves_deferredBlockingRuntimeWellFormed
      state subject hstate haccepted hmode
  have hblockingLifecycle :
      state.blockingIPC.scheduler.lifecycle = state.lifecycle :=
    hstate.1.blockingLifecycle
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hblockingLifecycle]
    exact haccepted
  have hlive :
      state.blockingIPC.scheduler.lifecycle.capabilities.subjects subject = true := by
    cases hlive :
        state.blockingIPC.scheduler.lifecycle.capabilities.subjects subject
    · cases hissued :
          state.blockingIPC.scheduler.lifecycle.issuedSubjects subject <;>
        simp [SubjectLifecycle.terminate, SubjectLifecycle.reject, hlive, hissued]
          at hblockingAccepted
    · rfl
  have hissued :
      state.blockingIPC.scheduler.lifecycle.issuedSubjects subject = true := by
    cases hissued :
        state.blockingIPC.scheduler.lifecycle.issuedSubjects subject <;>
      simp [SubjectLifecycle.terminate, SubjectLifecycle.reject, hissued]
        at hblockingAccepted ⊢
  have hsetBlocked :
      BlockingIPCContext.setBlocked
          (BlockingIPCContext.setBlocked state.blockingContexts subject none)
          subject none =
        BlockingIPCContext.setBlocked state.blockingContexts subject none := by
    funext candidate
    by_cases heq : candidate = subject <;>
      simp [BlockingIPCContext.setBlocked, heq]
  have hterminatedContext :
      BlockingIPCContext.terminate state.blockingIPCContext subject =
        BlockingIPCContext.terminate
          (detachTerminationSource state subject).blockingIPCContext subject := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simp [detachTerminationSource, CompositeState.blockingIPCContext,
        BlockingIPCContext.terminate, BlockingIPC.terminate,
        SubjectLifecycle.terminate, hlive, hissued, hendpoint,
        BlockingIPC.cancelSubject, SubjectLifecycle.terminated_not_live,
        BlockingIPC.setWaiterEndpoint, BlockingIPC.setCompletion,
        BlockingIPC.removeWaiter, BlockingIPCContext.setBlocked, hsetBlocked]
  have hterminatedWaiter :
      (BlockingIPCContext.terminate state.blockingIPCContext subject).ipc.waiterEndpoint
          subject = none := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simp [CompositeState.blockingIPCContext, BlockingIPCContext.terminate,
        BlockingIPC.terminate, SubjectLifecycle.terminate, hlive, hissued,
        hendpoint, BlockingIPC.cancelSubject, SubjectLifecycle.terminated_not_live,
        BlockingIPC.setWaiterEndpoint]
  have setRetained_detachInvalidated (blocking : BlockingIPCContext.State)
      (deferred : BlockingIPCContext.DeferredCancelState)
      (scheduler : Scheduler.State)
      (hwaiter : blocking.ipc.waiterEndpoint subject = none) :
      BlockingIPCContext.setRetained
          (BlockingIPCContext.detachInvalidated blocking deferred scheduler).2
          subject none =
        (BlockingIPCContext.detachInvalidated blocking
          (BlockingIPCContext.setRetained deferred subject none) scheduler).2 := by
    cases deferred with
    | mk retained =>
        simp only [BlockingIPCContext.setRetained,
          BlockingIPCContext.detachInvalidated]
        apply congrArg BlockingIPCContext.DeferredCancelState.mk
        funext candidate
        by_cases heq : candidate = subject
        · subst candidate
          simp [BlockingIPCContext.setRetained,
            BlockingIPCContext.detachInvalidated, hwaiter]
        · simp [BlockingIPCContext.setRetained,
            BlockingIPCContext.detachInvalidated, heq]
  have detachInvalidated_fst_deferred (blocking : BlockingIPCContext.State)
      (first second : BlockingIPCContext.DeferredCancelState)
      (scheduler : Scheduler.State) :
      (BlockingIPCContext.detachInvalidated blocking first scheduler).1 =
        (BlockingIPCContext.detachInvalidated blocking second scheduler).1 := by
    rfl
  have hdetachedBlocking :
      (BlockingIPCContext.detachInvalidated
          (BlockingIPCContext.terminate state.blockingIPCContext subject)
          state.deferredCancels
          (ResumablePreemption.cleanupSubject state.resumable subject).scheduler).1 =
        (BlockingIPCContext.detachInvalidated
          (BlockingIPCContext.terminate
            (detachTerminationSource state subject).blockingIPCContext subject)
          (detachTerminationSource state subject).deferredCancels
          (ResumablePreemption.cleanupSubject
            (detachTerminationSource state subject).resumable subject).scheduler).1 := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simpa [detachTerminationSource, hendpoint, hterminatedContext] using
        detachInvalidated_fst_deferred
          (BlockingIPCContext.terminate state.blockingIPCContext subject)
          state.deferredCancels
          (BlockingIPCContext.setRetained state.deferredCancels subject none)
          (ResumablePreemption.cleanupSubject state.resumable subject).scheduler
  have hblockingContext :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).blockingIPCContext =
        (publishInterruptCleanup (detachTerminationSource state subject)
          subject).blockingIPCContext := by
    let cleanup := ResumablePreemption.cleanupSubject state.resumable subject
    let publishDetached (detached : BlockingIPCContext.State) :
        BlockingIPCContext.State :=
      { ipc := { detached.ipc with
          mailbox := fun endpoint =>
            if cleanup.scheduler.lifecycle.capabilities.objects endpoint then
              detached.ipc.mailbox endpoint
            else none }
        blocked := detached.blocked }
    have hpublishedBlocking := congrArg publishDetached hdetachedBlocking
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simpa [installTerminatedSubject, publishInterruptCleanup,
        detachTerminationSource, CompositeState.blockingIPCContext,
        cleanup, publishDetached, hendpoint] using hpublishedBlocking
  have hblockingContexts :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).blockingContexts =
        (publishInterruptCleanup (detachTerminationSource state subject)
          subject).blockingContexts := by
    simpa [CompositeState.blockingIPCContext] using
      congrArg BlockingIPCContext.State.blocked hblockingContext
  have hdeferredProjection :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).deferredCancels =
        (publishInterruptCleanup (detachTerminationSource state subject)
          subject).deferredCancels := by
    have hcommute := setRetained_detachInvalidated
      (BlockingIPCContext.terminate state.blockingIPCContext subject)
      state.deferredCancels
      (ResumablePreemption.cleanupSubject state.resumable subject).scheduler
      hterminatedWaiter
    calc
      _ = BlockingIPCContext.setRetained
          (BlockingIPCContext.detachInvalidated
            (BlockingIPCContext.terminate state.blockingIPCContext subject)
            state.deferredCancels
            (ResumablePreemption.cleanupSubject state.resumable subject).scheduler).2
          subject none := rfl
      _ = (BlockingIPCContext.detachInvalidated
            (BlockingIPCContext.terminate state.blockingIPCContext subject)
            (BlockingIPCContext.setRetained state.deferredCancels subject none)
            (ResumablePreemption.cleanupSubject state.resumable subject).scheduler).2 :=
        hcommute
      _ = _ := by
        cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
          simp [publishInterruptCleanup, detachTerminationSource,
            hendpoint, hterminatedContext]
  have hresumableContexts :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).resumable.contexts =
        (publishInterruptCleanup (detachTerminationSource state subject)
          subject).resumable.contexts := by
    cases hendpoint : state.blockingIPC.waiterEndpoint subject <;>
      simp [installTerminatedSubject, publishInterruptCleanup,
        installTerminatedResumable, detachTerminationSource, hendpoint]
  constructor
  · simpa [gate, hmode, applyOperation, haccepted] using hruntime
  · unfold CompositeState.DeferredCancellationWellFormed at hpublished ⊢
    rw [hblockingContext, hblockingContexts, hdeferredProjection, hresumableContexts]
    exact hpublished.2

/-- Explicit termination preserves the complete retained-context
classification for every public gate result.  Lifecycle rejection and every
busy or halted outer-latch result are atomic; acceptance first detaches any
blocked or already-deferred target and then publishes authoritative cleanup. -/
theorem gate_terminateSubject_preserves_deferredBlockingRuntimeWellFormed
    state subject (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (gate state (.terminateSubject subject)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases htermination :
          (SubjectLifecycle.terminate state.lifecycle subject).result with
      | rejected reason =>
          simpa [gate, hmode, applyOperation, htermination] using hstate
      | accepted =>
          simpa [gate, hmode, applyOperation, htermination] using
            installTerminatedSubject_accepted_preserves_deferredBlockingRuntimeWellFormed
              state subject hstate htermination hmode

/-- Current-subject cleanup is the first consumer of the reusable
termination/detachment lemma.  Current selection derives the two source
absences required by that lemma: a current subject is neither an indexed
waiter nor a quiescent retained cancellation. -/
private theorem publishInterruptCleanup_preserves_deferredBlockingRuntimeWellFormed
    state faulting
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some faulting)
    (hmode : state.execution.mode = .running) :
    DeferredBlockingRuntimeWellFormed
      (publishInterruptCleanup state faulting) := by
  have hblockingLifecycle :
      state.blockingIPC.scheduler.lifecycle = state.lifecycle :=
    hstate.1.blockingLifecycle
  have hlifecycle : SubjectLifecycle.WellFormed state.lifecycle :=
    hstate.1.2.2.1
  have hlive :
      state.blockingIPC.scheduler.lifecycle.capabilities.subjects faulting = true := by
    rw [hblockingLifecycle]
    exact hlifecycle.2.2.2.2.2 faulting hcurrent
  have hissued :
      state.blockingIPC.scheduler.lifecycle.issuedSubjects faulting = true := by
    rw [hblockingLifecycle]
    exact hlifecycle.1 faulting (by simpa [hblockingLifecycle] using hlive)
  have hwaiter : state.blockingIPC.waiterEndpoint faulting = none := by
    cases hendpoint : state.blockingIPC.waiterEndpoint faulting with
    | none => rfl
    | some endpoint =>
        have hmember :=
          (hstate.2.1.1.1.2.2.2.2.1 endpoint faulting).mpr hendpoint
        have hnotCurrent :=
          (hstate.2.1.1.1.2.2.1 endpoint faulting hmember).2.2.2.2.2.1
        apply False.elim
        apply hnotCurrent
        simpa [CompositeState.blockingIPCContext, hblockingLifecycle] using hcurrent
  have hdeferred : state.deferredCancels.retained faulting = none := by
    cases hretained : state.deferredCancels.retained faulting with
    | none => rfl
    | some saved =>
        have hnotCurrent := (hstate.2.1.2.2 faulting saved hretained).2.2.2.2.1
        apply False.elim
        apply hnotCurrent
        simpa [CompositeState.blockingIPCContext, hblockingLifecycle] using hcurrent
  exact publishTerminationDetachment_preserves_deferredBlockingRuntimeWellFormed
    state faulting hstate hlive hissued hwaiter hdeferred hmode

/-- Explicit cleanup of the authoritative current subject preserves the
complete deferred invariant.  The explicit publisher additionally clears the
retired subject's retained slot; current-subject quiescence makes that update
extensionally equal to the already-empty slot established by the shared
cleanup proof. -/
private theorem installTerminatedSubject_current_preserves_deferredBlockingRuntimeWellFormed
    state subject
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some subject)
    (hmode : state.execution.mode = .running) :
    DeferredBlockingRuntimeWellFormed
      (installTerminatedSubject state subject
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  have hlifecycle : SubjectLifecycle.WellFormed state.lifecycle :=
    hstate.1.2.2.1
  have hlive : state.lifecycle.capabilities.subjects subject = true :=
    hlifecycle.2.2.2.2.2 subject hcurrent
  have hissued : state.lifecycle.issuedSubjects subject = true :=
    hlifecycle.1 subject hlive
  have haccepted :
      (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted := by
    simp [SubjectLifecycle.terminate, hlive, hissued]
  have hruntime :=
    gate_terminateSubject_accepted_preserves_runtimeWellFormed
      state subject hstate.1 hmode haccepted
  have hpublished :=
    publishInterruptCleanup_preserves_deferredBlockingRuntimeWellFormed
      state subject hstate hcurrent hmode
  have hretained :
      (publishInterruptCleanup state subject).deferredCancels.retained subject = none := by
    cases hvalue :
        (publishInterruptCleanup state subject).deferredCancels.retained subject with
    | none => rfl
    | some saved =>
        have hlivePost :=
          (hpublished.2.1.2.2 subject saved hvalue).2.2.1
        have hdead := ResumablePreemption.cleanup_terminates_subject
          state.resumable subject
        have hdeadBlocking :
            (publishInterruptCleanup state subject).blockingIPCContext.ipc.scheduler.lifecycle.capabilities.subjects
                subject = false := by
          simpa [publishInterruptCleanup, CompositeState.blockingIPCContext,
            BlockingIPCContext.detachInvalidated, installTerminatedResumable] using hdead
        rw [hdeadBlocking] at hlivePost
        contradiction
  have hdeferred :
      BlockingIPCContext.setRetained
          (publishInterruptCleanup state subject).deferredCancels subject none =
        (publishInterruptCleanup state subject).deferredCancels := by
    cases hdeferredState :
        (publishInterruptCleanup state subject).deferredCancels with
    | mk retained =>
        have hsubject : retained subject = none := by
          simpa [hdeferredState] using hretained
        change
          (⟨fun candidate =>
              if candidate = subject then none else retained candidate⟩ :
                BlockingIPCContext.DeferredCancelState) =
            (⟨retained⟩ : BlockingIPCContext.DeferredCancelState)
        congr
        funext candidate
        by_cases heq : candidate = subject
        · subst candidate
          simp [hsubject]
        · simp [heq]
  have hdeferredProjection :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).deferredCancels =
        (publishInterruptCleanup state subject).deferredCancels := by
    simpa [installTerminatedSubject, publishInterruptCleanup] using hdeferred
  have hblockingContext :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).blockingIPCContext =
        (publishInterruptCleanup state subject).blockingIPCContext := rfl
  have hresumableContexts :
      (installTerminatedSubject state subject
          (ResumablePreemption.cleanupSubject state.resumable subject)).resumable.contexts =
        (publishInterruptCleanup state subject).resumable.contexts := rfl
  constructor
  · simpa [gate, hmode, applyOperation, haccepted] using hruntime
  · unfold CompositeState.DeferredCancellationWellFormed at hpublished ⊢
    rw [hblockingContext, hdeferredProjection, hresumableContexts]
    exact hpublished.2

/-- Contained cleanup establishes the complete deferred-cancellation
post-state when the trusted faulting identity is the authoritative current
subject.  The binding rules out the only otherwise possible collision: a
quiescent retained identity cannot simultaneously be the subject retired by
the interrupt. -/
theorem interrupt_contained_preserves_deferredBlockingRuntimeWellFormed
    state frame faulting
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hbound : ContainedFaultIdentityBound state)
    (hcontained : (dispatchHardware state.execution frame).action = .contained faulting) :
    DeferredBlockingRuntimeWellFormed
      (applyOperation state (.interrupt frame)) := by
  have hcurrent : state.lifecycle.current = some faulting :=
    contained_faulting_identity_is_current state frame faulting hbound hcontained
  have hmode : state.execution.mode = .running := by
    cases hmode : state.execution.mode with
    | handling active => simp [dispatchHardware, hmode, halt] at hcontained
    | halted record => simp [dispatchHardware, hmode] at hcontained
    | running => rfl
  simpa [applyOperation, hcontained, hcurrent] using
    publishInterruptCleanup_preserves_deferredBlockingRuntimeWellFormed
      state faulting hstate hcurrent hmode

/-- Scheduler-selected termination preserves the complete retained-context
classification for every typed result.  A missing current subject and every
busy or halted outer-latch result are atomic; acceptance retires the
authoritative current subject through the shared cleanup publisher. -/
theorem gate_terminateCurrent_preserves_deferredBlockingRuntimeWellFormed
    state (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed (gate state .terminateCurrent).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases hcurrent : state.scheduler.lifecycle.current with
      | none =>
          simpa [gate, hmode, applyOperation, Scheduler.terminateCurrent,
            Scheduler.reject, hcurrent] using hstate
      | some subject =>
          have hschedulerLifecycle : state.scheduler.lifecycle = state.lifecycle :=
            hstate.1.1.2.1
          have hlifecycleCurrent : state.lifecycle.current = some subject := by
            rw [← hschedulerLifecycle]
            exact hcurrent
          have hpreserved :=
            installTerminatedSubject_current_preserves_deferredBlockingRuntimeWellFormed
              state subject hstate hlifecycleCurrent hmode
          have hlifecycle : SubjectLifecycle.WellFormed state.lifecycle :=
            hstate.1.2.2.1
          have hlive : state.lifecycle.capabilities.subjects subject = true :=
            hlifecycle.2.2.2.2.2 subject hlifecycleCurrent
          have hissued : state.lifecycle.issuedSubjects subject = true :=
            hlifecycle.1 subject hlive
          have haccepted :
              (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted := by
            simp [SubjectLifecycle.terminate, hlive, hissued]
          have hterminated :
              (Scheduler.terminateCurrent state.scheduler).result = .accepted := by
            cases htermination :
                SubjectLifecycle.terminate state.lifecycle subject with
            | mk lifecycle result =>
                cases result with
                | rejected reason => simp [htermination] at haccepted
                | accepted =>
                    simp [Scheduler.terminateCurrent, hcurrent,
                      hschedulerLifecycle, hlifecycleCurrent, htermination]
          simpa [gate, hmode, applyOperation, hterminated, hcurrent] using hpreserved

/-- The identity binding makes the faulting subject's retained slot
uninhabited after cleanup.  Without the binding, the pre-state deferred
invariant permits exactly the stale quiescent identity that motivated this
contained-entry premise. -/
theorem interrupt_contained_clears_faulting_deferred
    state frame faulting
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hbound : ContainedFaultIdentityBound state)
    (hcontained : (dispatchHardware state.execution frame).action = .contained faulting) :
    (applyOperation state (.interrupt frame)).deferredCancels.retained faulting = none := by
  have hcurrent : state.lifecycle.current = some faulting :=
    contained_faulting_identity_is_current state frame faulting hbound hcontained
  have hpost := interrupt_contained_preserves_deferredBlockingRuntimeWellFormed
    state frame faulting hstate hbound hcontained
  cases hretained :
      (applyOperation state (.interrupt frame)).deferredCancels.retained faulting with
  | none => rfl
  | some saved =>
      have hlive := hpost.2.1.2.2 faulting saved hretained
      have hdead := ResumablePreemption.cleanup_terminates_subject
        state.resumable faulting
      have hdeadLifecycle :
          (applyOperation state (.interrupt frame)).lifecycle.capabilities.subjects
            faulting = false := by
        simpa [applyOperation, hcontained, hcurrent, publishInterruptCleanup,
          installTerminatedResumable] using hdead
      have :
          (applyOperation state (.interrupt frame)).blockingIPCContext.ipc.scheduler.lifecycle.capabilities.subjects
            faulting = false := by
        rw [show
          (applyOperation state (.interrupt frame)).blockingIPCContext.ipc.scheduler.lifecycle =
            (applyOperation state (.interrupt frame)).lifecycle by
          exact hpost.1.blockingLifecycle]
        exact hdeadLifecycle
      have hlive' := hlive.2.2.1
      rw [this] at hlive'
      contradiction

/-- Exact pointwise contained-fault cleanup law, including validity, peer
quiescence, and its remaining address-space authority. -/
theorem interrupt_contained_defers_invalidated_waiter
    state frame faulting peer endpoint saved
    (hcurrentFaulting : state.lifecycle.current = some faulting)
    (hcontained : (dispatchHardware state.execution frame).action = .contained faulting)
    (hendpoint :
      (BlockingIPCContext.terminate state.blockingIPCContext faulting).ipc.waiterEndpoint peer =
        some endpoint)
    (hsaved :
      (BlockingIPCContext.terminate state.blockingIPCContext faulting).blocked peer = some saved)
    (hretired :
      (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.objects
        endpoint = false)
    (hvalid : BlockingIPCContext.validSaved peer saved = true)
    (hlive :
      (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.capabilities.subjects
        peer = true)
    (hquiescent :
      ((ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.runnable
        peer) = false)
    (hcurrent :
      (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.lifecycle.current ≠
        some peer)
    (hready :
      peer ∉ (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler.ready)
    (hauthority :
      Scheduler.ownsAddressSpace
        (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler peer = some peer) :
    let next := applyOperation state (.interrupt frame)
    next.blockingIPC.waiterEndpoint peer = none ∧
      next.blockingContexts peer = none ∧
      next.deferredCancels.retained peer = some saved ∧
      BlockingIPCContext.validSaved peer saved = true ∧
      next.scheduler.lifecycle.capabilities.subjects peer = true ∧
      next.scheduler.lifecycle.runnable peer = false ∧
      next.scheduler.lifecycle.current ≠ some peer ∧
      peer ∉ next.scheduler.ready ∧
      Scheduler.ownsAddressSpace next.scheduler peer = some peer := by
  have hexact := BlockingIPCContext.detachInvalidated_invalidated_exact
    (BlockingIPCContext.terminate state.blockingIPCContext faulting)
    state.deferredCancels
    (ResumablePreemption.cleanupSubject state.resumable faulting).scheduler
    peer endpoint saved hendpoint hsaved hretired
  simpa [applyOperation, hcontained, hcurrentFaulting, publishInterruptCleanup,
    installTerminatedResumable] using
    And.intro hexact.1
      (And.intro hexact.2.1
        (And.intro hexact.2.2
          ⟨hvalid, hlive, hquiescent, hcurrent, hready, hauthority⟩))

private theorem blockingContextAgreement_of_projections
    (before after : CompositeState)
    (hstate : BlockingIPCContext.ContextAgreement before.blockingIPCContext)
    (hwaiter : after.blockingIPC.waiterEndpoint = before.blockingIPC.waiterEndpoint)
    (hcontexts : after.blockingContexts = before.blockingContexts) :
    BlockingIPCContext.ContextAgreement after.blockingIPCContext := by
  rcases hstate with ⟨hagreement, hvalid⟩
  constructor
  · intro subject
    simpa [CompositeState.blockingIPCContext, hwaiter, hcontexts] using
      hagreement subject
  · intro subject saved hsaved
    apply hvalid subject saved
    simpa [CompositeState.blockingIPCContext, hcontexts] using hsaved

private theorem publishTerminatedBlockingSubject_preserves_contextAgreement
    state subject
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    BlockingIPCContext.ContextAgreement
      (publishTerminatedBlockingSubject state subject).blockingIPCContext := by
  cases hterminate :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result with
  | rejected reason =>
      simpa [publishTerminatedBlockingSubject, hterminate] using hstate
  | accepted =>
      simpa [publishTerminatedBlockingSubject, hterminate] using
        blockingIPCContext_terminate_preserves_contextAgreement
          state.blockingIPCContext subject hstate

private theorem dispatchIPC_preserves_contextAgreement state call
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    BlockingIPCContext.ContextAgreement (dispatchIPC state call).state.blockingIPCContext := by
  apply blockingContextAgreement_of_projections state _ hstate
  · cases call with
    | send handleWord word0 word1 => rfl
    | receive handleWord =>
        simp only [dispatchIPC]
        generalize hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint = resolved
        cases resolved with
        | error reason => simp [hresolve, installIPC]
        | ok endpoint =>
            cases hpending : state.transfers.pending endpoint.capability.object <;>
              simp [hresolve, hpending, installIPC]
  · cases call with
    | send handleWord word0 word1 => rfl
    | receive handleWord =>
        simp only [dispatchIPC]
        generalize hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint = resolved
        cases resolved with
        | error reason => simp [hresolve, installIPC]
        | ok endpoint =>
            cases hpending : state.transfers.pending endpoint.capability.object <;>
              simp [hresolve, hpending, installIPC]

private theorem installTerminatedSubject_preserves_contextAgreement state subject resumable
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    BlockingIPCContext.ContextAgreement
      (installTerminatedSubject state subject resumable).blockingIPCContext := by
  have hterminated := blockingIPCContext_terminate_preserves_contextAgreement
    state.blockingIPCContext subject hstate
  have hdetached := BlockingIPCContext.detachInvalidated_preserves_contextAgreement
    (BlockingIPCContext.terminate state.blockingIPCContext subject)
    state.deferredCancels resumable.scheduler hterminated
  rcases hdetached with ⟨hprojection, hvalid⟩
  constructor
  · simpa [installTerminatedSubject, CompositeState.blockingIPCContext] using hprojection
  · simpa [installTerminatedSubject, CompositeState.blockingIPCContext] using hvalid

/-- Every ordinary composite operation preserves the exact waiter/saved-context
agreement.  Operations unrelated to blocking retain both projections
literally; explicit termination removes the indexed waiter and saved context
together. -/
theorem gate_preserves_blockingContextAgreement state operation
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    BlockingIPCContext.ContextAgreement
      (gate state operation).state.blockingIPCContext := by
  cases hmode : state.execution.mode with
  | handling active =>
      cases operation with
      | nmi raw context =>
          simpa [gate, hmode, applyOperation, CompositeState.blockingIPCContext] using hstate
      | _ => simpa [gate, hmode] using hstate
  | halted record => cases operation <;> simpa [gate, hmode] using hstate
  | running =>
      cases operation <;> simp only [gate, hmode, applyOperation]
      all_goals repeat' first | split
      all_goals try exact hstate
      all_goals try exact publishInterruptCleanup_preserves_contextAgreement state _ hstate
      all_goals try
        apply blockingContextAgreement_of_projections state _ hstate <;>
          grind [selectLiveReturnAuthority, dispatchIPC, installIPC,
            installResumable, installTransfers, installCopiedCapabilities,
            installVirtualMemory, installCreatedSubject, installSchedulerAdmission,
            installSchedulerRemoval, installScheduler, installLifecycle,
            synchronizeMemory, publishInterruptCleanup]
      all_goals try
        apply blockingContextAgreement_of_projections
          (publishTerminatedBlockingSubject state _) _
          (publishTerminatedBlockingSubject_preserves_contextAgreement state _ hstate) <;>
          grind [installTerminatedSubject, installTerminatedResumable]
      all_goals try exact dispatchIPC_preserves_contextAgreement state _ hstate
      all_goals try exact installTerminatedSubject_preserves_contextAgreement state _ _ hstate
      all_goals try
        cases hcurrent : state.scheduler.lifecycle.current with
        | none => exact hstate
        | some subject =>
            exact installTerminatedSubject_preserves_contextAgreement state subject _ hstate

/-- Ordinary operations in this family do not mutate the authoritative
blocking endpoint, scheduler, waiter, completion, or saved-context store. -/
inductive BlockingStateNeutralOperation : Operation → Prop where
  | selectUserReturn purpose : BlockingStateNeutralOperation (.selectUserReturn purpose)
  | userReturn request : BlockingStateNeutralOperation (.userReturn request)
  | ipc call : BlockingStateNeutralOperation (.ipc call)
  | scheduleNext : BlockingStateNeutralOperation .scheduleNext
  | scheduleYield : BlockingStateNeutralOperation .scheduleYield
  | scheduleTick : BlockingStateNeutralOperation .scheduleTick
  | restart : BlockingStateNeutralOperation .restart

/-- A blocking-state-neutral ordinary step retains the complete typed blocking
state literally, not merely its waiter/context agreement projection. -/
theorem gate_blockingStateNeutral_preserves_blockingIPCContext state operation
    (hoperation : BlockingStateNeutralOperation operation) :
    (gate state operation).state.blockingIPCContext = state.blockingIPCContext := by
  cases hmode : state.execution.mode with
  | handling active => cases hoperation <;> simp [gate, hmode, applyOperation]
  | halted record => cases hoperation <;> simp [gate, hmode]
  | running =>
      cases hoperation
      · simp only [gate, hmode, applyOperation, selectLiveReturnAuthority]
        split <;> rfl
      · simp only [gate, hmode, applyOperation]
        split <;> split <;> rfl
      · rename_i call
        cases call with
        | send handleWord word0 word1 =>
            simp only [gate, hmode, applyOperation, dispatchIPC]
            generalize hdispatch :
              IPCSyscall.dispatch state.ipc state.ipcContext
                (.send handleWord word0 word1) = outcome
            cases outcome with
            | mk ipc reply =>
                cases reply <;>
                  simp [hdispatch, installIPC, CompositeState.blockingIPCContext]
        | receive handleWord =>
            simp only [gate, hmode, applyOperation, dispatchIPC]
            generalize hresolve :
              CapabilityHandle.resolveCurrent state.transfers.capabilities
                { caller := state.execution.core.context.currentSubject }
                handleWord .endpoint = resolved
            cases resolved with
            | error reason =>
                generalize hdispatch :
                  IPCSyscall.dispatch state.ipc state.ipcContext
                    (.receive handleWord) = outcome
                cases outcome with
                | mk ipc reply =>
                    cases reply <;>
                      simp [hresolve, hdispatch, installIPC,
                        CompositeState.blockingIPCContext]
            | ok endpoint =>
                cases hpending : state.transfers.pending endpoint.capability.object with
                | some envelope => simp [hresolve, hpending]
                | none =>
                    generalize hdispatch :
                      IPCSyscall.dispatch state.ipc state.ipcContext
                        (.receive handleWord) = outcome
                    cases outcome with
                    | mk ipc reply =>
                        cases reply <;>
                          simp [hresolve, hpending, hdispatch, installIPC,
                            CompositeState.blockingIPCContext]
      · simp only [gate, hmode, applyOperation]
        unfold schedulerDispatch
        generalize Scheduler.selectNext state.scheduler = outcome
        cases outcome with
        | mk scheduler result =>
            cases result with
            | rejected reason => simp [Scheduler.reject]
            | accepted selected => cases selected <;> simp [Scheduler.reject]
      · simp only [gate, hmode, applyOperation]
        unfold schedulerYield
        generalize Scheduler.yield state.scheduler = outcome
        cases outcome with
        | mk scheduler result => cases result <;> simp [Scheduler.reject]
      · simp only [gate, hmode, applyOperation]
        unfold schedulerTick
        generalize Scheduler.tick state.scheduler = outcome
        cases outcome with
        | mk scheduler result => cases result <;> simp [Scheduler.reject]
      · simp [gate, hmode, applyOperation]

/-- The first readiness-free ordinary slice preserves the full blocking
runtime invariant for every typed result and every execution-latch mode. -/
theorem gate_blockingStateNeutral_preserves_blockingRuntimeWellFormed state operation
    (hoperation : BlockingStateNeutralOperation operation)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state operation).state := by
  constructor
  · exact gate_preserves_runtimeWellFormed state operation hstate.1
  · rw [gate_blockingStateNeutral_preserves_blockingIPCContext state operation hoperation]
    exact hstate.2

/-- The complete raw syscall family retains the full blocking invariant.
Decoder and subsystem denials are atomic, access acceptance changes only
return-control state, and accepted map/unmap publication reuses the same
scheduler-preserving virtual-memory boundary as the corresponding raw
operations before selecting the syscall return authority. -/
theorem gate_syscall_preserves_blockingRuntimeWellFormed state call
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state (.syscall call)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases hdecode : Syscall.decode call with
      | error reason => simpa [gate, hmode, applyOperation, Syscall.dispatch, hdecode] using hstate
      | ok operation =>
          cases operation with
          | access page access =>
              cases hreply :
                  (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
              | rejected reason => simpa [gate, hmode, applyOperation, hreply] using hstate
              | accepted =>
                  have hselected :=
                    gate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
                      state (.selectUserReturn .syscallResume)
                      (.selectUserReturn .syscallResume) hstate
                  simpa [gate, hmode, applyOperation, hreply, hdecode] using hselected
          | map handleWord page permissions =>
              cases hreply :
                  (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
              | rejected reason => simpa [gate, hmode, applyOperation, hreply] using hstate
              | accepted =>
                  cases hresolve : CapabilityHandle.resolveCurrent
                      state.virtualMemory.memory.capabilities
                      { caller := state.syscallContext.caller } handleWord .memory with
                  | error denial =>
                      simp only [CompositeState.syscallContext] at hresolve
                      simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve,
                        CompositeState.syscallContext] at hreply
                  | ok resolution =>
                      simp only [CompositeState.syscallContext] at hresolve
                      cases hmap : (VirtualMapping.map state.virtualMemory
                          state.syscallContext.caller resolution.handle.slot
                          state.syscallContext.activeAddressSpace page permissions).result with
                      | rejected reason =>
                          simp only [CompositeState.syscallContext] at hmap
                          simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve,
                            hmap, CompositeState.syscallContext] at hreply
                      | accepted =>
                          simp only [CompositeState.syscallContext] at hmap
                          let next := (VirtualMapping.map state.virtualMemory
                            state.syscallContext.caller resolution.handle.slot
                            state.syscallContext.activeAddressSpace page permissions).state
                          have hmemory : next.memory = state.virtualMemory.memory :=
                            VirtualMapping.map_memory _ _ _ _ _ _
                          have howner : next.owner = state.virtualMemory.owner :=
                            VirtualMapping.map_owner _ _ _ _ _ _
                          have hvirtual : VirtualMapping.LifecycleWellFormed next :=
                            VirtualMapping.map_preserves_lifecycleWellFormed _ _ _ _ _ _
                              hstate.1.2.2.2.2.1
                          let translations : TLB.State :=
                            { state.resumable.translations with virtual := next }
                          have htlb : TLB.Coherent translations := by
                            simpa [translations, TLB.Coherent] using
                              hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
                          have hinstalled :=
                            installVirtualMemory_preserves_blockingRuntimeWellFormed
                              state next translations hstate hmemory howner hvirtual htlb rfl
                          have hselected :=
                            gate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
                              (installVirtualMemory state next translations)
                              (.selectUserReturn .syscallResume)
                              (.selectUserReturn .syscallResume) hinstalled
                          have hselected' : BlockingRuntimeWellFormed
                              (selectLiveReturnAuthority
                                (installVirtualMemory state next translations)
                                .syscallResume) := by
                            simpa [gate, applyOperation, installVirtualMemory, hmode] using hselected
                          have houtcome :
                              Syscall.dispatch state.virtualMemory state.syscallContext call =
                                { state := next, reply := .accepted } := by
                            simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve,
                              hmap, CompositeState.syscallContext, next]
                          simpa [gate, hmode, applyOperation, houtcome, hdecode,
                            next, translations] using hselected'
          | unmap page =>
              cases hreply :
                  (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
              | rejected reason => simpa [gate, hmode, applyOperation, hreply] using hstate
              | accepted =>
                  cases hunmap : (VirtualMapping.unmap state.virtualMemory
                      state.syscallContext.caller state.syscallContext.activeAddressSpace page).result with
                  | rejected reason =>
                      simp only [CompositeState.syscallContext] at hunmap
                      simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hunmap,
                        CompositeState.syscallContext] at hreply
                  | accepted =>
                      simp only [CompositeState.syscallContext] at hunmap
                      let next := (VirtualMapping.unmap state.virtualMemory
                        state.syscallContext.caller state.syscallContext.activeAddressSpace page).state
                      have hmemory : next.memory = state.virtualMemory.memory :=
                        VirtualMapping.unmap_memory _ _ _ _
                      have howner : next.owner = state.virtualMemory.owner :=
                        VirtualMapping.unmap_owner _ _ _ _
                      have hvirtual : VirtualMapping.LifecycleWellFormed next :=
                        VirtualMapping.unmap_preserves_lifecycleWellFormed _ _ _ _
                          hstate.1.2.2.2.2.1
                      let translations := TLB.invalidatePage
                        { state.resumable.translations with virtual := next }
                        state.syscallContext.activeAddressSpace page
                      have htlb : TLB.Coherent translations := by
                        exact TLB.invalidate_page_preserves_coherent _ _ _
                          hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
                      have hinstalled :=
                        installVirtualMemory_preserves_blockingRuntimeWellFormed
                          state next translations hstate hmemory howner hvirtual htlb rfl
                      have hselected :=
                        gate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
                          (installVirtualMemory state next translations)
                          (.selectUserReturn .syscallResume)
                          (.selectUserReturn .syscallResume) hinstalled
                      have hselected' : BlockingRuntimeWellFormed
                          (selectLiveReturnAuthority
                            (installVirtualMemory state next translations)
                            .syscallResume) := by
                        simpa [gate, applyOperation, installVirtualMemory, hmode] using hselected
                      have houtcome :
                          Syscall.dispatch state.virtualMemory state.syscallContext call =
                            { state := next, reply := .accepted } := by
                        simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hunmap,
                          CompositeState.syscallContext, next]
                      simpa [gate, hmode, applyOperation, houtcome, hdecode,
                        next, translations] using hselected'

/-- A sealed transfer offer retains the complete blocking precondition.
Accepted offers allocate a pending descendant and publish its sealed mailbox,
but preserve exactly the subject, object, kind, and live-slot registries used
to validate every existing waiter.  Rejected offers and outer-latch denials
are literal no-ops. -/
theorem gate_transferOffer_preserves_blockingRuntimeWellFormed state endpointWord sourceWord
    sourceKind payload rights (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      let outcome := CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
        payload rights
      cases hresult : outcome.result with
      | rejected reason =>
          simpa [gate, hmode, applyOperation, outcome, hresult] using hstate
      | accepted =>
          have haccepted :
              (CapabilityTransfer.offerWords state.transfers
                state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
                payload rights).result = .accepted := by
            simpa [outcome] using hresult
          have hglobal :=
            (gate_transferOffer_accepted_preserves_runtimeWellFormed state endpointWord sourceWord
              sourceKind payload rights hstate.1 hmode haccepted).1
          refine ⟨hglobal, ?_⟩
          let next := (CapabilityTransfer.offerWords state.transfers
            state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
            payload rights).state
          have htransfer : CapabilityTransfer.WellFormed next :=
            CapabilityTransfer.offerWords_accepted_preserves_wellFormed state.transfers
              state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
              payload rights hstate.1.2.2.2.2.2.2.2.2.2.1 haccepted
          have hregistry :=
            CapabilityTransfer.offerWords_accepted_preserves_authority_registry
              state.transfers state.execution.core.context.currentSubject endpointWord sourceWord
              sourceKind payload rights haccepted
          change next.capabilities.subjects = state.transfers.capabilities.subjects ∧
              next.capabilities.objects = state.transfers.capabilities.objects ∧
              next.capabilities.kinds = state.transfers.capabilities.kinds ∧
              next.capabilities.slots = state.transfers.capabilities.slots ∧
              next.allocator = state.transfers.allocator ∧
              next.binding = state.transfers.binding ∧
              next.issued = state.transfers.issued ∧
              next.issuedAddressSpace = state.transfers.issuedAddressSpace at hregistry
          rcases hregistry with ⟨hsubjects, hobjects, hkinds, hslots, _⟩
          rcases hstate.1.1 with
            ⟨_, hschedulerLifecycle, _, _, _, _, hipcCapabilities, _, _,
              htransferEndpoints, _⟩
          have hbase : state.transfers.capabilities =
              state.blockingIPC.scheduler.lifecycle.capabilities := by
            calc
              state.transfers.capabilities = state.ipc.endpoints.capabilities := by
                exact congrArg (fun endpoints => endpoints.capabilities) htransferEndpoints
              _ = state.lifecycle.capabilities := hipcCapabilities
              _ = state.blockingIPC.scheduler.lifecycle.capabilities :=
                congrArg SubjectLifecycle.State.capabilities hstate.1.blockingLifecycle.symm
          have hsubjects' : next.capabilities.subjects =
              state.blockingIPC.scheduler.lifecycle.capabilities.subjects :=
            hsubjects.trans (congrArg Capability.State.subjects hbase)
          have hobjects' : next.capabilities.objects =
              state.blockingIPC.scheduler.lifecycle.capabilities.objects :=
            hobjects.trans (congrArg Capability.State.objects hbase)
          have hkinds' : next.capabilities.kinds =
              state.blockingIPC.scheduler.lifecycle.capabilities.kinds :=
            hkinds.trans (congrArg Capability.State.kinds hbase)
          have hslots' : next.capabilities.slots =
              state.blockingIPC.scheduler.lifecycle.capabilities.slots :=
            hslots.trans (congrArg Capability.State.slots hbase)
          rcases hstate.2 with ⟨hblocking, hagreement⟩
          rcases hblocking with
            ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, _⟩
          rcases hglobal with ⟨_, _, _, _, _, _, hscheduler, _, _, _, _, _, _⟩
          have hscheduler' : Scheduler.WellFormed
              { state.scheduler with lifecycle :=
                { state.lifecycle with capabilities := next.capabilities } } := by
            simpa [gate, hmode, applyOperation, haccepted, installTransfers, next] using
              hscheduler
          have hblocking' : BlockingIPC.WellFormed
              { state.blockingIPC with scheduler :=
                { state.scheduler with lifecycle :=
                  { state.lifecycle with capabilities := next.capabilities } } } := by
            refine ⟨hscheduler', hqueues, ?_, hunique, hindex, ?_, htransfer.1.1⟩
            · intro endpoint subject hmember
              obtain ⟨hliveEndpoint, ⟨slot, capability, hslot, hobject, hkind,
                hreceive, _⟩, hliveSubject, hrunnable, howner, hcurrent, hready⟩ :=
                hwaiters endpoint subject hmember
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hobjects']
                exact hliveEndpoint
              · refine ⟨slot, capability, ?_, hobject, hkind, hreceive, ?_⟩
                · rw [hslots']
                  exact hslot
                · rw [hobjects']
                  exact hliveEndpoint
              · rw [hsubjects']
                exact hliveSubject
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle] using hrunnable
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle, Scheduler.ownsAddressSpace] using howner
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle] using hcurrent
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler] using hready
            · intro endpoint envelope hmail
              obtain ⟨hlive, hkind, henvelope, hempty⟩ := hmailbox endpoint envelope hmail
              refine ⟨?_, ?_, henvelope, hempty⟩
              · rw [hobjects']
                exact hlive
              · rw [hkinds']
                exact hkind
          simpa [gate, hmode, applyOperation, haccepted, installTransfers,
            CompositeState.blockingIPCContext, BlockingIPCContext.ContextAgreement,
            BlockingIPCContext.WellFormed, next] using And.intro hblocking' hagreement

/-- A sealed transfer receipt retains the complete blocking precondition.
Delivery may fill one checked-empty capability slot and consume one mailbox,
but preserves every pre-existing waiter authority and every remaining mailbox
entry. Rejected receipts and outer-latch denials are literal no-ops. -/
theorem gate_transferAccept_preserves_blockingRuntimeWellFormed state endpointWord
    destinationSlot (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.transferAccept endpointWord destinationSlot)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      let outcome := CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot
      cases hresult : outcome.result with
      | rejected reason =>
          simpa [gate, hmode, applyOperation, outcome, hresult] using hstate
      | delivered envelope =>
          have hdelivered :
              (CapabilityTransfer.acceptWord state.transfers
                state.execution.core.context.currentSubject endpointWord
                destinationSlot).result = .delivered envelope := by
            simpa [outcome] using hresult
          have hglobal :=
            (gate_transferAccept_delivered_preserves_runtimeWellFormed state endpointWord
              destinationSlot envelope hstate.1 hmode hdelivered).1
          refine ⟨hglobal, ?_⟩
          let next := (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).state
          have htransfer : CapabilityTransfer.WellFormed next :=
            CapabilityTransfer.acceptWord_preserves_wellFormed state.transfers
              state.execution.core.context.currentSubject endpointWord destinationSlot
              hstate.1.2.2.2.2.2.2.2.2.2.1
          have hmetadata :=
            CapabilityTransfer.acceptWord_delivered_preserves_registry_and_authority
              state.transfers state.execution.core.context.currentSubject endpointWord
              destinationSlot envelope hdelivered
          change next.capabilities.subjects = state.transfers.capabilities.subjects ∧
              next.capabilities.objects = state.transfers.capabilities.objects ∧
              next.capabilities.kinds = state.transfers.capabilities.kinds ∧
              next.capabilities.slotCapacity = state.transfers.capabilities.slotCapacity ∧
              (∀ subject slot capability,
                state.transfers.capabilities.slots subject slot = some capability →
                  next.capabilities.slots subject slot = some capability) ∧
              (∀ subject object right,
                Capability.HasAuthority state.transfers.capabilities subject object right →
                  Capability.HasAuthority next.capabilities subject object right) at hmetadata
          rcases hmetadata with
            ⟨hsubjects, hobjects, hkinds, _hcapacity, hslots, _hauthority⟩
          rcases hstate.1.1 with
            ⟨_, hschedulerLifecycle, _, _, _, _, hipcCapabilities, _, _,
              htransferEndpoints, _⟩
          have hbase : state.transfers.capabilities =
              state.blockingIPC.scheduler.lifecycle.capabilities := by
            calc
              state.transfers.capabilities = state.ipc.endpoints.capabilities := by
                exact congrArg (fun endpoints => endpoints.capabilities) htransferEndpoints
              _ = state.lifecycle.capabilities := hipcCapabilities
              _ = state.blockingIPC.scheduler.lifecycle.capabilities :=
                congrArg SubjectLifecycle.State.capabilities hstate.1.blockingLifecycle.symm
          have hsubjects' : next.capabilities.subjects =
              state.blockingIPC.scheduler.lifecycle.capabilities.subjects :=
            hsubjects.trans (congrArg Capability.State.subjects hbase)
          have hobjects' : next.capabilities.objects =
              state.blockingIPC.scheduler.lifecycle.capabilities.objects :=
            hobjects.trans (congrArg Capability.State.objects hbase)
          have hkinds' : next.capabilities.kinds =
              state.blockingIPC.scheduler.lifecycle.capabilities.kinds :=
            hkinds.trans (congrArg Capability.State.kinds hbase)
          rcases hstate.2 with ⟨hblocking, hagreement⟩
          rcases hblocking with
            ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, _⟩
          rcases hglobal with ⟨_, _, _, _, _, _, hscheduler, _, _, _, _, _, _⟩
          have hscheduler' : Scheduler.WellFormed
              { state.scheduler with lifecycle :=
                { state.lifecycle with capabilities := next.capabilities } } := by
            simpa [gate, hmode, applyOperation, hdelivered, installTransfers, next] using
              hscheduler
          have hblocking' : BlockingIPC.WellFormed
              { state.blockingIPC with
                scheduler :=
                  { state.scheduler with lifecycle :=
                    { state.lifecycle with capabilities := next.capabilities } } } := by
            refine ⟨hscheduler', hqueues, ?_, hunique, hindex, ?_, htransfer.1.1⟩
            · intro endpoint subject hmember
              obtain ⟨hliveEndpoint, ⟨slot, capability, hslot, hobject, hkind,
                hreceive, _⟩, hliveSubject, hrunnable, howner, hcurrent, hready⟩ :=
                hwaiters endpoint subject hmember
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hobjects']
                exact hliveEndpoint
              · refine ⟨slot, capability, ?_, hobject, hkind, hreceive, ?_⟩
                · apply hslots
                  simpa [CompositeState.blockingIPCContext, hbase] using hslot
                · rw [hobjects']
                  exact hliveEndpoint
              · rw [hsubjects']
                exact hliveSubject
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle] using hrunnable
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle, Scheduler.ownsAddressSpace] using howner
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle] using hcurrent
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler] using hready
            · intro endpoint found hmail
              obtain ⟨hlive, hkind, henvelope, hempty⟩ :=
                hmailbox endpoint found hmail
              refine ⟨?_, ?_, henvelope, hempty⟩
              · rw [hobjects']
                exact hlive
              · rw [hkinds']
                exact hkind
          simpa [gate, hmode, applyOperation, hdelivered, installTransfers,
            CompositeState.blockingIPCContext, BlockingIPCContext.ContextAgreement,
            BlockingIPCContext.WellFormed, next] using And.intro hblocking' hagreement

/-- Capability delegation retains the complete blocking precondition.
Accepted copy fills one checked-empty slot and preserves every authority
already held by an indexed waiter; typed denials and outer-latch rejection are
literal no-ops. -/
theorem gate_capabilityCopy_preserves_blockingRuntimeWellFormed state source destination
    destinationSlot rights (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.capabilityCopy source destination destinationSlot rights)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      let outcome := Capability.copy state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
      cases hresult : outcome.result with
      | rejected reason =>
          simpa [gate, hmode, applyOperation, outcome, hresult] using hstate
      | accepted =>
          have haccepted :
              (Capability.copy state.capabilities
                state.execution.core.context.currentSubject source destination destinationSlot
                rights).result = .accepted := by
            simpa [outcome] using hresult
          let next := (Capability.copy state.capabilities
            state.execution.core.context.currentSubject source destination destinationSlot
            rights).state
          have hcopy :
              Capability.copy state.capabilities
                state.execution.core.context.currentSubject source destination destinationSlot
                rights = { state := next, result := .accepted } := by
            cases hraw : Capability.copy state.capabilities
                state.execution.core.context.currentSubject source destination destinationSlot
                rights with
            | mk actual actualResult =>
                simp [hraw, next] at haccepted ⊢
                exact haccepted
          have hglobal :=
            (gate_capabilityCopy_accepted_preserves_runtimeWellFormed state source destination
              destinationSlot rights next hstate.1 hmode hcopy).1
          refine ⟨hglobal, ?_⟩
          have hcapabilities : Capability.WellFormed next :=
            Capability.copy_preserves_wellFormed state.capabilities
              state.execution.core.context.currentSubject source destination destinationSlot
              rights hstate.1.2.2.2.1
          have hregistry := Capability.copy_preserves_registries state.capabilities
            state.execution.core.context.currentSubject source destination destinationSlot rights
          change next.subjects = state.capabilities.subjects ∧
              next.objects = state.capabilities.objects ∧
              next.kinds = state.capabilities.kinds ∧
              next.slotCapacity = state.capabilities.slotCapacity at hregistry
          rcases hregistry with ⟨hsubjects, hobjects, hkinds, _hcapacity⟩
          rcases hstate.1.1 with
            ⟨_, hschedulerLifecycle, _, hcapabilitiesCoherent, _, _, _, _, _, _, _⟩
          have hbase : state.capabilities =
              state.blockingIPC.scheduler.lifecycle.capabilities := by
            exact hcapabilitiesCoherent.trans
              (congrArg SubjectLifecycle.State.capabilities hstate.1.blockingLifecycle.symm)
          have hsubjects' : next.subjects =
              state.blockingIPC.scheduler.lifecycle.capabilities.subjects :=
            hsubjects.trans (congrArg Capability.State.subjects hbase)
          have hobjects' : next.objects =
              state.blockingIPC.scheduler.lifecycle.capabilities.objects :=
            hobjects.trans (congrArg Capability.State.objects hbase)
          have hkinds' : next.kinds =
              state.blockingIPC.scheduler.lifecycle.capabilities.kinds :=
            hkinds.trans (congrArg Capability.State.kinds hbase)
          rcases hstate.2 with ⟨hblocking, hagreement⟩
          rcases hblocking with
            ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, holdCapabilities⟩
          rcases hglobal with ⟨_, _, _, _, _, _, hscheduler, _, _, _, _, _, _⟩
          have hscheduler' : Scheduler.WellFormed
              { state.scheduler with lifecycle :=
                { state.lifecycle with capabilities := next } } := by
            simpa [gate, hmode, applyOperation, haccepted, installCopiedCapabilities, next] using
              hscheduler
          have hblocking' : BlockingIPC.WellFormed
              { state.blockingIPC with scheduler :=
                { state.scheduler with lifecycle :=
                  { state.lifecycle with capabilities := next } } } := by
            refine ⟨hscheduler', hqueues, ?_, hunique, hindex, ?_, hcapabilities⟩
            · intro endpoint subject hmember
              obtain ⟨hliveEndpoint, ⟨slot, capability, hslot, hobject, hkind,
                hreceive, _⟩, hliveSubject, hrunnable, howner, hcurrent, hready⟩ :=
                hwaiters endpoint subject hmember
              have holdAuthority :
                  Capability.HasAuthority state.capabilities subject endpoint .receive := by
                refine ⟨slot, capability, ?_, hobject, ?_⟩
                · change
                    state.blockingIPC.scheduler.lifecycle.capabilities.slots subject slot =
                      some capability at hslot
                  rw [← hbase] at hslot
                  exact hslot
                · simpa [Capability.hasRight, Capability.permits] using hreceive
              have hnewAuthority :=
                Capability.copy_preserves_authority state.capabilities
                  state.execution.core.context.currentSubject source destination destinationSlot
                  rights subject endpoint .receive holdAuthority
              change Capability.HasAuthority next subject endpoint .receive at hnewAuthority
              obtain ⟨newSlot, newCapability, hnewSlot, hnewObject, hnewReceive⟩ :=
                hnewAuthority
              have holdEndpointKind :
                  state.blockingIPC.scheduler.lifecycle.capabilities.kinds endpoint =
                    some .endpoint := by
                change
                  state.blockingIPC.scheduler.lifecycle.capabilities.slots subject slot =
                    some capability at hslot
                have holdValid := holdCapabilities.1 subject slot capability hslot
                have holdEndpointKindContext :
                    state.blockingIPCContext.ipc.scheduler.lifecycle.capabilities.kinds endpoint =
                      some .endpoint := by
                  simpa [hobject, hkind] using holdValid.2.2.1
                change
                  state.blockingIPC.scheduler.lifecycle.capabilities.kinds endpoint =
                    some .endpoint at holdEndpointKindContext
                exact holdEndpointKindContext
              have hnewValid := hcapabilities.1 subject newSlot newCapability hnewSlot
              have hnewKind : newCapability.kind = .endpoint := by
                have hregistryKind :
                    next.kinds endpoint = some newCapability.kind := by
                  simpa [hnewObject] using hnewValid.2.2.1
                rw [hkinds', holdEndpointKind] at hregistryKind
                exact Option.some.inj hregistryKind.symm
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hobjects']
                exact hliveEndpoint
              · refine ⟨newSlot, newCapability, hnewSlot, hnewObject, hnewKind, ?_, ?_⟩
                · simpa [Capability.hasRight, Capability.permits] using hnewReceive
                · rw [hobjects']
                  exact hliveEndpoint
              · rw [hsubjects']
                exact hliveSubject
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle] using hrunnable
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle, Scheduler.ownsAddressSpace] using howner
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
                  hschedulerLifecycle] using hcurrent
              · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler] using hready
            · intro endpoint envelope hmail
              obtain ⟨hlive, hkind, henvelope, hempty⟩ := hmailbox endpoint envelope hmail
              refine ⟨?_, ?_, henvelope, hempty⟩
              · rw [hobjects']
                exact hlive
              · rw [hkinds']
                exact hkind
          simpa [gate, hmode, applyOperation, haccepted, installCopiedCapabilities,
            CompositeState.blockingIPCContext, BlockingIPCContext.ContextAgreement,
            BlockingIPCContext.WellFormed, next] using And.intro hblocking' hagreement

/-- Publishing a capability state that retains all receive authority carries
the complete blocking invariant.  This is the common cross-subsystem boundary
for direct and transitive revocation: a waiter may move to a different
surviving slot, but it cannot lose its authority to the indexed endpoint. -/
theorem installReceiveAuthorityPreservingCapabilities_preserves_blockingRuntimeWellFormed
    state next
    (hstate : BlockingRuntimeWellFormed state)
    (hglobal : RuntimeWellFormed (installCopiedCapabilities state next))
    (hcapabilities : Capability.WellFormed next)
    (hsubjects : next.subjects = state.capabilities.subjects)
    (hobjects : next.objects = state.capabilities.objects)
    (hkinds : next.kinds = state.capabilities.kinds)
    (hauthority : ∀ subject endpoint,
      Capability.HasAuthority state.capabilities subject endpoint .receive →
        Capability.HasAuthority next subject endpoint .receive) :
    BlockingRuntimeWellFormed (installCopiedCapabilities state next) := by
  refine ⟨hglobal, ?_⟩
  rcases hstate.1.1 with
    ⟨_, hschedulerLifecycle, _, hcapabilitiesCoherent, _, _, _, _, _, _, _⟩
  have hbase : state.capabilities =
      state.blockingIPC.scheduler.lifecycle.capabilities := by
    exact hcapabilitiesCoherent.trans
      (congrArg SubjectLifecycle.State.capabilities hstate.1.blockingLifecycle.symm)
  have hsubjects' : next.subjects =
      state.blockingIPC.scheduler.lifecycle.capabilities.subjects :=
    hsubjects.trans (congrArg Capability.State.subjects hbase)
  have hobjects' : next.objects =
      state.blockingIPC.scheduler.lifecycle.capabilities.objects :=
    hobjects.trans (congrArg Capability.State.objects hbase)
  have hkinds' : next.kinds =
      state.blockingIPC.scheduler.lifecycle.capabilities.kinds :=
    hkinds.trans (congrArg Capability.State.kinds hbase)
  rcases hstate.2 with ⟨hblocking, hagreement⟩
  rcases hblocking with
    ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, holdCapabilities⟩
  rcases hglobal with ⟨_, _, _, _, _, _, hscheduler, _, _, _, _, _, _⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with capabilities := next } } := by
    simpa [installCopiedCapabilities] using hscheduler
  have hblocking' : BlockingIPC.WellFormed
      { state.blockingIPC with scheduler :=
        { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next } } } := by
    refine ⟨hscheduler', hqueues, ?_, hunique, hindex, ?_, hcapabilities⟩
    · intro endpoint subject hmember
      obtain ⟨hliveEndpoint, ⟨slot, capability, hslot, hobject, hkind,
        hreceive, _⟩, hliveSubject, hrunnable, howner, hcurrent, hready⟩ :=
        hwaiters endpoint subject hmember
      have holdAuthority :
          Capability.HasAuthority state.capabilities subject endpoint .receive := by
        refine ⟨slot, capability, ?_, hobject, ?_⟩
        · change
            state.blockingIPC.scheduler.lifecycle.capabilities.slots subject slot =
              some capability at hslot
          rw [← hbase] at hslot
          exact hslot
        · simpa [Capability.hasRight, Capability.permits] using hreceive
      obtain ⟨newSlot, newCapability, hnewSlot, hnewObject, hnewReceive⟩ :=
        hauthority subject endpoint holdAuthority
      have holdEndpointKind :
          state.blockingIPC.scheduler.lifecycle.capabilities.kinds endpoint =
            some .endpoint := by
        have holdValid := holdCapabilities.1 subject slot capability hslot
        have holdEndpointKindContext :
            state.blockingIPCContext.ipc.scheduler.lifecycle.capabilities.kinds endpoint =
              some .endpoint := by
          simpa [hobject, hkind] using holdValid.2.2.1
        change
          state.blockingIPC.scheduler.lifecycle.capabilities.kinds endpoint =
            some .endpoint at holdEndpointKindContext
        exact holdEndpointKindContext
      have hnewValid := hcapabilities.1 subject newSlot newCapability hnewSlot
      have hnewKind : newCapability.kind = .endpoint := by
        have hregistryKind : next.kinds endpoint = some newCapability.kind := by
          simpa [hnewObject] using hnewValid.2.2.1
        rw [hkinds', holdEndpointKind] at hregistryKind
        exact Option.some.inj hregistryKind.symm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hobjects']
        exact hliveEndpoint
      · refine ⟨newSlot, newCapability, hnewSlot, hnewObject, hnewKind, ?_, ?_⟩
        · simpa [Capability.hasRight, Capability.permits] using hnewReceive
        · rw [hobjects']
          exact hliveEndpoint
      · rw [hsubjects']
        exact hliveSubject
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
          hschedulerLifecycle] using hrunnable
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
          hschedulerLifecycle, Scheduler.ownsAddressSpace] using howner
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
          hschedulerLifecycle] using hcurrent
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler] using hready
    · intro endpoint envelope hmail
      obtain ⟨hlive, hkind, henvelope, hempty⟩ := hmailbox endpoint envelope hmail
      refine ⟨?_, ?_, henvelope, hempty⟩
      · rw [hobjects']
        exact hlive
      · rw [hkinds']
        exact hkind
  simpa [installCopiedCapabilities, CompositeState.blockingIPCContext,
    BlockingIPCContext.ContextAgreement, BlockingIPCContext.WellFormed] using
      And.intro hblocking' hagreement


/-- Atomic subtree revocation publication retains the complete blocking
precondition: the finite lineage guard keeps every indexed waiter's receive
authority, and canceling sealed descendants touches no waiter or context. -/
private theorem installRevokedSubtree_preserves_blockingRuntimeWellFormed
    state root next
    (hstate : BlockingRuntimeWellFormed state)
    (hglobal : RuntimeWellFormed (installRevokedSubtree state root next))
    (hcapabilities : Capability.WellFormed next)
    (hsubjects : next.subjects = state.capabilities.subjects)
    (hobjects : next.objects = state.capabilities.objects)
    (hkinds : next.kinds = state.capabilities.kinds)
    (hauthority : ∀ subject endpoint,
      Capability.HasAuthority state.capabilities subject endpoint .receive →
        Capability.HasAuthority next subject endpoint .receive) :
    BlockingRuntimeWellFormed (installRevokedSubtree state root next) := by
  refine ⟨hglobal, ?_⟩
  rcases hstate.1.1 with
    ⟨_, hschedulerLifecycle, _, hcapabilitiesCoherent, _, _, _, _, _, _, _⟩
  have hbase : state.capabilities =
      state.blockingIPC.scheduler.lifecycle.capabilities := by
    exact hcapabilitiesCoherent.trans
      (congrArg SubjectLifecycle.State.capabilities hstate.1.blockingLifecycle.symm)
  have hsubjects' : next.subjects =
      state.blockingIPC.scheduler.lifecycle.capabilities.subjects :=
    hsubjects.trans (congrArg Capability.State.subjects hbase)
  have hobjects' : next.objects =
      state.blockingIPC.scheduler.lifecycle.capabilities.objects :=
    hobjects.trans (congrArg Capability.State.objects hbase)
  have hkinds' : next.kinds =
      state.blockingIPC.scheduler.lifecycle.capabilities.kinds :=
    hkinds.trans (congrArg Capability.State.kinds hbase)
  rcases hstate.2 with ⟨hblocking, hagreement⟩
  rcases hblocking with
    ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, holdCapabilities⟩
  rcases hglobal with ⟨_, _, _, _, _, _, hscheduler, _, _, _, _, _, _⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with capabilities := next } } := by
    simpa [installRevokedSubtree, installTransfers] using hscheduler
  have hblocking' : BlockingIPC.WellFormed
      { state.blockingIPC with scheduler :=
        { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next } } } := by
    refine ⟨hscheduler', hqueues, ?_, hunique, hindex, ?_, hcapabilities⟩
    · intro endpoint subject hmember
      obtain ⟨hliveEndpoint, ⟨slot, capability, hslot, hobject, hkind,
        hreceive, _⟩, hliveSubject, hrunnable, howner, hcurrent, hready⟩ :=
        hwaiters endpoint subject hmember
      have holdAuthority :
          Capability.HasAuthority state.capabilities subject endpoint .receive := by
        refine ⟨slot, capability, ?_, hobject, ?_⟩
        · change
            state.blockingIPC.scheduler.lifecycle.capabilities.slots subject slot =
              some capability at hslot
          rw [← hbase] at hslot
          exact hslot
        · simpa [Capability.hasRight, Capability.permits] using hreceive
      obtain ⟨newSlot, newCapability, hnewSlot, hnewObject, hnewReceive⟩ :=
        hauthority subject endpoint holdAuthority
      have holdEndpointKind :
          state.blockingIPC.scheduler.lifecycle.capabilities.kinds endpoint =
            some .endpoint := by
        have holdValid := holdCapabilities.1 subject slot capability hslot
        have holdEndpointKindContext :
            state.blockingIPCContext.ipc.scheduler.lifecycle.capabilities.kinds endpoint =
              some .endpoint := by
          simpa [hobject, hkind] using holdValid.2.2.1
        change
          state.blockingIPC.scheduler.lifecycle.capabilities.kinds endpoint =
            some .endpoint at holdEndpointKindContext
        exact holdEndpointKindContext
      have hnewValid := hcapabilities.1 subject newSlot newCapability hnewSlot
      have hnewKind : newCapability.kind = .endpoint := by
        have hregistryKind : next.kinds endpoint = some newCapability.kind := by
          simpa [hnewObject] using hnewValid.2.2.1
        rw [hkinds', holdEndpointKind] at hregistryKind
        exact Option.some.inj hregistryKind.symm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hobjects']
        exact hliveEndpoint
      · refine ⟨newSlot, newCapability, hnewSlot, hnewObject, hnewKind, ?_, ?_⟩
        · simpa [Capability.hasRight, Capability.permits] using hnewReceive
        · rw [hobjects']
          exact hliveEndpoint
      · rw [hsubjects']
        exact hliveSubject
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
          hschedulerLifecycle] using hrunnable
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
          hschedulerLifecycle, Scheduler.ownsAddressSpace] using howner
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler,
          hschedulerLifecycle] using hcurrent
      · simpa [CompositeState.blockingIPCContext, hstate.1.blockingScheduler] using hready
    · intro endpoint envelope hmail
      obtain ⟨hlive, hkind, henvelope, hempty⟩ := hmailbox endpoint envelope hmail
      refine ⟨?_, ?_, henvelope, hempty⟩
      · rw [hobjects']
        exact hlive
      · rw [hkinds']
        exact hkind
  simpa [installRevokedSubtree, installTransfers, CompositeState.blockingIPCContext,
    BlockingIPCContext.ContextAgreement, BlockingIPCContext.WellFormed] using
      And.intro hblocking' hagreement

/-- Direct revocation retains the complete blocking precondition.  The
composite-safe guard now rejects removal of receive authority, so every
accepted transition preserves an authority witness for each indexed waiter;
ordinary denials and outer-latch rejection remain literal no-ops. -/
theorem gate_capabilityRevoke_preserves_blockingRuntimeWellFormed state authoritySlot victim
    victimSlot (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases hrevoke : Capability.revokeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim victimSlot with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [gate, hmode, applyOperation, hrevoke] using hstate
          | accepted =>
              have hglobal :=
                (gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state authoritySlot
                  victim victimSlot next hstate.1 hmode hrevoke).1
              obtain ⟨hraw, _⟩ :=
                Capability.revokeRuntimeSafe_accepted_raw state.capabilities
                  state.execution.core.context.currentSubject authoritySlot victim victimSlot
                  next hrevoke
              have hmetadata := Capability.revoke_preserves_metadata state.capabilities
                state.execution.core.context.currentSubject authoritySlot victim victimSlot
              rw [hraw] at hmetadata
              rcases hmetadata with
                ⟨hsubjects, hobjects, hkinds, _hcapacity, _hnext, _hderivations⟩
              have hcapabilities : Capability.WellFormed next := by
                have hold := Capability.revoke_preserves_wellFormed state.capabilities
                  state.execution.core.context.currentSubject authoritySlot victim victimSlot
                  hstate.1.2.2.2.1
                simpa [hraw] using hold
              have hauthority : ∀ subject endpoint,
                  Capability.HasAuthority state.capabilities subject endpoint .receive →
                    Capability.HasAuthority next subject endpoint .receive := by
                intro subject endpoint hold
                exact Capability.revokeRuntimeSafe_accepted_preserves_critical_authority
                  state.capabilities state.execution.core.context.currentSubject authoritySlot
                  victim victimSlot next hrevoke subject endpoint .receive
                  (by exact Or.inr (Or.inr (Or.inr rfl))) hold
              have hinstalled :=
                installReceiveAuthorityPreservingCapabilities_preserves_blockingRuntimeWellFormed
                  state next hstate
                  (by simpa [gate, hmode, applyOperation, hrevoke] using hglobal)
                  hcapabilities hsubjects hobjects hkinds hauthority
              simpa [gate, hmode, applyOperation, hrevoke] using hinstalled

/-- Transitive revocation satisfies the same waiter-authority boundary.  The
finite lineage guard rejects any subtree containing receive authority, while
accepted removal preserves every indexed waiter's endpoint authorization. -/
theorem gate_capabilityRevokeSubtree_preserves_blockingRuntimeWellFormed state authoritySlot
    victim victimSlot (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases hrevoke : Capability.revokeSubtreeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim victimSlot with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [gate, hmode, applyOperation, hrevoke] using hstate
          | accepted =>
              have hglobal :=
                (gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state
                  authoritySlot victim victimSlot next hstate.1 hmode hrevoke).1
              obtain ⟨hraw, _⟩ :=
                Capability.revokeSubtreeRuntimeSafe_accepted_raw state.capabilities
                  state.execution.core.context.currentSubject authoritySlot victim victimSlot
                  next hrevoke
              have hmetadata := Capability.revokeSubtree_preserves_metadata state.capabilities
                state.execution.core.context.currentSubject authoritySlot victim victimSlot
              rw [hraw] at hmetadata
              rcases hmetadata with
                ⟨hsubjects, hobjects, hkinds, _hcapacity, _hnext, _hderivations⟩
              have hcapabilities : Capability.WellFormed next := by
                have hold := Capability.revokeSubtree_preserves_wellFormed state.capabilities
                  state.execution.core.context.currentSubject authoritySlot victim victimSlot
                  hstate.1.2.2.2.1
                simpa [hraw] using hold
              have hauthority : ∀ subject endpoint,
                  Capability.HasAuthority state.capabilities subject endpoint .receive →
                    Capability.HasAuthority next subject endpoint .receive := by
                intro subject endpoint hold
                exact Capability.revokeSubtreeRuntimeSafe_accepted_preserves_critical_authority
                  state.capabilities state.execution.core.context.currentSubject authoritySlot
                  victim victimSlot next hstate.1.2.2.2.1 hrevoke subject endpoint .receive
                  (by exact Or.inr (Or.inr (Or.inr rfl))) hold
              obtain ⟨target, hlookup, _hclear⟩ :=
                Capability.revokeSubtreeRuntimeSafe_accepted_target state.capabilities
                  state.execution.core.context.currentSubject authoritySlot victim victimSlot
                  next hrevoke
              have hinstalled :=
                installRevokedSubtree_preserves_blockingRuntimeWellFormed
                  state target.identity next hstate
                  (by simpa [gate, hmode, applyOperation, hrevoke, hlookup] using hglobal)
                  hcapabilities hsubjects hobjects hkinds hauthority
              simpa [gate, hmode, applyOperation, hrevoke, hlookup] using hinstalled

/-- Fresh-subject publication retains the complete blocking precondition.
Creation only promotes one monotonic lifecycle identity; every existing waiter,
mailbox, scheduler member, and saved context keeps the same authority and
index. Typed denials and outer-latch rejection are literal no-ops. -/
theorem gate_createSubject_preserves_blockingRuntimeWellFormed state subject
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state (.createSubject subject)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases hcreate : SubjectLifecycle.create state.lifecycle subject with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [gate, hmode, applyOperation, hcreate] using hstate
          | accepted =>
              have hglobal :=
                createSubject_operationPreservesRuntimeWellFormed subject state hstate.1
              refine ⟨hglobal, ?_⟩
              rcases hstate.2 with ⟨hblocking, hagreement⟩
              change BlockingIPC.WellFormed state.blockingIPC at hblocking
              rcases hblocking with
                ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, _⟩
              rcases hglobal with
                ⟨_, _, _, hcapabilities, _, _, hscheduler, _, _, _, _, _, _, _⟩
              have hblockingScheduler :
                  state.blockingIPC.scheduler = state.scheduler :=
                hstate.1.blockingScheduler
              have hblockingLifecycle :
                  state.blockingIPC.scheduler.lifecycle = state.lifecycle :=
                hstate.1.blockingLifecycle
              have hslots :
                  next.capabilities.slots = state.lifecycle.capabilities.slots := by
                have hold := congrArg
                  (fun outcome => outcome.state.capabilities.slots) hcreate
                exact hold.symm.trans (createSubject_slots state.lifecycle subject)
              have hobjects :
                  next.capabilities.objects = state.lifecycle.capabilities.objects := by
                have hold := congrArg
                  (fun outcome => outcome.state.capabilities.objects) hcreate
                exact hold.symm.trans (createSubject_objects state.lifecycle subject)
              have hkinds :
                  next.capabilities.kinds = state.lifecycle.capabilities.kinds := by
                have hold := congrArg
                  (fun outcome => outcome.state.capabilities.kinds) hcreate
                exact hold.symm.trans (createSubject_kinds state.lifecycle subject)
              have hrunnableEq :
                  next.runnable = state.lifecycle.runnable := by
                have hold := congrArg (fun outcome => outcome.state.runnable) hcreate
                exact hold.symm.trans (createSubject_runnable state.lifecycle subject)
              have haddressOwner :
                  next.addressOwner = state.lifecycle.addressOwner := by
                have hold := congrArg (fun outcome => outcome.state.addressOwner) hcreate
                exact hold.symm.trans (createSubject_addressOwner state.lifecycle subject)
              have hcurrentEq :
                  next.current = state.lifecycle.current := by
                have hold := congrArg (fun outcome => outcome.state.current) hcreate
                exact hold.symm.trans (createSubject_current state.lifecycle subject)
              have hblocking' : BlockingIPC.WellFormed
                  (gate state (.createSubject subject)).state.blockingIPC := by
                simp only [gate, hmode, applyOperation, hcreate, installCreatedSubject]
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                    hscheduler
                · simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                    hqueues
                · intro endpoint waiter hmember
                  have hmember' : waiter ∈ state.blockingIPC.waiters endpoint := by
                    simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                      hmember
                  obtain ⟨hliveEndpoint, ⟨slot, capability, hslot, hobject, hkind,
                    hreceive, _⟩, hliveWaiter, hrunnable, howner, hcurrent, hready⟩ :=
                    hwaiters endpoint waiter hmember'
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · rw [hobjects, ← hblockingLifecycle]
                    exact hliveEndpoint
                  · refine ⟨slot, capability, ?_, hobject, hkind, hreceive, ?_⟩
                    · rw [hslots, ← hblockingLifecycle]
                      exact hslot
                    · rw [hobjects, ← hblockingLifecycle]
                      exact hliveEndpoint
                  · have hold := createSubject_preserves_live
                      state.lifecycle subject waiter (by
                        rw [← hblockingLifecycle]
                        exact hliveWaiter)
                    rw [hcreate] at hold
                    exact hold
                  · rw [hrunnableEq, ← hblockingLifecycle]
                    exact hrunnable
                  · simpa [Scheduler.ownsAddressSpace, haddressOwner,
                      ← hblockingLifecycle] using howner
                  · rw [hcurrentEq, ← hblockingLifecycle]
                    exact hcurrent
                  · simpa [hblockingScheduler] using hready
                · simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                    hunique
                · simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                    hindex
                · intro endpoint envelope hmail
                  have hmail' : state.blockingIPC.mailbox endpoint = some envelope := by
                    simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                      hmail
                  obtain ⟨hlive, hkind, henvelope, hempty⟩ :=
                    hmailbox endpoint envelope hmail'
                  refine ⟨?_, ?_, henvelope, ?_⟩
                  · rw [hobjects, ← hblockingLifecycle]
                    exact hlive
                  · rw [hkinds, ← hblockingLifecycle]
                    exact hkind
                  · simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                      hempty
                · simpa [gate, hmode, applyOperation, hcreate, installCreatedSubject] using
                    hcapabilities
              refine ⟨hblocking', ?_⟩
              simpa [CompositeState.blockingIPCContext,
                BlockingIPCContext.ContextAgreement, gate, hmode, applyOperation,
                hcreate, installCreatedSubject] using hagreement

/-- Scheduler admission is readiness-free at the blocking boundary.  A
successful admission appends only a runnable subject with an already-staged
kernel context; every indexed waiter is non-runnable, so no waiter can be the
new ready member.  Rejections and outer-latch denials remain literal no-ops. -/
theorem gate_scheduleAdd_preserves_blockingRuntimeWellFormed state subject
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state (.scheduleAdd subject)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      cases hadmission : schedulerAdmission state subject with
      | mk next result =>
          cases result with
          | rejected reason =>
              have hunchanged := schedulerAdmission_rejected_unchanged
                state subject reason (by simp [hadmission])
              simpa [gate, hmode, applyOperation, hadmission, hunchanged] using hstate
          | accepted context =>
              obtain ⟨hnotRetained, hadd, saved, hmember, howner⟩ :=
                schedulerAdmission_accepted_exact state subject context next hadmission
              have hglobal :=
                (gate_scheduleAdd_accepted_preserves_runtimeWellFormed
                  state subject context next saved hstate.1 hmode hadd
                    ⟨hmember, howner⟩ hnotRetained).1
              refine ⟨hglobal, ?_⟩
              rcases hstate.2 with ⟨hblocking, hagreement⟩
              change BlockingIPC.WellFormed state.blockingIPC at hblocking
              rcases hblocking with
                ⟨_, hqueues, hwaiters, hunique, hindex, hmailbox, hcapabilities⟩
              obtain ⟨hlifecycle, hready⟩ :=
                schedulerAdd_accepted_projections state.scheduler subject context next hadd
              have hscheduler : Scheduler.WellFormed next := by
                have hold := Scheduler.add_preserves_wellFormed
                  state.scheduler subject hstate.1.2.2.2.2.2.2.1
                simpa [hadd] using hold
              have hblocking' : BlockingIPC.WellFormed
                  (gate state (.scheduleAdd subject)).state.blockingIPC := by
                simp only [gate, hmode, applyOperation, hadmission,
                  installSchedulerAdmission]
                refine ⟨hscheduler, hqueues, ?_, hunique, hindex, ?_, ?_⟩
                · intro endpoint waiter hwaiter
                  obtain ⟨hliveEndpoint, hauthority, hliveWaiter, hblocked,
                    howns, hnotCurrent, hnotReady⟩ :=
                      hwaiters endpoint waiter hwaiter
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa [hlifecycle, hstate.1.blockingScheduler] using hliveEndpoint
                  · simpa [BlockingIPC.authorizedReceive, hlifecycle,
                      hstate.1.blockingScheduler] using hauthority
                  · simpa [hlifecycle, hstate.1.blockingScheduler] using hliveWaiter
                  · simpa [hlifecycle, hstate.1.blockingScheduler] using hblocked
                  · simpa [Scheduler.ownsAddressSpace, hlifecycle,
                      hstate.1.blockingScheduler] using howns
                  · simpa [hlifecycle, hstate.1.blockingScheduler] using hnotCurrent
                  · rw [hready]
                    intro hmember'
                    rcases List.mem_append.mp hmember' with hold | hold
                    · apply hnotReady
                      simpa [hstate.1.blockingScheduler] using hold
                    · simp only [List.mem_singleton] at hold
                      subst waiter
                      have hrunnable :
                          next.lifecycle.runnable subject = true :=
                        (hscheduler.2.2.2.1 subject (by simp [hready])).2.1
                      rw [hlifecycle, ← hstate.1.blockingScheduler] at hrunnable
                      simp [hblocked] at hrunnable
                · simpa [hlifecycle, hstate.1.blockingScheduler] using hmailbox
                · simpa [hlifecycle, hstate.1.blockingScheduler] using hcapabilities
              refine ⟨hblocking', ?_⟩
              simpa [CompositeState.blockingIPCContext,
                BlockingIPCContext.ContextAgreement, gate, hmode, applyOperation,
                hadmission, installSchedulerAdmission] using hagreement

/-- A scheduler tick preserves every lifecycle field observed by blocked
waiters and cannot rotate a subject disjoint from both current and ready into
either selected position. -/
private theorem schedulerTick_preserves_blockedView scheduler subject
    (hcurrent : scheduler.lifecycle.current ≠ some subject)
    (hready : subject ∉ scheduler.ready) :
    let next := (Scheduler.tick scheduler).state
    next.lifecycle.capabilities = scheduler.lifecycle.capabilities ∧
      next.lifecycle.runnable = scheduler.lifecycle.runnable ∧
      next.lifecycle.addressOwner = scheduler.lifecycle.addressOwner ∧
      next.lifecycle.current ≠ some subject ∧
      subject ∉ next.ready := by
  generalize htick : Scheduler.tick scheduler = outcome
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason =>
          have hnext := Scheduler.tick_rejected_unchanged scheduler reason (by simp [htick])
          rw [htick] at hnext
          change next = scheduler at hnext
          subst next
          exact ⟨rfl, rfl, rfl, hcurrent, hready⟩
      | accepted context =>
          simp only [Scheduler.tick, Scheduler.yield] at htick
          split at htick <;> try simp_all [Scheduler.reject]
          split at htick <;> try simp_all [Scheduler.reject]
          generalize hselect : Scheduler.selectNext _ = selected at htick
          cases selected with
          | mk selectedState selectedResult =>
              cases selectedResult with
              | rejected reason => simp [Scheduler.reject] at htick
              | accepted selectedContext =>
                  injection htick with hstate _
                  subst next
                  simp only [Scheduler.selectNext] at hselect
                  split at hselect <;> try simp_all [Scheduler.reject]
                  split at hselect <;> try simp_all [Scheduler.reject]
                  rcases hselect with ⟨rfl, _⟩
                  grind

/-- A resumable switch cannot select or save a subject that was neither the
current subject nor a member of the ready queue.  Therefore an existing
absence from the kernel-owned context bank remains an absence after every
accepted switch, typed rejection, and fatal entry. -/
theorem resumeSwitch_preserves_quiescent_context_absence
    state interruptState frame registers subject
    (hcurrent : state.scheduler.lifecycle.current ≠ some subject)
    (hready : subject ∉ state.scheduler.ready)
    (habsent : ResumablePreemption.contextFor state.contexts subject = none) :
    ResumablePreemption.contextFor
      (ResumablePreemption.switch state interruptState frame registers).state.contexts
      subject = none := by
  have hschedulerView :=
    schedulerTick_preserves_blockedView state.scheduler subject hcurrent hready
  simp only [ResumablePreemption.switch]
  split <;> try simp_all [ResumablePreemption.reject, ResumablePreemption.halt]
  split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals
    simp_all [ResumablePreemption.contextFor, ResumablePreemption.eraseContext]

/-- The scheduler projection of a resumable switch leaves a quiescent subject
quiescent.  Rejections and fatal entry preserve the scheduler literally;
accepted switching publishes exactly the scheduler tick covered above. -/
theorem resumeSwitch_preserves_quiescent_scheduler_view
    state interruptState frame registers subject
    (hcurrent : state.scheduler.lifecycle.current ≠ some subject)
    (hready : subject ∉ state.scheduler.ready) :
    let next :=
      (ResumablePreemption.switch state interruptState frame registers).state.scheduler
    next.lifecycle.capabilities = state.scheduler.lifecycle.capabilities ∧
      next.lifecycle.runnable = state.scheduler.lifecycle.runnable ∧
      next.lifecycle.addressOwner = state.scheduler.lifecycle.addressOwner ∧
      next.lifecycle.current ≠ some subject ∧
      subject ∉ next.ready := by
  have hschedulerView :=
    schedulerTick_preserves_blockedView state.scheduler subject hcurrent hready
  simp only [ResumablePreemption.switch]
  split <;> try simp_all [ResumablePreemption.reject, ResumablePreemption.halt]
  split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals
    exact hschedulerView

/-- A scheduler tick cannot make an existing endpoint waiter runnable, current,
or ready.  The tick rotates only the old current subject and the existing ready
queue, both of which are disjoint from every well-formed waiter. -/
private theorem blockingIPC_wellFormed_tick (state : BlockingIPC.State)
    (hstate : BlockingIPC.WellFormed state) :
    BlockingIPC.WellFormed
      { state with scheduler := (Scheduler.tick state.scheduler).state } := by
  rcases hstate with
    ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcapabilities⟩
  have hscheduler' := Scheduler.tick_preserves_wellFormed state.scheduler hscheduler
  refine ⟨hscheduler', hqueues, ?_, hunique, hindex, ?_, ?_⟩
  · intro endpoint subject hmember
    obtain ⟨hliveEndpoint, hauthority, hliveSubject, hrunnable, howner,
      hcurrent, hready⟩ := hwaiters endpoint subject hmember
    obtain ⟨hcapabilities, hrunnable', haddressOwner, hcurrent', hready'⟩ :=
      schedulerTick_preserves_blockedView state.scheduler subject hcurrent hready
    refine ⟨?_, ?_, ?_, ?_, ?_, hcurrent', hready'⟩
    · rw [hcapabilities]
      exact hliveEndpoint
    · simpa [BlockingIPC.authorizedReceive, hcapabilities] using hauthority
    · rw [hcapabilities]
      exact hliveSubject
    · rw [hrunnable']
      exact hrunnable
    · simpa [Scheduler.ownsAddressSpace, haddressOwner] using howner
  · intro endpoint envelope hvalue
    obtain ⟨hlive, hkind, henvelope, hempty⟩ := hmailbox endpoint envelope hvalue
    have hcapabilities := schedulerTick_preserves_capabilities state.scheduler
    exact ⟨by simpa [hcapabilities] using hlive,
      by simpa [hcapabilities] using hkind, henvelope, hempty⟩
  · simpa [schedulerTick_preserves_capabilities state.scheduler] using hcapabilities

/-- A successful save/restore switch publishes exactly the scheduler tick, so
the waiter-disjoint rotation lemma applies to its blocking projection. -/
private theorem resumeSwitch_noError_preserves_blockingIPCWellFormed
    (state : CompositeState) frame registers
    (herror : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).error = none)
    (hscheduler : state.resumable.scheduler = state.blockingIPC.scheduler)
    (hstate : BlockingIPC.WellFormed state.blockingIPC) :
    BlockingIPC.WellFormed
      { state.blockingIPC with scheduler :=
        (ResumablePreemption.switch state.resumable state.execution.core
          frame registers).state.scheduler } := by
  simp only [ResumablePreemption.switch] at herror ⊢
  split <;> try simp_all [ResumablePreemption.reject, ResumablePreemption.halt]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals simpa [hscheduler] using blockingIPC_wellFormed_tick state.blockingIPC hstate

/-- The complete resumable-preemption family retains the stronger blocking
runtime precondition without a readiness witness.  A subsequent block, wake,
or cancellation can therefore execute immediately after any restored switch,
typed denial, fatal entry, or outer-latch rejection. -/
theorem gate_resumePreempt_preserves_blockingRuntimeWellFormed state frame registers
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.resumePreempt frame registers)).state := by
  constructor
  · exact resumePreempt_operationPreservesRuntimeWellFormed frame registers state hstate.1
  · constructor
    · cases hmode : state.execution.mode with
      | handling active => simpa [gate, hmode] using hstate.2.1
      | halted record => simpa [gate, hmode] using hstate.2.1
      | running =>
          cases herror : (ResumablePreemption.switch state.resumable
              state.execution.core frame registers).error with
          | none =>
              have hresumable : state.resumable.scheduler = state.scheduler :=
                hstate.1.1.2.2.2.2.2.2.2.1
              have hscheduler : state.resumable.scheduler = state.blockingIPC.scheduler :=
                hresumable.trans hstate.1.blockingScheduler.symm
              simpa [gate, hmode, applyOperation, herror, installResumable,
                CompositeState.blockingIPCContext, BlockingIPCContext.WellFormed] using
                resumeSwitch_noError_preserves_blockingIPCWellFormed
                  state frame registers herror hscheduler hstate.2.1
          | some reason =>
              cases reason with
              | fatalEntry =>
                  cases hhalted : (ResumablePreemption.switch state.resumable
                      state.execution.core frame registers).state.halted with
                  | false =>
                      simpa [gate, hmode, applyOperation, herror, hhalted] using hstate.2.1
                  | true =>
                      have hscheduler := resumeSwitch_halted_preserves_scheduler
                        state.resumable state.execution.core frame registers hhalted
                      have hresumable : state.resumable.scheduler = state.scheduler :=
                        hstate.1.1.2.2.2.2.2.2.2.1
                      have hscheduler' :
                          (ResumablePreemption.switch state.resumable state.execution.core
                            frame registers).state.scheduler = state.blockingIPC.scheduler :=
                        hscheduler.trans (hresumable.trans hstate.1.blockingScheduler.symm)
                      simpa [gate, hmode, applyOperation, herror, hhalted, installResumable,
                        CompositeState.blockingIPCContext, BlockingIPCContext.WellFormed,
                        hscheduler'] using hstate.2.1
              | nonTimer | malformedIncoming | noCurrent | contextMismatch | duplicateSave |
                  staleActiveSpace | bankFull | schedulerRejected | noDestination |
                  staleDestination =>
                    simpa [gate, hmode, applyOperation, herror] using hstate.2.1
    · exact gate_preserves_blockingContextAgreement state
        (.resumePreempt frame registers) hstate.2.2

/-- Every inbound interrupt result except contained subject cleanup retains the
complete blocking precondition.  Ordinary entry changes only the execution
latch, fatal entry republishes the unchanged authoritative scheduler under the
terminal resumable latch, and outer-latch rejection is literal absorption.

Contained user faults are deliberately excluded here: retiring a subject can
also retire endpoint objects on which other subjects are waiting, so that
branch must cancel every newly unauthorized waiter before it can satisfy the
same readiness-free conclusion. -/
theorem gate_interrupt_noncontained_preserves_blockingRuntimeWellFormed
    state frame
    (hnoncontained : ∀ subject,
      (dispatchHardware state.execution frame).action ≠ .contained subject)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state (.interrupt frame)).state := by
  constructor
  · exact interrupt_operationPreservesRuntimeWellFormed frame state hstate.1
  · cases hmode : state.execution.mode with
    | handling active => simpa [gate, hmode] using hstate.2
    | halted record => simpa [gate, hmode] using hstate.2
    | running =>
        let entry := dispatchHardware state.execution frame
        cases haction : entry.action with
        | contained subject =>
            exact False.elim (hnoncontained subject (by simpa [entry] using haction))
        | fatal reason =>
            have hscheduler : state.resumable.scheduler = state.blockingIPC.scheduler :=
              hstate.1.1.2.2.2.2.2.2.2.1.trans hstate.1.blockingScheduler.symm
            simpa [gate, hmode, applyOperation, entry, haction, installResumable,
              hscheduler, CompositeState.blockingIPCContext] using hstate.2
        | timer =>
            simpa [gate, hmode, applyOperation, entry, haction,
              CompositeState.blockingIPCContext] using hstate.2
        | syscall =>
            simpa [gate, hmode, applyOperation, entry, haction,
              CompositeState.blockingIPCContext] using hstate.2
        | rejected reason =>
            simpa [gate, hmode, applyOperation, entry, haction,
              CompositeState.blockingIPCContext] using hstate.2
        | alreadyHalted record =>
            simpa [gate, hmode, applyOperation, entry, haction] using hstate.2

/-- Every non-contained interrupt outcome also retains the complete deferred
cancellation classification.  Fatal entry changes only the execution and
resumable halt latches; timer, syscall, rejected, and already-halted outcomes
leave the waiter, saved-context, retained-context, and resumable banks exact. -/
theorem gate_interrupt_noncontained_preserves_deferredBlockingRuntimeWellFormed
    state frame
    (hnoncontained : ∀ subject,
      (dispatchHardware state.execution frame).action ≠ .contained subject)
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed (gate state (.interrupt frame)).state := by
  constructor
  · exact (gate_interrupt_noncontained_preserves_blockingRuntimeWellFormed
      state frame hnoncontained ⟨hstate.1, hstate.2.1.1⟩).1
  · cases hmode : state.execution.mode with
    | handling active => simpa [gate, hmode] using hstate.2
    | halted record => simpa [gate, hmode] using hstate.2
    | running =>
        let entry := dispatchHardware state.execution frame
        cases haction : entry.action with
        | contained subject =>
            exact False.elim (hnoncontained subject (by simpa [entry] using haction))
        | fatal reason =>
            have hscheduler : state.resumable.scheduler = state.blockingIPC.scheduler :=
              hstate.1.1.2.2.2.2.2.2.2.1.trans hstate.1.blockingScheduler.symm
            simpa [gate, hmode, applyOperation, entry, haction, installResumable,
              hscheduler,
              CompositeState.DeferredCancellationWellFormed,
              CompositeState.blockingIPCContext] using hstate.2
        | timer =>
            simpa [gate, hmode, applyOperation, entry, haction,
              CompositeState.DeferredCancellationWellFormed,
              CompositeState.blockingIPCContext] using hstate.2
        | syscall =>
            simpa [gate, hmode, applyOperation, entry, haction,
              CompositeState.DeferredCancellationWellFormed,
              CompositeState.blockingIPCContext] using hstate.2
        | rejected reason =>
            simpa [gate, hmode, applyOperation, entry, haction,
              CompositeState.DeferredCancellationWellFormed,
              CompositeState.blockingIPCContext] using hstate.2
        | alreadyHalted record =>
            simpa [gate, hmode, applyOperation, entry, haction] using hstate.2

/-- The complete interrupt family preserves the deferred blocking runtime.
The trusted execution/lifecycle binding is consumed only by the contained
user-fault branch; all other typed outcomes preserve the same invariant
without an additional readiness fact. -/
theorem gate_interrupt_preserves_deferredBlockingRuntimeWellFormed
    state frame
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed (gate state (.interrupt frame)).state := by
  by_cases hcontained :
      ∃ subject, (dispatchHardware state.execution frame).action = .contained subject
  · obtain ⟨subject, haction⟩ := hcontained
    have hmode : state.execution.mode = .running := by
      cases hmode : state.execution.mode with
      | handling active => simp [dispatchHardware, hmode, halt] at haction
      | halted record => simp [dispatchHardware, hmode] at haction
      | running => rfl
    by_cases hcurrent : state.lifecycle.current = some subject
    · have hpreserved :=
        publishInterruptCleanup_preserves_deferredBlockingRuntimeWellFormed
          state subject hstate hcurrent hmode
      simpa [gate, hmode, applyOperation, haction, hcurrent] using hpreserved
    · simpa [gate, hmode, applyOperation, haction, hcurrent] using hstate
  · exact gate_interrupt_noncontained_preserves_deferredBlockingRuntimeWellFormed
      state frame (fun subject haction => hcontained ⟨subject, haction⟩) hstate

/-- Out-of-band NMI fail-stop retains the complete deferred blocking runtime.
The terminal step changes only the execution latch and resumable halt bit; the
authoritative scheduler, waiter/context store, retained cancellations, and
resumable context bank remain exact.  An already-halted NMI is absorbed. -/
theorem gate_nmi_preserves_deferredBlockingRuntimeWellFormed
    state raw context
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed (gate state (.nmi raw context)).state := by
  constructor
  · cases hmode : state.execution.mode with
    | halted record => simpa [gate, hmode] using hstate.1
    | running | handling =>
        simpa [gate, hmode] using
          applyNmi_preserves_runtimeWellFormed state raw context hstate.1
  · cases hmode : state.execution.mode with
    | halted record => simpa [gate, hmode] using hstate.2
    | running | handling =>
        simpa [gate, hmode, applyOperation,
          CompositeState.DeferredCancellationWellFormed,
          CompositeState.blockingIPCContext] using hstate.2

/-- Ordinary operations currently known to retain the complete blocking
runtime invariant.  Neutral control/data-IPC steps keep the blocking state
literal; raw and syscall mapping use the scheduler replacement law above;
sealed offers preserve every registry observed by existing waiters. -/
inductive BlockingRuntimePreservingOperation : Operation → Prop where
  | neutral {operation} (hoperation : BlockingStateNeutralOperation operation) :
      BlockingRuntimePreservingOperation operation
  | map slot page permissions :
      BlockingRuntimePreservingOperation (.map slot page permissions)
  | unmap page : BlockingRuntimePreservingOperation (.unmap page)
  | protect page permissions :
      BlockingRuntimePreservingOperation (.protect page permissions)
  | syscall call : BlockingRuntimePreservingOperation (.syscall call)
  | transferOffer endpointWord sourceWord sourceKind payload rights :
      BlockingRuntimePreservingOperation
        (.transferOffer endpointWord sourceWord sourceKind payload rights)
  | transferAccept endpointWord destinationSlot :
      BlockingRuntimePreservingOperation (.transferAccept endpointWord destinationSlot)
  | capabilityCopy source destination destinationSlot rights :
      BlockingRuntimePreservingOperation
        (.capabilityCopy source destination destinationSlot rights)
  | capabilityRevoke authoritySlot victim victimSlot :
      BlockingRuntimePreservingOperation
        (.capabilityRevoke authoritySlot victim victimSlot)
  | capabilityRevokeSubtree authoritySlot victim victimSlot :
      BlockingRuntimePreservingOperation
        (.capabilityRevokeSubtree authoritySlot victim victimSlot)
  | createSubject subject : BlockingRuntimePreservingOperation (.createSubject subject)
  | scheduleAdd subject : BlockingRuntimePreservingOperation (.scheduleAdd subject)
  | resumePreempt frame registers :
      BlockingRuntimePreservingOperation (.resumePreempt frame registers)

theorem gate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
    state operation (hoperation : BlockingRuntimePreservingOperation operation)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state operation).state := by
  cases hoperation with
  | neutral hneutral =>
      exact gate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
        state operation hneutral hstate
  | map slot page permissions =>
      exact gate_map_preserves_blockingRuntimeWellFormed
        state slot page permissions hstate
  | unmap page => exact gate_unmap_preserves_blockingRuntimeWellFormed state page hstate
  | protect page permissions =>
      exact gate_protect_preserves_blockingRuntimeWellFormed
        state page permissions hstate
  | syscall call => exact gate_syscall_preserves_blockingRuntimeWellFormed state call hstate
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact gate_transferOffer_preserves_blockingRuntimeWellFormed state endpointWord sourceWord
        sourceKind payload rights hstate
  | transferAccept endpointWord destinationSlot =>
      exact gate_transferAccept_preserves_blockingRuntimeWellFormed
        state endpointWord destinationSlot hstate
  | capabilityCopy source destination destinationSlot rights =>
      exact gate_capabilityCopy_preserves_blockingRuntimeWellFormed state source destination
        destinationSlot rights hstate
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact gate_capabilityRevoke_preserves_blockingRuntimeWellFormed state authoritySlot victim
        victimSlot hstate
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact gate_capabilityRevokeSubtree_preserves_blockingRuntimeWellFormed state authoritySlot
        victim victimSlot hstate
  | createSubject subject =>
      exact gate_createSubject_preserves_blockingRuntimeWellFormed state subject hstate
  | scheduleAdd subject =>
      exact gate_scheduleAdd_preserves_blockingRuntimeWellFormed state subject hstate
  | resumePreempt frame registers =>
      exact gate_resumePreempt_preserves_blockingRuntimeWellFormed state frame registers hstate

theorem dispatchHardware_deterministic state frame first second
    (hfirst : dispatchHardware state frame = first)
    (hsecond : dispatchHardware state frame = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem dispatchHardware_preserves_wellFormed state frame (hstate : WellFormed state) :
    WellFormed (dispatchHardware state frame).state := by
  rcases hstate with ⟨hlifecycle, hbound, hmodeWellFormed⟩
  change SubjectLifecycle.WellFormed state.core.lifecycle at hlifecycle
  cases hmode : state.mode with
  | handling active =>
      simp only [hmode] at hmodeWellFormed
      simpa [dispatchHardware, hmode, halt, WellFormed, Interrupt.WellFormed] using
        And.intro hlifecycle hmodeWellFormed.2
  | halted record =>
      simpa [dispatchHardware, hmode, WellFormed, Interrupt.WellFormed] using
        And.intro hlifecycle (And.intro hbound hmodeWellFormed)
  | running =>
      simp only [hmode] at hmodeWellFormed
      simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
      unfold Interrupt.dispatchHardware
      cases hvector : Interrupt.decodeVector frame.vector with
      | none => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
      | some vector =>
          cases vector with
          | pageFault =>
              cases frame.savedPrivilege with
              | kernel => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
              | user =>
                  simpa [hvector, WellFormed, Interrupt.WellFormed] using
                    SubjectLifecycle.terminateState_preserves_wellFormed
                      state.core.lifecycle state.core.context.currentSubject hlifecycle
          | timer => simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
          | syscall =>
              cases frame.savedPrivilege <;>
                simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle

theorem attacker_registers_cannot_change_dispatch state frame first second :
    dispatch state { hardware := frame, registers := first } =
      dispatch state { hardware := frame, registers := second } := by
  rfl

theorem halted_entry_absorbing state record frame
    (hmode : state.mode = .halted record) :
    dispatchHardware state frame = { state, action := .alreadyHalted record } := by
  simp [dispatchHardware, hmode]

theorem halted_gate_absorbing state record operation
    (hmode : state.execution.mode = .halted record) :
    gate state operation = { state, result := .rejectedHalted record } := by
  cases operation <;> simp [gate, hmode]

theorem halted_suffix_absorbing state record proposals
    (hmode : state.execution.mode = .halted record) :
    runOperations state proposals = state := by
  induction proposals generalizing state with
  | nil => rfl
  | cons proposal rest ih =>
      simp only [runOperations]
      rw [halted_gate_absorbing state record proposal hmode]
      exact ih state hmode

/-- A rejected live PCI snapshot enters the same fatal latch used by the
ordinary composite gate, so every later public-operation suffix is absorbed
byte-for-byte. -/
theorem observeDMAControl_invalid_suffix_absorbing state snapshot reason proposals
    (hrunning : state.execution.mode = .running)
    (hinvalid : DMAQuarantine.validate snapshot = .rejected reason) :
    let next := (observeDMAControl state snapshot).state
    next.execution.mode =
        .halted (dmaHaltRecord .dmaInvalidControlSnapshot) ∧
      runOperations next proposals = next := by
  rw [observeDMAControl_invalid_exact_fatal state snapshot reason hrunning hinvalid]
  dsimp [latchDMAControlFailure]
  constructor
  · rfl
  · exact halted_suffix_absorbing _ _ proposals rfl

/-- A valid-but-different PCI snapshot has the distinct diagnostic reason and
the same exact fatal absorption property. -/
theorem observeDMAControl_changed_suffix_absorbing state snapshot accepted proposals
    (hrunning : state.execution.mode = .running)
    (hvalid : DMAQuarantine.validate snapshot = .accepted accepted)
    (hchanged : snapshot ≠ state.dmaAccepted.snapshot) :
    let next := (observeDMAControl state snapshot).state
    next.execution.mode =
        .halted (dmaHaltRecord .dmaControlSnapshotChanged) ∧
      runOperations next proposals = next := by
  rw [observeDMAControl_changed_exact_fatal state snapshot accepted
    hrunning hvalid hchanged]
  dsimp [latchDMAControlFailure]
  constructor
  · rfl
  · exact halted_suffix_absorbing _ _ proposals rfl

end LeanOS.FailStop
