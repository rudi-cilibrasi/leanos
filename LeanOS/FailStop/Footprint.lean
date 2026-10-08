import LeanOS.FailStop.Operations

/-!
# Fail-stop composite: operation footprints and the frame rule

Every typed `Operation` declares its footprint: the composite projections it
reads and the subset it may write (`Operation.footprint`).  The frame theorem
`applyOperation_frames` proves that every projection outside the declared
write set is literally unchanged by `applyOperation`.

The proof is assembled from one frame lemma per publication helper
(`installLifecycle_frames`, `installTransfers_frames`, ...).  Each helper lemma
is discharged by case analysis on `CompositeFootprint.Projection`, so adding a
projection to `CompositeState` adds one automatically discharged case to each
helper lemma rather than a re-proof of any whole-state theorem.  Theorems
about a projection that an operation does not write are then lifted through
`applyOperation_project_untouched` and `applyOperation_preserves_of_dependsOn`
instead of being re-proved per operation.
-/
namespace LeanOS.FailStop

open LeanOS
open LeanOS.CompositeFootprint (Projection Footprint)
set_option linter.unusedSimpArgs false

/-! ## Named projection groups -/

/-- Projections republished by a capability, lifecycle, or transfer
publication: every consumer of the shared lifecycle and capability registry. -/
def publicationProjections : List Projection :=
  [ .execution, .scheduler, .preemption, .virtualMemory, .ipc, .capabilities
  , .lifecycle, .resumable, .transfers, .blockingIPC ]

/-- Projections republished by subject cleanup: the full publication group plus
the blocking-context bank and deferred cancellations. -/
def cleanupProjections : List Projection :=
  publicationProjections ++ [.blockingContexts, .deferredCancels]

/-- Projections republished from an exact resumable context bank. -/
def resumableProjections : List Projection :=
  [ .execution, .scheduler, .preemption, .virtualMemory, .ipc, .capabilities
  , .lifecycle, .resumable, .blockingIPC ]

/-- Projections republished by a mapping-only virtual-memory transition. -/
def mappingProjections : List Projection :=
  [ .execution, .scheduler, .preemption, .virtualMemory, .ipc, .lifecycle
  , .resumable, .blockingIPC ]

/-- Projections republished by a queue-only scheduler admission. -/
def admissionProjections : List Projection :=
  [.scheduler, .preemption, .resumable, .blockingIPC]

/-- Projections republished by a resumable-aware scheduler removal. -/
def removalProjections : List Projection :=
  [.execution, .scheduler, .preemption, .lifecycle, .resumable, .blockingIPC]

/-- Projections read by return-plan liveness (`CompositeState.ReturnPlanLive`). -/
def returnPlanProjections : List Projection :=
  [.execution, .virtualMemory]

/-! ## Operation footprints -/

/-- The declared footprint of each typed operation.  `reads` lists what the
operation inspects in addition to what it writes; writes are always reads. -/
def Operation.footprint : Operation → Footprint
  | .interrupt _ => .ofLists [] cleanupProjections
  | .nmi _ _ => .ofLists [] [.execution, .resumable]
  | .selectUserReturn _ => .ofLists returnPlanProjections [.execution]
  | .userReturn _ => .ofLists returnPlanProjections [.execution, .resumable]
  | .syscall _ => .ofLists [] mappingProjections
  | .ipc _ => .ofLists [.execution] [.ipc, .transfers]
  | .resumePreempt _ _ => .ofLists [] resumableProjections
  | .transferOffer .. => .ofLists [] publicationProjections
  | .transferAccept .. => .ofLists [] publicationProjections
  | .capabilityCopy .. => .ofLists [] publicationProjections
  | .capabilityRevoke .. => .ofLists [] publicationProjections
  | .capabilityRevokeSubtree .. => .ofLists [] publicationProjections
  | .map .. => .ofLists [] mappingProjections
  | .unmap _ => .ofLists [] mappingProjections
  | .protect .. => .ofLists [] mappingProjections
  | .createSubject _ => .ofLists [] publicationProjections
  | .terminateSubject _ => .ofLists [] cleanupProjections
  | .scheduleAdd _ => .ofLists [.deferredCancels] admissionProjections
  | .scheduleRemove _ => .ofLists [] removalProjections
  | .scheduleNext => .ofLists [] publicationProjections
  | .scheduleYield => .ofLists [] publicationProjections
  | .scheduleTick => .ofLists [] publicationProjections
  | .terminateCurrent => .ofLists [] cleanupProjections
  | .restart => .empty

/-! ## The composite frame rule -/

/-- Composite frame obligations weaken to any footprint that writes more. -/
theorem CompositeState.Frames.mono {small large : Footprint}
    (within : small.WritesWithin large) {before after : CompositeState}
    (framed : CompositeState.Frames small before after) :
    CompositeState.Frames large before after := by
  intro projection
  exact CompositeFootprint.frames_mono within projection (framed projection)

/-- Discharge `WritesWithin` between two list-built footprints by checking
write-list inclusion on the concrete lists. -/
macro "footprint_within" : tactic =>
  `(tactic| exact CompositeFootprint.Footprint.ofLists_writesWithin (by decide))

/-- Decide that a projection lies outside a concrete declared write set. -/
macro "untouched_decide" : tactic =>
  `(tactic| (simp only [CompositeFootprint.Untouched]; decide))

/-- Discharge a helper frame lemma: written projections contradict the
untouched hypothesis by evaluation, and every untouched projection is
unchanged by definitional unfolding of a structure update. -/
macro "composite_frame" : tactic =>
  `(tactic| (
      intro projection untouched
      cases projection <;>
        first
          | exact absurd untouched (by untouched_decide)
          | rfl))

/-! ## Helper frame lemmas -/

theorem selectLiveReturnAuthority_frames state purpose :
    CompositeState.Frames (.ofLists [] [.execution]) state
      (selectLiveReturnAuthority state purpose) := by
  rw [selectLiveReturnAuthority_eq_execution_update]
  composite_frame

theorem executionUpdate_frames (state : CompositeState) (execution : State) :
    CompositeState.Frames (.ofLists [] [.execution]) state
      { state with execution } := by
  composite_frame

theorem executionResumableUpdate_frames (state : CompositeState) (execution : State)
    (resumable : ResumablePreemption.State) :
    CompositeState.Frames (.ofLists [] [.execution, .resumable]) state
      { state with execution, resumable } := by
  composite_frame

theorem installLifecycle_frames state lifecycle :
    CompositeState.Frames (.ofLists [] publicationProjections) state
      (installLifecycle state lifecycle) := by
  composite_frame

theorem installCopiedCapabilities_frames state capabilities :
    CompositeState.Frames (.ofLists [] publicationProjections) state
      (installCopiedCapabilities state capabilities) := by
  composite_frame

theorem installCreatedSubject_frames state subject :
    CompositeState.Frames (.ofLists [] publicationProjections) state
      (installCreatedSubject state subject) := by
  composite_frame

theorem installScheduler_frames state scheduler :
    CompositeState.Frames (.ofLists [] publicationProjections) state
      (installScheduler state scheduler) := by
  composite_frame

theorem installSchedulerAdmission_frames state scheduler :
    CompositeState.Frames (.ofLists [] admissionProjections) state
      (installSchedulerAdmission state scheduler) := by
  composite_frame

theorem installResumable_frames state resumable :
    CompositeState.Frames (.ofLists [] resumableProjections) state
      (installResumable state resumable) := by
  composite_frame

theorem installSchedulerRemoval_frames state resumable :
    CompositeState.Frames (.ofLists [] removalProjections) state
      (installSchedulerRemoval state resumable) := by
  composite_frame

theorem installTransfers_frames state transfers :
    CompositeState.Frames (.ofLists [] publicationProjections) state
      (installTransfers state transfers) := by
  composite_frame

theorem installRevokedSubtree_frames state root capabilities :
    CompositeState.Frames (.ofLists [] publicationProjections) state
      (installRevokedSubtree state root capabilities) := by
  composite_frame

theorem installTerminatedSubject_frames state subject resumable :
    CompositeState.Frames (.ofLists [] cleanupProjections) state
      (installTerminatedSubject state subject resumable) := by
  composite_frame

theorem publishInterruptCleanup_frames state subject :
    CompositeState.Frames (.ofLists [] cleanupProjections) state
      (publishInterruptCleanup state subject) := by
  composite_frame

theorem installVirtualMemory_frames state virtualMemory translations :
    CompositeState.Frames (.ofLists [] mappingProjections) state
      (installVirtualMemory state virtualMemory translations) := by
  composite_frame

theorem installIPC_frames state ipc :
    CompositeState.Frames (.ofLists [] [.ipc, .transfers]) state
      (installIPC state ipc) := by
  composite_frame

/-- The data-only IPC dispatcher writes only the IPC and transfer projections,
on every accepted, rejected, and sealed-transfer-pending branch. -/
theorem dispatchIPC_frames state call :
    CompositeState.Frames (.ofLists [.execution] [.ipc, .transfers]) state
      (dispatchIPC state call).state := by
  have within : (Footprint.ofLists [] [.ipc, .transfers]).WritesWithin
      (.ofLists [.execution] [.ipc, .transfers]) := by footprint_within
  cases call <;> simp only [dispatchIPC]
  all_goals
    repeat' first | split
    all_goals first
      | exact CompositeState.frames_of_eq _ rfl
      | exact (installIPC_frames _ _).mono within

/-! ## Per-operation frame theorems -/

/-- Close one `applyOperation` branch: a stutter, or a helper publication
whose frame weakens to the operation's declared footprint. -/
macro "operation_frame" : tactic =>
  `(tactic| first
      | exact CompositeState.frames_of_eq _ rfl
      | with_reducible exact (selectLiveReturnAuthority_frames _ _).mono (by footprint_within)
      | with_reducible exact (executionUpdate_frames _ _).mono (by footprint_within)
      | with_reducible exact (executionResumableUpdate_frames _ _ _).mono (by footprint_within)
      | with_reducible exact (installLifecycle_frames _ _).mono (by footprint_within)
      | with_reducible exact (installCopiedCapabilities_frames _ _).mono (by footprint_within)
      | with_reducible exact (installCreatedSubject_frames _ _).mono (by footprint_within)
      | with_reducible exact (installScheduler_frames _ _).mono (by footprint_within)
      | with_reducible exact (installSchedulerAdmission_frames _ _).mono (by footprint_within)
      | with_reducible exact (installResumable_frames _ _).mono (by footprint_within)
      | with_reducible exact (installSchedulerRemoval_frames _ _).mono (by footprint_within)
      | with_reducible exact (installTransfers_frames _ _).mono (by footprint_within)
      | with_reducible exact (installRevokedSubtree_frames _ _ _).mono (by footprint_within)
      | with_reducible exact (installTerminatedSubject_frames _ _ _).mono (by footprint_within)
      | with_reducible exact (publishInterruptCleanup_frames _ _).mono (by footprint_within)
      | with_reducible exact (installVirtualMemory_frames _ _ _).mono (by footprint_within)
      | with_reducible exact dispatchIPC_frames _ _
      | with_reducible exact (CompositeState.frames_trans _
          ((installVirtualMemory_frames _ _ _).mono (by footprint_within))
          ((selectLiveReturnAuthority_frames _ _).mono (by footprint_within)))
      | with_reducible exact (CompositeState.frames_trans _
          ((executionUpdate_frames _ _).mono (by footprint_within))
          ((installResumable_frames _ _).mono (by footprint_within))))

/-- **Frame rule.**  Every projection outside an operation's declared write
set is literally unchanged by its exact composite post-state. -/
theorem applyOperation_frames (state : CompositeState) (operation : Operation) :
    CompositeState.Frames operation.footprint state (applyOperation state operation) := by
  cases operation <;> simp only [applyOperation, Operation.footprint]
  all_goals
    repeat' first | split
    all_goals operation_frame

/-- Projection form of the frame rule. -/
theorem applyOperation_project_untouched (state : CompositeState) (operation : Operation)
    (projection : Projection)
    (untouched : CompositeFootprint.Untouched operation.footprint projection) :
    (applyOperation state operation).project projection = state.project projection :=
  applyOperation_frames state operation projection untouched

/-- A state predicate that depends only on the projections selected by
`support`: changing nothing in the support cannot change its truth. -/
def CompositeState.DependsOn (support : Projection → Bool)
    (predicate : CompositeState → Prop) : Prop :=
  ∀ before after : CompositeState,
    (∀ projection, support projection = true →
      after.project projection = before.project projection) →
    predicate before → predicate after

/-- **Lifting rule.**  A predicate over projections an operation does not
write is preserved by that operation, without inspecting the operation. -/
theorem applyOperation_preserves_of_dependsOn {support : Projection → Bool}
    {predicate : CompositeState → Prop} (dependsOn : CompositeState.DependsOn support predicate)
    (state : CompositeState) (operation : Operation)
    (disjoint : ∀ projection, support projection = true →
      CompositeFootprint.Untouched operation.footprint projection)
    (holds : predicate state) :
    predicate (applyOperation state operation) :=
  dependsOn state _ (fun projection supported =>
    applyOperation_project_untouched state operation projection
      (disjoint projection supported)) holds

/-- Direct-port, DMA, and invalidation-publication authority are outside every
ordinary operation's write set. -/
theorem Operation.footprint_untouched_authority (operation : Operation) :
    CompositeFootprint.Untouched operation.footprint .directPortIO ∧
      CompositeFootprint.Untouched operation.footprint .dmaAccepted ∧
      CompositeFootprint.Untouched operation.footprint .dmaObserved ∧
      CompositeFootprint.Untouched operation.footprint .invalidationPublication := by
  cases operation <;> simp only [CompositeFootprint.Untouched, Operation.footprint] <;> decide

/-! ## Lifted projection theorems -/

private theorem dispatchIPC_directPortIO state call :
    (dispatchIPC state call).state.directPortIO = state.directPortIO :=
  dispatchIPC_frames state call .directPortIO (by untouched_decide)

private theorem dispatchIPC_dmaAuthority state call :
    (dispatchIPC state call).state.dmaAccepted = state.dmaAccepted ∧
      (dispatchIPC state call).state.dmaObserved = state.dmaObserved :=
  ⟨dispatchIPC_frames state call .dmaAccepted (by untouched_decide),
    dispatchIPC_frames state call .dmaObserved (by untouched_decide)⟩

private theorem installTerminatedSubject_directPortIO state subject resumable :
    (installTerminatedSubject state subject resumable).directPortIO = state.directPortIO :=
  installTerminatedSubject_frames state subject resumable .directPortIO (by untouched_decide)

/-- Every public composite operation retains the complete direct-port control
and device projection literally.  Kernel device mutation remains confined to
the separately typed, purpose-bound `DirectPortIO.executeKernel` boundary, so
attacker-controlled composite words cannot relax TSS/IOPL policy or synthesize
a device transition.  This is the frame rule at the `directPortIO`
projection. -/
@[simp] theorem applyOperation_directPortIO state operation :
    (applyOperation state operation).directPortIO = state.directPortIO :=
  applyOperation_project_untouched state operation .directPortIO
    (Operation.footprint_untouched_authority operation).1

@[simp] theorem applyOperation_dmaAccepted state operation :
    (applyOperation state operation).dmaAccepted = state.dmaAccepted :=
  applyOperation_project_untouched state operation .dmaAccepted
    (Operation.footprint_untouched_authority operation).2.1

@[simp] theorem applyOperation_dmaObserved state operation :
    (applyOperation state operation).dmaObserved = state.dmaObserved :=
  applyOperation_project_untouched state operation .dmaObserved
    (Operation.footprint_untouched_authority operation).2.2.1

/-- No ordinary operation writes the conditional invalidation-publication
projection. -/
theorem applyOperation_invalidationPublication state operation :
    (applyOperation state operation).invalidationPublication =
      state.invalidationPublication :=
  applyOperation_project_untouched state operation .invalidationPublication
    (Operation.footprint_untouched_authority operation).2.2.2

end LeanOS.FailStop
