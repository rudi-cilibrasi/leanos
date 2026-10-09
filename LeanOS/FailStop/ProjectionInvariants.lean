import LeanOS.FailStop.Gate

/-!
# Fail-stop composite: invariants split by projection

A `ProjectionInvariant` is one conjunct of a composite invariant together with
the projections it reads, and a machine-checked proof (`DependsOn`) that it
reads nothing else.  A transition whose declared write set misses that
support preserves the conjunct by the frame rule alone
(`ProjectionInvariant.preserved_of_frames`).  A whole invariant stated as a
list of such conjuncts (`ProjectionInvariant.All`) is then preserved once each
*touched* conjunct is proved (`ProjectionInvariant.All.preserved_of_frames`).

`RuntimeWellFormed` is decomposed this way into `runtimeInvariants`, one
conjunct per subsystem plus the cross-projection agreements, and
`runtimeWellFormed_iff_all` proves the decomposition exact.  Adding a new
projection with its own invariant therefore adds one list entry; every
operation that does not write the new projection discharges it through its
frame theorem, with no change to the existing per-operation proofs.
-/
namespace LeanOS.FailStop

open LeanOS
open LeanOS.CompositeFootprint (Projection Footprint)

/-- One conjunct of a composite invariant and the projections it reads. -/
structure ProjectionInvariant where
  /-- The projections the conjunct may inspect. -/
  support : List Projection
  /-- The conjunct itself. -/
  holds : CompositeState → Prop
  /-- The conjunct reads nothing outside `support`. -/
  dependsOn : CompositeState.DependsOn (fun projection => decide (projection ∈ support)) holds

/-- A footprint leaves an invariant's support untouched.  This is a closed
Boolean computation for concrete supports and list-built footprints. -/
def ProjectionInvariant.untouchedBy (invariant : ProjectionInvariant)
    (footprint : Footprint) : Bool :=
  invariant.support.all fun projection => !footprint.writes projection

theorem ProjectionInvariant.untouchedBy_untouched {invariant : ProjectionInvariant}
    {footprint : Footprint} (untouched : invariant.untouchedBy footprint = true)
    (projection : Projection) (supported : projection ∈ invariant.support) :
    CompositeFootprint.Untouched footprint projection := by
  have member := List.all_eq_true.1 untouched projection supported
  simpa [CompositeFootprint.Untouched] using member

/-- **Invariant lifting.**  A transition framed by a footprint that misses an
invariant's support preserves that invariant. -/
theorem ProjectionInvariant.preserved_of_frames (invariant : ProjectionInvariant)
    {footprint : Footprint} {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (untouched : invariant.untouchedBy footprint = true)
    (holds : invariant.holds before) :
    invariant.holds after :=
  invariant.dependsOn before after (fun projection supported =>
    frames projection (invariant.untouchedBy_untouched untouched projection
      (by simpa using supported))) holds

/-- A whole invariant given as a list of supported conjuncts. -/
def ProjectionInvariant.All (invariants : List ProjectionInvariant)
    (state : CompositeState) : Prop :=
  ∀ invariant, invariant ∈ invariants → invariant.holds state

/-- **Per-projection preservation.**  A framed transition preserves a list of
supported conjuncts once every conjunct whose support it writes is proved;
every other conjunct is discharged by the frame rule. -/
theorem ProjectionInvariant.All.preserved_of_frames {invariants : List ProjectionInvariant}
    {footprint : Footprint} {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (holds : ProjectionInvariant.All invariants before)
    (touched : ∀ invariant, invariant ∈ invariants →
      invariant.untouchedBy footprint = false → invariant.holds after) :
    ProjectionInvariant.All invariants after := by
  intro invariant member
  cases untouched : invariant.untouchedBy footprint
  · exact touched invariant member untouched
  · exact invariant.preserved_of_frames frames untouched (holds invariant member)

/-- The conjuncts of a concatenated invariant are those of its parts. -/
theorem ProjectionInvariant.all_append (first second : List ProjectionInvariant)
    (state : CompositeState) :
    ProjectionInvariant.All (first ++ second) state ↔
      ProjectionInvariant.All first state ∧ ProjectionInvariant.All second state := by
  simp only [ProjectionInvariant.All, List.mem_append]
  constructor
  · intro holds
    exact ⟨fun invariant member => holds invariant (Or.inl member),
      fun invariant member => holds invariant (Or.inr member)⟩
  · rintro ⟨first, second⟩ invariant (member | member)
    · exact first invariant member
    · exact second invariant member

/-- Prove a `DependsOn` obligation by destructuring both states and
identifying every supported field: the predicate then mentions only shared
fields and the hypothesis closes the goal definitionally. -/
macro "projection_depends_on" : tactic => `(tactic| (
  intro before after same holds
  cases before; cases after
  agree_subst same
  exact holds))

/-! ## `RuntimeWellFormed` by projection -/

/-- Cross-projection lifecycle and capability coherence. -/
def coherentInvariant : ProjectionInvariant where
  support := [ .execution, .scheduler, .preemption, .virtualMemory, .ipc
    , .capabilities, .lifecycle, .resumable, .transfers ]
  holds := CompositeState.Coherent
  dependsOn := by projection_depends_on

def executionInvariant : ProjectionInvariant where
  support := [.execution]
  holds state := WellFormed state.execution
  dependsOn := by projection_depends_on

def lifecycleInvariant : ProjectionInvariant where
  support := [.lifecycle]
  holds state := SubjectLifecycle.WellFormed state.lifecycle
  dependsOn := by projection_depends_on

def capabilitiesInvariant : ProjectionInvariant where
  support := [.capabilities]
  holds state := Capability.WellFormed state.capabilities
  dependsOn := by projection_depends_on

def virtualMemoryInvariant : ProjectionInvariant where
  support := [.virtualMemory]
  holds state := VirtualMapping.LifecycleWellFormed state.virtualMemory
  dependsOn := by projection_depends_on

def ipcInvariant : ProjectionInvariant where
  support := [.ipc]
  holds state := IPCSyscall.WellFormed state.ipc
  dependsOn := by projection_depends_on

def schedulerInvariant : ProjectionInvariant where
  support := [.scheduler]
  holds state := Scheduler.WellFormed state.scheduler
  dependsOn := by projection_depends_on

def preemptionInvariant : ProjectionInvariant where
  support := [.preemption]
  holds state := Preemption.WellFormed state.preemption
  dependsOn := by projection_depends_on

def resumableInvariant : ProjectionInvariant where
  support := [.resumable]
  holds state := ResumablePreemption.WellFormed state.resumable
  dependsOn := by projection_depends_on

def transfersInvariant : ProjectionInvariant where
  support := [.transfers]
  holds state := CapabilityTransfer.WellFormed state.transfers
  dependsOn := by projection_depends_on

/-- The resumable terminal latch agrees with the execution latch. -/
def haltAgreementInvariant : ProjectionInvariant where
  support := [.execution, .resumable]
  holds state :=
    (state.resumable.halted = true ↔ ∃ record, state.execution.mode = .halted record)
  dependsOn := by projection_depends_on

/-- Armed return authority names a live compiled return plan. -/
def returnPlanInvariant : ProjectionInvariant where
  support := [.execution, .virtualMemory]
  holds state := state.execution.returnAuthorityArmed = true → state.ReturnPlanLive = true
  dependsOn := by projection_depends_on

/-- The blocking store observes the composite scheduler and lifecycle. -/
def blockingCoherentInvariant : ProjectionInvariant where
  support := [.scheduler, .lifecycle, .blockingIPC]
  holds := CompositeState.BlockingIPCCoherent
  dependsOn := by projection_depends_on

/-- Boot-accepted direct-port controls and the exact PCI quarantine. -/
def authorityInvariant : ProjectionInvariant where
  support := [.directPortIO, .dmaAccepted, .dmaObserved]
  holds state :=
    DirectPortIO.AcceptedControls state.directPortIO.controls ∧ state.DMAQuarantined
  dependsOn := by projection_depends_on

/-- `RuntimeWellFormed`, one supported conjunct per entry, in definition
order. -/
def runtimeInvariants : List ProjectionInvariant :=
  [ coherentInvariant, executionInvariant, lifecycleInvariant, capabilitiesInvariant
  , virtualMemoryInvariant, ipcInvariant, schedulerInvariant, preemptionInvariant
  , resumableInvariant, transfersInvariant, haltAgreementInvariant, returnPlanInvariant
  , blockingCoherentInvariant, authorityInvariant ]

/-- The per-projection decomposition is exactly the global runtime
invariant. -/
theorem runtimeWellFormed_iff_all (state : CompositeState) :
    RuntimeWellFormed state ↔ ProjectionInvariant.All runtimeInvariants state := by
  simp only [ProjectionInvariant.All, runtimeInvariants, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  rfl

/-- **Runtime lifting.**  A framed transition preserves `RuntimeWellFormed`
once every runtime conjunct whose support it writes is proved. -/
theorem runtimeWellFormed_preserved_of_frames {footprint : Footprint}
    {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (holds : RuntimeWellFormed before)
    (touched : ∀ invariant, invariant ∈ runtimeInvariants →
      invariant.untouchedBy footprint = false → invariant.holds after) :
    RuntimeWellFormed after :=
  (runtimeWellFormed_iff_all after).2
    (ProjectionInvariant.All.preserved_of_frames frames
      ((runtimeWellFormed_iff_all before).1 holds) touched)

/-- A transition that writes no runtime projection preserves
`RuntimeWellFormed` by the frame rule alone. -/
theorem runtimeWellFormed_preserved_of_untouched {footprint : Footprint}
    {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (untouched : ∀ invariant, invariant ∈ runtimeInvariants →
      invariant.untouchedBy footprint = true)
    (holds : RuntimeWellFormed before) :
    RuntimeWellFormed after :=
  runtimeWellFormed_preserved_of_frames frames holds fun invariant member touched => by
    rw [untouched invariant member] at touched
    contradiction

/-- Every ordinary gate step preserves a supported invariant whose support
its declared footprint misses. -/
theorem gate_preserves_projectionInvariant (invariant : ProjectionInvariant)
    (state : CompositeState) (operation : Operation)
    (untouched : invariant.untouchedBy operation.footprint = true)
    (holds : invariant.holds state) :
    invariant.holds (gate state operation).state :=
  invariant.preserved_of_frames (gate_frames state operation) untouched holds

/-- No ordinary operation writes the direct-port or DMA authority, so every
gate step preserves the authority conjunct of `RuntimeWellFormed` by the
frame rule. -/
theorem gate_preserves_authorityInvariant (state : CompositeState) (operation : Operation)
    (holds : authorityInvariant.holds state) :
    authorityInvariant.holds (gate state operation).state := by
  apply gate_preserves_projectionInvariant authorityInvariant state operation _ holds
  have authority := Operation.footprint_untouched_authority operation
  simp only [ProjectionInvariant.untouchedBy, authorityInvariant, List.all_cons,
    List.all_nil, Bool.and_true]
  simp only [CompositeFootprint.Untouched] at authority
  simp [authority.1, authority.2.1, authority.2.2.1]

end LeanOS.FailStop
