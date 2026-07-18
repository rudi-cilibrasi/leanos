import LeanOS.MemoryLifecycle

/-!
# Admitted per-subject frame budgets

This sequential model adds a fixed, kernel-owned admission partition to the
authoritative memory-lifecycle state.  A frame may be committed to at most one
subject because `commitment` is a function.  Allocation selects only a free
frame committed to the trusted subject; capability holders and destination
slots never select the charging principal.
-/
namespace LeanOS.FrameBudget

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId
abbrev SlotId := Capability.SlotId
abbrev FrameId := FrameAllocator.FrameId

structure State where
  memory : MemoryLifecycle.State
  /-- Monotonic subject-identity history; terminated identifiers are not reused. -/
  issuedSubjects : SubjectId → Bool
  /-- Fixed boot-admitted owner of each budgetable frame. `none` is unbudgeted. -/
  commitment : FrameId → Option SubjectId

def budgetFrames (state : State) (subject : SubjectId) : List FrameId :=
  state.memory.allocator.frames.filter fun frame => state.commitment frame = some subject

def usage (state : State) (subject : SubjectId) : Nat :=
  (budgetFrames state subject).countP fun frame =>
    match state.memory.allocator.status frame with
    | .owned _ => true
    | _ => false

def limit (state : State) (subject : SubjectId) : Nat :=
  (budgetFrames state subject).length

def hasAvailable (state : State) (subject : SubjectId) : Bool :=
  (budgetFrames state subject).any fun frame =>
    state.memory.allocator.status frame == .free

/-- Admission and authoritative allocator/object ownership agree. -/
def WellFormed (state : State) : Prop :=
  MemoryLifecycle.WellFormed state.memory ∧
  (∀ subject, state.memory.capabilities.subjects subject = true →
    state.issuedSubjects subject = true) ∧
  (∀ frame subject, state.commitment frame = some subject →
    frame ∈ state.memory.allocator.frames ∧
      ¬FrameAllocator.IsReserved state.memory.allocator frame ∧
      state.issuedSubjects subject = true) ∧
  (∀ object frame, state.memory.binding object = some frame →
    ∃ subject, state.commitment frame = some subject ∧
      state.memory.capabilities.subjects subject = true) ∧
  (∀ frame object, state.memory.allocator.status frame = .owned object →
    state.memory.binding object = some frame)

theorem usage_le_limit (state : State) (subject : SubjectId) :
    usage state subject ≤ limit state subject := by
  exact List.countP_le_length

theorem commitments_disjoint (state : State) (frame : FrameId) (left right : SubjectId)
    (hl : state.commitment frame = some left) (hr : state.commitment frame = some right) :
    left = right := by
  rw [hl] at hr
  exact Option.some.inj hr

inductive AllocationError where
  | invalidSubject | outOfRange | occupiedSlot | objectAlreadyIssued
  | identityExhausted | budgetExhausted
  deriving BEq, DecidableEq, Repr

inductive TerminateError where | neverIssued | alreadyTerminated
  deriving BEq, DecidableEq, Repr

inductive Result (error : Type) where | accepted | rejected (reason : error)
  deriving DecidableEq, Repr

structure Outcome (error : Type) where
  state : State
  result : Result error

def reject (state : State) (reason : error) : Outcome error :=
  { state, result := .rejected reason }

def firstAvailable (state : State) (subject : SubjectId) : Option FrameId :=
  state.memory.allocator.frames.find? fun frame =>
    state.commitment frame = some subject &&
      state.memory.allocator.status frame == .free

/-- Allocate to the trusted kernel-selected subject.  No untrusted owner word
or capability holder participates in the charging decision. -/
def allocate (state : State) (trustedSubject : SubjectId) (object : ObjectId)
    (slot : SlotId) : Outcome AllocationError :=
  if state.memory.capabilities.subjects trustedSubject != true then
    reject state .invalidSubject
  else if CapabilityHandle.slotReserved ≤ slot ∨
      !Capability.slotInRange state.memory.capabilities trustedSubject slot then
    reject state .outOfRange
  else if state.memory.capabilities.nextIdentity = 0 ∨
      CapabilityHandle.generationReserved ≤ state.memory.capabilities.nextIdentity then
    reject state .identityExhausted
  else if (state.memory.capabilities.slots trustedSubject slot).isSome then
    reject state .occupiedSlot
  else if state.memory.issued object then reject state .objectAlreadyIssued
  else match firstAvailable state trustedSubject with
    | none => reject state .budgetExhausted
    | some frame =>
      let allocationMemory : MemoryLifecycle.State :=
        { capabilities := Capability.installRoot
            (MemoryLifecycle.activateObject state.memory.capabilities object)
            trustedSubject slot object .memory Capability.allRights
          allocator := FrameAllocator.setStatus state.memory.allocator frame (.owned object)
          binding := MemoryLifecycle.setBinding state.memory.binding object (some frame)
          issued := MemoryLifecycle.setIssued state.memory.issued object }
      { state := { state with memory := allocationMemory }, result := .accepted }

def release (state : State) (trustedSubject : SubjectId) (slot : SlotId) :
    Outcome MemoryLifecycle.ReleaseError :=
  match MemoryLifecycle.release state.memory trustedSubject slot with
  | ⟨next, .accepted⟩ =>
      { state := { state with memory := next }, result := .accepted }
  | ⟨next, .rejected reason⟩ =>
      { state := { state with memory := next }, result := .rejected reason }

def chargedObjects (state : State) (subject : SubjectId) : List ObjectId :=
  (budgetFrames state subject).filterMap fun frame =>
    match state.memory.allocator.status frame with
    | .owned object => some object
    | _ => none

def setLiveSubject (capabilities : Capability.State) (subject : SubjectId)
    (live : Bool) : Capability.State :=
  { capabilities with subjects := fun candidate =>
      if candidate = subject then live else capabilities.subjects candidate }

def reclaimedStatus (state : State) (subject : SubjectId) (frame : FrameId) :
    FrameAllocator.FrameState :=
  if state.commitment frame = some subject then
    match state.memory.allocator.status frame with
    | .owned _ => .free
    | status => status
  else state.memory.allocator.status frame

/-- Whole-subject cleanup retires every object charged to the subject, clears
delegated aliases to those objects, and returns exactly its owned committed
frames to the allocator.  Admission itself remains fixed and cannot be minted
by repeated cleanup. -/
def terminateState (state : State) (subject : SubjectId) : State :=
  let retired := chargedObjects state subject
  let capabilities := state.memory.capabilities
  let cleanedCapabilities : Capability.State :=
    { (setLiveSubject capabilities subject false) with
      objects := fun object => if retired.contains object then false
        else capabilities.objects object
      kinds := fun object => if retired.contains object then none
        else capabilities.kinds object
      slots := fun holder slot =>
        match capabilities.slots holder slot with
        | none => none
        | some cap => if holder = subject || retired.contains cap.object then none else some cap }
  { state with
    memory :=
      { capabilities := cleanedCapabilities
        allocator := { state.memory.allocator with status := reclaimedStatus state subject }
        binding := fun object => if retired.contains object then none
          else state.memory.binding object
        issued := state.memory.issued } }

def terminate (state : State) (subject : SubjectId) : Outcome TerminateError :=
  if !state.issuedSubjects subject then reject state .neverIssued
  else if !state.memory.capabilities.subjects subject then reject state .alreadyTerminated
  else { state := terminateState state subject, result := .accepted }

theorem allocate_rejected_unchanged state subject object slot reason
    (h : (allocate state subject object slot).result = .rejected reason) :
    (allocate state subject object slot).state = state := by
  simp only [allocate] at h ⊢
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> simp_all [reject]

theorem release_rejected_unchanged state subject slot reason
    (h : (release state subject slot).result = .rejected reason) :
    (release state subject slot).state = state := by
  simp only [release] at h ⊢
  cases hresult : MemoryLifecycle.release state.memory subject slot with
  | mk next result =>
    cases result with
    | accepted => simp [hresult] at h
    | rejected rejectedReason =>
      simp [hresult] at h ⊢
      subst reason
      have hrejected :
          (MemoryLifecycle.release state.memory subject slot).result =
            .rejected rejectedReason := by simp [hresult]
      have unchanged := MemoryLifecycle.release_rejected_unchanged
        state.memory subject slot rejectedReason hrejected
      have hnext : next = state.memory := by simpa [hresult] using unchanged
      subst next
      rfl

theorem terminate_rejected_unchanged state subject reason
    (h : (terminate state subject).result = .rejected reason) :
    (terminate state subject).state = state := by
  simp only [terminate] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]

theorem allocation_charge_confined state trustedSubject object slot
    (h : (allocate state trustedSubject object slot).result = .accepted) :
    ∃ frame, (allocate state trustedSubject object slot).state.memory.binding object = some frame ∧
      state.commitment frame = some trustedSubject ∧
      FrameAllocator.IsOwnedBy
        (allocate state trustedSubject object slot).state.memory.allocator frame object := by
  simp only [allocate] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  next =>
    split <;> simp_all [reject]
    next frame hfind =>
      have hp := List.find?_some hfind
      simp at hp
      refine ⟨frame, by simp [MemoryLifecycle.setBinding], ?_, ?_⟩
      · exact hp.1
      · simp [FrameAllocator.IsOwnedBy, FrameAllocator.setStatus]

theorem allocation_other_usage_unchanged state trustedSubject object slot other
    (hne : other ≠ trustedSubject) :
    usage (allocate state trustedSubject object slot).state other = usage state other := by
  simp only [allocate]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  next frame hfind =>
    unfold usage budgetFrames
    apply List.countP_congr
    intro candidate hc
    have hcommit : state.commitment candidate = some other := by
      simpa using (List.mem_filter.mp hc).2
    have hselected := List.find?_some hfind
    simp at hselected
    have hframe : candidate ≠ frame := by
      intro heq
      subst candidate
      rw [hselected.1] at hcommit
      exact hne (Option.some.inj hcommit.symm)
    simp [FrameAllocator.setStatus, hframe]

theorem peer_available_not_budgetExhausted state subject object slot
    (havailable : hasAvailable state subject = true) :
    (allocate state subject object slot).result ≠ .rejected .budgetExhausted := by
  unfold allocate
  split <;> try simp [reject]
  split <;> try simp [reject]
  split <;> try simp [reject]
  split <;> try simp [reject]
  split <;> try simp [reject]
  unfold hasAvailable budgetFrames at havailable
  simp only [List.any_eq_true] at havailable
  obtain ⟨frame, hmem, hfree⟩ := havailable
  have hcommit := (List.mem_filter.mp hmem).2
  have hfind : firstAvailable state subject ≠ none := by
    intro hnone
    unfold firstAvailable at hnone
    have hall := List.find?_eq_none.mp hnone
    have hfalse := hall frame (List.mem_filter.mp hmem).1
    simp_all
  split <;> simp_all [reject]

/-- Under the ordinary object/slot preconditions, an admitted free frame makes
allocation succeed; exhaustion of any peer is irrelevant to this decision. -/
theorem available_allocation_accepted state subject object slot
    (hlive : state.memory.capabilities.subjects subject = true)
    (hslot : slot < CapabilityHandle.slotReserved)
    (hinrange : Capability.slotInRange state.memory.capabilities subject slot = true)
    (hidentity : state.memory.capabilities.nextIdentity ≠ 0)
    (hidentityBound : state.memory.capabilities.nextIdentity <
      CapabilityHandle.generationReserved)
    (hempty : state.memory.capabilities.slots subject slot = none)
    (hunissued : state.memory.issued object = false)
    (havailable : hasAvailable state subject = true) :
    (allocate state subject object slot).result = .accepted := by
  have hslotBound : ¬CapabilityHandle.slotReserved ≤ slot := by omega
  have hgenerationBound :
      ¬CapabilityHandle.generationReserved ≤ state.memory.capabilities.nextIdentity := by omega
  cases hfirst : firstAvailable state subject with
  | none =>
    have hisolation := peer_available_not_budgetExhausted state subject object slot havailable
    simp [allocate, hlive, hslotBound, hinrange, hidentity, hgenerationBound, hempty,
      hunissued, hfirst, reject] at hisolation
  | some frame =>
    simp [allocate, hlive, hslotBound, hinrange, hidentity, hgenerationBound, hempty,
      hunissued, hfirst]

theorem release_preserves_commitment state subject slot :
    (release state subject slot).state.commitment = state.commitment := by
  unfold release
  split <;> rfl

theorem terminate_preserves_commitment state subject :
    (terminate state subject).state.commitment = state.commitment := by
  unfold terminate
  split <;> try rfl
  split <;> rfl

theorem termination_frees_charged_frame state subject frame object
    (hcommit : state.commitment frame = some subject)
    (howned : state.memory.allocator.status frame = .owned object) :
    (terminateState state subject).memory.allocator.status frame = .free := by
  simp [terminateState, reclaimedStatus, hcommit, howned]

theorem termination_preserves_other_frame state subject frame
    (hcommit : state.commitment frame ≠ some subject) :
    (terminateState state subject).memory.allocator.status frame =
      state.memory.allocator.status frame := by
  simp [terminateState, reclaimedStatus, hcommit]

/-! Executable budget, isolation, delegation, reuse, and corruption traces. -/
private def caps (cap0 cap1 : Nat) : Capability.State :=
  { subjects := fun subject => subject < 2
    objects := fun _ => false
    kinds := fun _ => none
    slotCapacity := fun subject => if subject = 0 then cap0 else cap1
    slots := fun _ _ => none }

private def sample (budget0 budget1 : Nat) : State :=
  let frames := List.range (budget0 + budget1)
  { memory :=
      { capabilities := caps 4 4
        allocator := { frames, status := fun frame => if frame ∈ frames then .free else .reserved }
        binding := fun _ => none
        issued := fun _ => false }
    issuedSubjects := fun subject => subject < 2
    commitment := fun frame =>
      if frame < budget0 then some 0
      else if frame < budget0 + budget1 then some 1 else none }

example : (allocate (sample 0 1) 0 10 0).result = .rejected .budgetExhausted := by
  native_decide
example : (allocate (sample 1 1) 0 10 0).result = .accepted := by native_decide
example : (allocate (sample 1 1) 2 10 0).result = .rejected .invalidSubject := by native_decide
example : (allocate (sample 1 1) 0 10 4).result = .rejected .outOfRange := by native_decide

private def subject0Full := (allocate (sample 1 2) 0 10 0).state
example : (allocate subject0Full 0 11 1).result = .rejected .budgetExhausted := by native_decide
example : (allocate subject0Full 1 11 0).result = .accepted := by native_decide
example : (allocate (allocate subject0Full 1 11 0).state 1 12 1).result = .accepted := by
  native_decide
example : (allocate subject0Full 0 11 0).result = .rejected .occupiedSlot := by native_decide
example : (allocate subject0Full 0 11 1).state = subject0Full := by
  exact allocate_rejected_unchanged _ _ _ _ AllocationError.budgetExhausted
    (by native_decide)

private def released := (release subject0Full 0 0).state
example : (allocate released 0 11 0).result = .accepted := by native_decide
example : (release released 0 0).result = .rejected .staleSlot := by native_decide

private def delegated :=
  let allocated := (allocate (sample 1 1) 0 10 0).state
  let copied := Capability.copy allocated.memory.capabilities 0 0 1 0
    (Capability.oneRight .read)
  { allocated with memory := { allocated.memory with capabilities := copied.state } }

example : usage delegated 0 = 1 ∧ usage delegated 1 = 0 := by native_decide
example : (release delegated 1 0).result = .rejected .missingRevoke := by native_decide

private def twoObjects :=
  (allocate (allocate (sample 2 1) 0 10 0).state 0 11 1).state
private def terminated := (terminate twoObjects 0).state
example : usage terminated 0 = 0 ∧ hasAvailable terminated 0 := by native_decide
example : terminated.memory.issued 10 ∧ terminated.memory.issued 11 := by native_decide
example : (terminate terminated 0).result = .rejected .alreadyTerminated := by native_decide

/-- Corrupted ownership without a binding is rejected by the coherence invariant. -/
private def corruptMemory (memory : MemoryLifecycle.State) : MemoryLifecycle.State :=
  { memory with allocator := FrameAllocator.setStatus memory.allocator 0 (.owned 99) }

private def corrupted : State :=
  let base := sample 1 1
  { base with memory := corruptMemory base.memory }
example : ¬WellFormed corrupted := by
  intro h
  have hbinding := h.2.2.2.2 0 99 (by native_decide)
  simp [corrupted, corruptMemory, sample] at hbinding

end LeanOS.FrameBudget
