import LeanOS.EndpointIPC
import LeanOS.VirtualMapping

/-!
# Subject lifecycle

This finite, sequential model makes subject identity lifetime explicit.  Subject
identifiers are never reused.  A trusted kernel operation creates and terminates
subjects; termination is one atomic state transformation.
-/
namespace LeanOS.SubjectLifecycle

set_option linter.unusedSimpArgs false

open LeanOS

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId
abbrev FrameId := FrameAllocator.FrameId
abbrev AddressSpaceId := VirtualMapping.AddressSpaceId

structure Message where
  sender : SubjectId
  word : UInt64
  deriving DecidableEq, Repr

structure State where
  capabilities : Capability.State
  issuedSubjects : SubjectId → Bool
  ownedMemory : ObjectId → Option (SubjectId × FrameId)
  addressOwner : AddressSpaceId → Option SubjectId
  mapping : AddressSpaceId → VirtualMapping.VirtualPage → Option ObjectId
  endpointOwner : ObjectId → Option SubjectId
  mailbox : ObjectId → Option Message
  frameOwner : FrameId → Option SubjectId
  freeFrame : FrameId → Bool
  runnable : SubjectId → Bool
  current : Option SubjectId

def WellFormed (state : State) : Prop :=
  (∀ subject, state.capabilities.subjects subject = true →
    state.issuedSubjects subject = true) ∧
  (∀ object subject frame, state.ownedMemory object = some (subject, frame) →
    state.capabilities.subjects subject = true ∧ state.frameOwner frame = some subject ∧
      state.freeFrame frame = false) ∧
  (∀ addressSpace subject, state.addressOwner addressSpace = some subject →
    state.capabilities.subjects subject = true) ∧
  (∀ object subject, state.endpointOwner object = some subject →
    state.capabilities.subjects subject = true) ∧
  (∀ subject, state.runnable subject = true → state.capabilities.subjects subject = true) ∧
  (∀ subject, state.current = some subject → state.capabilities.subjects subject = true)

inductive CreateError where | alreadyLive | alreadyIssued
  deriving DecidableEq, Repr

inductive TerminateError where | neverIssued | alreadyTerminated
  deriving DecidableEq, Repr

inductive Result (error : Type) where | accepted | rejected (reason : error)
  deriving DecidableEq, Repr

structure Outcome (error : Type) where
  state : State
  result : Result error

def reject (state : State) (reason : error) : Outcome error :=
  { state, result := .rejected reason }

def setBool (values : Nat → Bool) (key : Nat) (value : Bool) :=
  fun candidate => if candidate = key then value else values candidate

def create (state : State) (subject : SubjectId) : Outcome CreateError :=
  if state.capabilities.subjects subject then reject state .alreadyLive
  else if state.issuedSubjects subject then reject state .alreadyIssued
  else
    { state := { state with
        capabilities := { state.capabilities with
          subjects := setBool state.capabilities.subjects subject true }
        issuedSubjects := setBool state.issuedSubjects subject true }
      result := .accepted }

def terminatedCapabilities (state : State) (subject : SubjectId) : Capability.State :=
  { state.capabilities with
    subjects := setBool state.capabilities.subjects subject false
    objects := fun object =>
      if (state.ownedMemory object).any (fun owner => owner.1 = subject) ||
          state.endpointOwner object = some subject then false
      else state.capabilities.objects object
    kinds := fun object =>
      if (state.ownedMemory object).any (fun owner => owner.1 = subject) ||
          state.endpointOwner object = some subject then none
      else state.capabilities.kinds object
    slots := fun holder slot =>
      match state.capabilities.slots holder slot with
      | none => none
      | some capability =>
          if holder = subject ||
              (state.ownedMemory capability.object).any (fun owner => owner.1 = subject) ||
              state.endpointOwner capability.object = some subject
          then none else some capability }

def terminateState (state : State) (subject : SubjectId) : State :=
  { state with
    capabilities := terminatedCapabilities state subject
    ownedMemory := fun object =>
      match state.ownedMemory object with
      | some ownership => if ownership.1 = subject then none else some ownership
      | none => none
    addressOwner := fun addressSpace =>
      if state.addressOwner addressSpace = some subject then none else state.addressOwner addressSpace
    mapping := fun addressSpace page =>
      match state.addressOwner addressSpace, state.mapping addressSpace page with
      | some owner, _ => if owner = subject then none else state.mapping addressSpace page
      | none, some object =>
          if (state.ownedMemory object).any (fun owner => owner.1 = subject) then none
          else some object
      | none, none => none
    endpointOwner := fun object =>
      if state.endpointOwner object = some subject then none else state.endpointOwner object
    mailbox := fun object =>
      if state.endpointOwner object = some subject then none
      else match state.mailbox object with
        | some message => if message.sender = subject then none else some message
        | none => none
    frameOwner := fun frame =>
      if state.frameOwner frame = some subject then none else state.frameOwner frame
    freeFrame := fun frame =>
      if state.frameOwner frame = some subject then true else state.freeFrame frame
    runnable := setBool state.runnable subject false
    current := if state.current = some subject then none else state.current }

def terminate (state : State) (subject : SubjectId) : Outcome TerminateError :=
  if !state.issuedSubjects subject then reject state .neverIssued
  else if !state.capabilities.subjects subject then reject state .alreadyTerminated
  else { state := terminateState state subject, result := .accepted }

theorem create_rejected_unchanged state subject reason
    (h : (create state subject).result = .rejected reason) :
    (create state subject).state = state := by
  simp only [create] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]

theorem terminate_rejected_unchanged state subject reason
    (h : (terminate state subject).result = .rejected reason) :
    (terminate state subject).state = state := by
  simp only [terminate] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]

theorem create_preserves_wellFormed state subject (hstate : WellFormed state) :
    WellFormed (create state subject).state := by
  simp only [create]
  split
  · simpa [reject]
  split
  · simpa [reject]
  · unfold WellFormed at hstate ⊢
    rcases hstate with ⟨hlive, hmemory, haddress, hendpoint, hrunnable, hcurrent⟩
    have promote : ∀ candidate, state.capabilities.subjects candidate = true →
        setBool state.capabilities.subjects subject true candidate = true := by
      intro candidate hc
      by_cases heq : candidate = subject <;> simp [setBool, heq, hc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro candidate hc
      by_cases heq : candidate = subject
      · subst candidate; simp [setBool]
      · have hold := hlive candidate (by simpa [setBool, heq] using hc)
        simpa [setBool, heq] using hold
    · intro object owner frame h
      exact ⟨promote owner (hmemory object owner frame h).1,
        (hmemory object owner frame h).2⟩
    · intro addressSpace owner h
      exact promote owner (haddress addressSpace owner h)
    · intro object owner h
      exact promote owner (hendpoint object owner h)
    · intro candidate h
      exact promote candidate (hrunnable candidate h)
    · intro candidate h
      exact promote candidate (hcurrent candidate h)

theorem terminateState_preserves_wellFormed state subject (hstate : WellFormed state) :
    WellFormed (terminateState state subject) := by
  unfold WellFormed at hstate ⊢
  rcases hstate with ⟨hlive, hmemory, haddress, hendpoint, hrunnable, hcurrent⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro candidate hc
    have hc' : state.capabilities.subjects candidate = true := by
      by_cases heq : candidate = subject
      · subst candidate
        simp [terminateState, terminatedCapabilities, setBool] at hc
      · simpa [terminateState, terminatedCapabilities, setBool, heq] using hc
    exact hlive candidate hc'
  · intro object owner frame h
    cases ho : state.ownedMemory object with
    | none => simp [terminateState, ho] at h
    | some ownership =>
      by_cases heq : ownership.1 = subject
      · simp [terminateState, ho, heq] at h
      · have hold : state.ownedMemory object = some (owner, frame) := by
          simpa [terminateState, ho, heq] using h
        have hownership : ownership = (owner, frame) :=
          Option.some.inj (ho.symm.trans hold)
        have howner : ownership.1 = owner := congrArg Prod.fst hownership
        have old := hmemory object owner frame hold
        constructor
        · have hone : owner ≠ subject := by
            intro hs
            exact heq (howner.trans hs)
          simpa [terminateState, terminatedCapabilities, setBool, hone] using old.1
        · constructor
          · have hone : owner ≠ subject := by
              intro hs
              exact heq (howner.trans hs)
            simp [terminateState, old.2.1, hone]
          · have hnot : state.frameOwner frame ≠ some subject := by
              rw [old.2.1]
              simp [show owner ≠ subject from fun hs => heq (howner.trans hs)]
            simpa [terminateState, hnot] using old.2.2
  · intro addressSpace owner h
    by_cases heq : state.addressOwner addressSpace = some subject
    · simp [terminateState, heq] at h
    · have hold : state.addressOwner addressSpace = some owner := by
        simpa [terminateState, heq] using h
      have old := haddress addressSpace owner hold
      have hone : owner ≠ subject := by intro hs; subst owner; exact heq hold
      simpa [terminateState, terminatedCapabilities, setBool, hone] using old
  · intro object owner h
    by_cases heq : state.endpointOwner object = some subject
    · simp [terminateState, heq] at h
    · have hold : state.endpointOwner object = some owner := by
        simpa [terminateState, heq] using h
      have old := hendpoint object owner hold
      have hone : owner ≠ subject := by intro hs; subst owner; exact heq hold
      simpa [terminateState, terminatedCapabilities, setBool, hone] using old
  · intro candidate h
    have hone : candidate ≠ subject := by
      intro heq; subst candidate; simp [terminateState, setBool] at h
    have hold : state.runnable candidate = true := by
      simpa [terminateState, setBool, hone] using h
    simpa [terminateState, terminatedCapabilities, setBool, hone] using hrunnable candidate hold
  · intro candidate h
    have hone : candidate ≠ subject := by
      intro heq; subst candidate; simp [terminateState] at h
    have hold : state.current = some candidate := by
      simp [terminateState, hone] at h
      exact h.2
    simpa [terminateState, terminatedCapabilities, setBool, hone] using hcurrent candidate hold

theorem terminate_preserves_wellFormed state subject (hstate : WellFormed state) :
    WellFormed (terminate state subject).state := by
  simp only [terminate]
  split
  · simpa [reject]
  split
  · simpa [reject]
  · exact terminateState_preserves_wellFormed state subject hstate

theorem terminated_not_live (state : State) subject :
    (terminateState state subject).capabilities.subjects subject = false := by
  simp [terminateState, terminatedCapabilities, setBool]

theorem terminated_slot_empty (state : State) subject slot :
    (terminateState state subject).capabilities.slots subject slot = none := by
  simp [terminateState, terminatedCapabilities]
  cases state.capabilities.slots subject slot <;> simp

theorem terminated_lookup_invalid (state : State) subject slot :
    Capability.lookup (terminateState state subject).capabilities subject slot =
      .invalidSubject := by
  simp [Capability.lookup, terminated_not_live]

theorem terminated_not_runnable (state : State) subject :
    (terminateState state subject).runnable subject = false := by
  simp [terminateState, setBool]

theorem terminated_not_current (state : State) subject :
    (terminateState state subject).current ≠ some subject := by
  simp [terminateState]

theorem terminated_address_spaces_removed (state : State) subject addressSpace
    (h : state.addressOwner addressSpace = some subject) :
    (terminateState state subject).addressOwner addressSpace = none := by
  simp [terminateState, h]

theorem terminated_memory_reclaimed (state : State) subject object frame
    (h : state.ownedMemory object = some (subject, frame))
    (hf : state.frameOwner frame = some subject) :
    (terminateState state subject).ownedMemory object = none ∧
      (terminateState state subject).freeFrame frame = true := by
  constructor
  · simp [terminateState, h]
  · simp [terminateState, hf]

theorem unrelated_memory_unchanged (state : State) subject object owner frame
    (h : state.ownedMemory object = some (owner, frame)) (hne : owner ≠ subject) :
    (terminateState state subject).ownedMemory object = some (owner, frame) := by
  simp [terminateState, h, hne]

theorem terminated_endpoint_removed (state : State) subject object
    (h : state.endpointOwner object = some subject) :
    (terminateState state subject).endpointOwner object = none ∧
      (terminateState state subject).mailbox object = none := by
  simp [terminateState, h]

theorem issued_history_preserved (state : State) subject candidate :
    (terminateState state subject).issuedSubjects candidate = state.issuedSubjects candidate := rfl

theorem old_identity_never_recreated (state : State) subject
    (hissued : state.issuedSubjects subject = true) :
    (create (terminateState state subject) subject).result = .rejected .alreadyIssued := by
  unfold create
  rw [show (terminateState state subject).capabilities.subjects subject = false from
    terminated_not_live state subject]
  simp [terminateState, hissued, reject]

-- A compact adversarial state exercises delegated authority, mappings, a
-- pending message, current/runnable cleanup, reuse rejection, and isolation.
private def caps : Capability.State :=
  { subjects := fun s => s < 3
    objects := fun o => o = 10 || o = 11 || o = 12
    kinds := fun o => if o = 10 then some .memory else if o = 11 then some .addressSpace
      else if o = 12 then some .endpoint else none
    slots := fun s slot =>
      if s = 1 && slot = 0 then some { object := 10, kind := .memory, rights := { read := true } }
      else if s = 2 && slot = 0 then some { object := 10, kind := .memory, rights := { read := true } }
      else none }

private def adversarial : State :=
  { capabilities := caps
    issuedSubjects := fun s => s < 3
    ownedMemory := fun o => if o = 10 then some (1, 7) else none
    addressOwner := fun a => if a = 11 then some 1 else none
    mapping := fun a p => if a = 11 && p = 0 then some 10 else none
    endpointOwner := fun o => if o = 12 then some 1 else none
    mailbox := fun o => if o = 12 then some { sender := 1, word := 42 } else none
    frameOwner := fun f => if f = 7 then some 1 else none
    freeFrame := fun _ => false
    runnable := fun s => s = 1 || s = 2
    current := some 1 }

private def terminated := (terminate adversarial 1).state

example : (terminate adversarial 1).result = .accepted := by native_decide
example : Capability.lookup terminated.capabilities 1 0 = .invalidSubject := by native_decide
example : terminated.ownedMemory 10 = none ∧ terminated.freeFrame 7 := by native_decide
example : terminated.addressOwner 11 = none ∧ terminated.mapping 11 0 = none := by native_decide
example : terminated.endpointOwner 12 = none ∧ terminated.mailbox 12 = none := by native_decide
example : terminated.current = none ∧ !terminated.runnable 1 := by native_decide
example : Capability.lookup terminated.capabilities 2 0 = .staleSlot := by native_decide
example : (terminate terminated 1).result = .rejected .alreadyTerminated := by native_decide
example : (create terminated 1).result = .rejected .alreadyIssued := by native_decide

end LeanOS.SubjectLifecycle
