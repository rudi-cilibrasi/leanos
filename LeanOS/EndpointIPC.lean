import LeanOS.MemoryLifecycle
import LeanOS.CapabilityHandle

/-!
# Capability-authorized endpoint IPC

This sequential model provides capacity-one, nonblocking mailboxes. Endpoint
identifiers are never reused. A trusted operation argument supplies the sender;
the two payload words are inert data and never transfer capabilities.
-/
namespace LeanOS.EndpointIPC

set_option linter.unusedSimpArgs false

open LeanOS
abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId
abbrev SlotId := Capability.SlotId

structure Payload where
  word0 : UInt64
  word1 : UInt64
  deriving DecidableEq, Repr

structure Envelope where
  endpoint : ObjectId
  sender : SubjectId
  payload : Payload
  deriving DecidableEq, Repr

structure State extends MemoryLifecycle.State where
  /-- Shared monotonic history from the composed address-space lifecycle. -/
  issuedAddressSpace : ObjectId → Bool
  mailbox : ObjectId → Option Envelope
  /-- Ghost evidence: append-only records created only by accepted sends. -/
  sendHistory : ObjectId → List Envelope

/-- Capability validity, endpoint lifetime, bounded mailbox, and provenance agree. -/
def WellFormed (state : State) : Prop :=
  Capability.WellFormed state.capabilities ∧
  (∀ object, state.capabilities.objects object = true →
    state.capabilities.kinds object = some .endpoint → state.issued object = true) ∧
  (∀ object envelope, state.mailbox object = some envelope →
    state.capabilities.objects object = true ∧
    state.capabilities.kinds object = some .endpoint ∧
    envelope.endpoint = object ∧ envelope ∈ state.sendHistory object) ∧
  (∀ object, state.capabilities.objects object ≠ true → state.mailbox object = none) ∧
  (∀ object envelope, envelope ∈ state.sendHistory object → envelope.endpoint = object)

inductive CreateError where
  | invalidSubject | outOfRange | occupiedSlot | objectInUse | objectAlreadyIssued
  deriving DecidableEq, Repr

inductive DestroyError where
  | invalidSubject | staleHandle | wrongKind | missingRevoke | retiredEndpoint
  deriving DecidableEq, Repr

inductive SendError where
  | invalidSubject | staleHandle | wrongKind | missingSend | retiredEndpoint | full
  deriving DecidableEq, Repr

inductive ReceiveError where
  | invalidSubject | staleHandle | wrongKind | missingReceive | retiredEndpoint | empty
  deriving DecidableEq, Repr

inductive Result (ε : Type) where | accepted | rejected (reason : ε)
  deriving DecidableEq, Repr

structure Outcome (ε : Type) where
  state : State
  result : Result ε

inductive ReceiveResult where
  | delivered (envelope : Envelope) | rejected (reason : ReceiveError)
  deriving DecidableEq, Repr

structure ReceiveOutcome where
  state : State
  result : ReceiveResult

def reject (state : State) (reason : ε) : Outcome ε :=
  { state, result := .rejected reason }

def rejectReceive (state : State) (reason : ReceiveError) : ReceiveOutcome :=
  { state, result := .rejected reason }

def setBool (values : ObjectId → Bool) (object : ObjectId) (value : Bool) :=
  fun candidate => if candidate = object then value else values candidate

def setOption (values : ObjectId → Option α) (object : ObjectId) (value : Option α) :=
  fun candidate => if candidate = object then value else values candidate

def appendHistory (history : ObjectId → List Envelope) (object : ObjectId)
    (envelope : Envelope) :=
  fun candidate => if candidate = object then history candidate ++ [envelope] else history candidate

def activate (state : Capability.State) (object : ObjectId) : Capability.State :=
  { state with
    objects := setBool state.objects object true
    kinds := fun candidate => if candidate = object then some .endpoint else state.kinds candidate }

def retire (state : Capability.State) (object : ObjectId) : Capability.State :=
  { state with
    objects := setBool state.objects object false
    kinds := fun candidate => if candidate = object then none else state.kinds candidate
    slots := fun subject slot =>
      match state.slots subject slot with
      | some cap => if cap.object = object then none else some cap
      | none => none }

def endpointRootRights : Capability.Rights :=
  { send := true, receive := true, grant := true, revoke := true }

/-- Create a fresh endpoint and install its root capability. -/
def create (state : State) (object : ObjectId) (subject : SubjectId) (slot : SlotId) :
    Outcome CreateError :=
  if state.capabilities.subjects subject != true then reject state .invalidSubject
  else if !Capability.slotInRange state.capabilities subject slot then reject state .outOfRange
  else if (state.capabilities.slots subject slot).isSome then reject state .occupiedSlot
  else if state.capabilities.objects object then reject state .objectInUse
  else if state.issued object || state.issuedAddressSpace object then
    reject state .objectAlreadyIssued
  else
    { state :=
        { state with
          capabilities := Capability.installRoot (activate state.capabilities object) subject slot
            object .endpoint endpointRootRights
          mailbox := setOption state.mailbox object none
          issued := setBool state.issued object true
          sendHistory := state.sendHistory }
      result := .accepted }

/-- Destroy an endpoint, atomically removing its mailbox and all capabilities. -/
def destroy (state : State) (subject : SubjectId) (slot : SlotId) : Outcome DestroyError :=
  match Capability.lookup state.capabilities subject slot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleHandle
  | .found cap =>
      if cap.kind != .endpoint then reject state .wrongKind
      else if !cap.rights.revoke then reject state .missingRevoke
      else if state.capabilities.objects cap.object != true then reject state .retiredEndpoint
      else if state.capabilities.kinds cap.object != some .endpoint then reject state .retiredEndpoint
      else
        { state := { state with
            capabilities := retire state.capabilities cap.object
            mailbox := setOption state.mailbox cap.object none }
          result := .accepted }

/-- Send one inert two-word payload using the trusted modeled caller identity. -/
def send (state : State) (caller : SubjectId) (slot : SlotId) (payload : Payload) :
    Outcome SendError :=
  match Capability.lookup state.capabilities caller slot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleHandle
  | .found cap =>
      if cap.kind != .endpoint then reject state .wrongKind
      else if !cap.rights.send then reject state .missingSend
      else if state.capabilities.objects cap.object != true then reject state .retiredEndpoint
      else if state.capabilities.kinds cap.object != some .endpoint then reject state .retiredEndpoint
      else if (state.mailbox cap.object).isSome then reject state .full
      else
        let envelope := { endpoint := cap.object, sender := caller, payload }
        { state := { state with
            mailbox := setOption state.mailbox cap.object (some envelope)
            sendHistory := appendHistory state.sendHistory cap.object envelope }
          result := .accepted }

/-- Receive and clear the oldest message. Capacity one makes FIFO explicit. -/
def receive (state : State) (caller : SubjectId) (slot : SlotId) : ReceiveOutcome :=
  match Capability.lookup state.capabilities caller slot with
  | .invalidSubject => rejectReceive state .invalidSubject
  | .staleSlot => rejectReceive state .staleHandle
  | .found cap =>
      if cap.kind != .endpoint then rejectReceive state .wrongKind
      else if !cap.rights.receive then rejectReceive state .missingReceive
      else if state.capabilities.objects cap.object != true then rejectReceive state .retiredEndpoint
      else if state.capabilities.kinds cap.object != some .endpoint then rejectReceive state .retiredEndpoint
      else match state.mailbox cap.object with
        | none => rejectReceive state .empty
        | some envelope =>
          { state := { state with mailbox := setOption state.mailbox cap.object none }
            result := .delivered envelope }

/-- Generation-checked holder-facing send boundary. -/
def sendHandle (state : State) (caller : SubjectId) (handle : CapabilityHandle.Handle)
    (payload : Payload) : Outcome SendError :=
  match CapabilityHandle.resolve state.capabilities caller handle .endpoint with
  | .error .invalidSubject => reject state .invalidSubject
  | .error _ => reject state .staleHandle
  | .ok _ => send state caller handle.slot payload

/-- Generation-checked holder-facing receive boundary. -/
def receiveHandle (state : State) (caller : SubjectId)
    (handle : CapabilityHandle.Handle) : ReceiveOutcome :=
  match CapabilityHandle.resolve state.capabilities caller handle .endpoint with
  | .error .invalidSubject => rejectReceive state .invalidSubject
  | .error _ => rejectReceive state .staleHandle
  | .ok _ => receive state caller handle.slot

/-- Generation-checked holder-facing endpoint destruction boundary. -/
def destroyHandle (state : State) (caller : SubjectId)
    (handle : CapabilityHandle.Handle) : Outcome DestroyError :=
  match CapabilityHandle.resolve state.capabilities caller handle .endpoint with
  | .error .invalidSubject => reject state .invalidSubject
  | .error _ => reject state .staleHandle
  | .ok _ => destroy state caller handle.slot

/-- States reachable from a valid empty-mailbox state. Non-send transitions may
remove messages but cannot introduce them; the only introducing event is an
accepted invocation of `send`. -/
inductive Reachable : State → Prop where
  | initial (state : State) (wellFormed : WellFormed state)
      (empty : ∀ object, state.mailbox object = none) : Reachable state
  | withoutSend (prior next : State) (reachable : Reachable prior)
      (wellFormed : WellFormed next)
      (noIntroduction : ∀ object envelope, next.mailbox object = some envelope →
        prior.mailbox object = some envelope) : Reachable next
  | acceptedSend (prior : State) (caller : SubjectId) (slot : SlotId) (payload : Payload)
      (reachable : Reachable prior)
      (accepted : (send prior caller slot payload).result = .accepted)
      (wellFormed : WellFormed (send prior caller slot payload).state) :
      Reachable (send prior caller slot payload).state

/-- Delegate through the shared capability policy; no IPC rule is duplicated. -/
def delegate (state : State) (actor : SubjectId) (source : SlotId)
    (destination : SubjectId) (destinationSlot : SlotId) (rights : Capability.Rights) :
    State × Capability.Result :=
  let outcome := Capability.copy state.capabilities actor source destination destinationSlot rights
  ({ state with capabilities := outcome.state }, outcome.result)

def delegateHandle (state : State) (actor : SubjectId) (source : CapabilityHandle.Handle)
    (destination : SubjectId) (destinationSlot : SlotId) (rights : Capability.Rights) :
    State × Capability.Result :=
  let outcome := CapabilityHandle.copy state.capabilities actor source .endpoint
    destination destinationSlot rights
  ({ state with capabilities := outcome.state }, outcome.result)

/-- Revoke through the shared capability policy. -/
def revoke (state : State) (actor : SubjectId) (authoritySlot : SlotId)
    (victim : SubjectId) (victimSlot : SlotId) : State × Capability.Result :=
  let outcome := Capability.revoke state.capabilities actor authoritySlot victim victimSlot
  ({ state with capabilities := outcome.state }, outcome.result)

def revokeHandle (state : State) (actor : SubjectId) (authority : CapabilityHandle.Handle)
    (victim : SubjectId) (target : CapabilityHandle.Handle) : State × Capability.Result :=
  let outcome := CapabilityHandle.revoke state.capabilities actor authority .endpoint victim target
  ({ state with capabilities := outcome.state }, outcome.result)

/-- Atomically revoke one endpoint-capability lineage through the shared store. -/
def revokeSubtree (state : State) (actor : SubjectId) (authoritySlot : SlotId)
    (victim : SubjectId) (victimSlot : SlotId) : State × Capability.Result :=
  let outcome := Capability.revokeSubtree state.capabilities actor authoritySlot victim victimSlot
  ({ state with capabilities := outcome.state }, outcome.result)

def revokeSubtreeHandle (state : State) (actor : SubjectId)
    (authority : CapabilityHandle.Handle) (victim : SubjectId)
    (target : CapabilityHandle.Handle) : State × Capability.Result :=
  let outcome := CapabilityHandle.revokeSubtree state.capabilities actor authority .endpoint
    victim target
  ({ state with capabilities := outcome.state }, outcome.result)

theorem revokeSubtree_preserves_wellFormed (state : State) actor authoritySlot victim victimSlot
    (hstate : WellFormed state) :
    WellFormed (revokeSubtree state actor authoritySlot victim victimSlot).1 := by
  refine ⟨Capability.revokeSubtree_preserves_wellFormed
    state.capabilities actor authoritySlot victim victimSlot hstate.1,
    ?_⟩
  have hregistry := Capability.revokeSubtree_preserves_registry
    state.capabilities actor authoritySlot victim victimSlot
  simp only [revokeSubtree]
  rw [hregistry.2.1, hregistry.2.2]
  exact hstate.2

theorem revokeSubtree_preserves_noncapability_state (state : State)
    actor authoritySlot victim victimSlot :
    let next := (revokeSubtree state actor authoritySlot victim victimSlot).1
    next.allocator = state.allocator ∧ next.binding = state.binding ∧
      next.issued = state.issued ∧ next.issuedAddressSpace = state.issuedAddressSpace ∧
      next.mailbox = state.mailbox ∧ next.sendHistory = state.sendHistory := by
  simp [revokeSubtree]

theorem revokeSubtree_rejected_unchanged (state : State) actor authoritySlot victim victimSlot reason
    (hrejected : (revokeSubtree state actor authoritySlot victim victimSlot).2 =
      .rejected reason) :
    (revokeSubtree state actor authoritySlot victim victimSlot).1 = state := by
  have hcaps := Capability.revokeSubtree_rejected_unchanged
    state.capabilities actor authoritySlot victim victimSlot reason (by
      simpa [revokeSubtree] using hrejected)
  simp [revokeSubtree, hcaps]

theorem create_rejected_unchanged (state : State) object subject slot reason
    (h : (create state object subject slot).result = .rejected reason) :
    (create state object subject slot).state = state := by
  simp only [create] at h ⊢
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> simp_all [reject]

theorem destroy_rejected_unchanged (state : State) subject slot reason
    (h : (destroy state subject slot).result = .rejected reason) :
    (destroy state subject slot).state = state := by
  simp only [destroy] at h ⊢
  split <;> try simp_all [reject]
  next cap =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> simp_all [reject]

theorem send_rejected_unchanged (state : State) caller slot payload reason
    (h : (send state caller slot payload).result = .rejected reason) :
    (send state caller slot payload).state = state := by
  simp only [send] at h ⊢
  split <;> try simp_all [reject]
  next cap =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> simp_all [reject]

theorem receive_rejected_unchanged (state : State) caller slot reason
    (h : (receive state caller slot).result = .rejected reason) :
    (receive state caller slot).state = state := by
  simp only [receive] at h ⊢
  split <;> try simp_all [rejectReceive]
  next cap =>
    split <;> try simp_all [rejectReceive]
    split <;> try simp_all [rejectReceive]
    split <;> try simp_all [rejectReceive]
    split <;> try simp_all [rejectReceive]
    split <;> simp_all [rejectReceive]

/-- Every create transition preserves the composite endpoint invariant. -/
theorem create_preserves_wellFormed (state : State) object subject slot
    (hstate : WellFormed state) :
    WellFormed (create state object subject slot).state := by
  simp only [create]
  split <;> try simpa [reject] using hstate
  split <;> try simpa [reject] using hstate
  split <;> try simpa [reject] using hstate
  split <;> try simpa [reject] using hstate
  split <;> try simpa [reject] using hstate
  change WellFormed
    { capabilities := Capability.installRoot (activate state.capabilities object) subject slot
        object .endpoint endpointRootRights
      allocator := state.allocator
      binding := state.binding
      issuedAddressSpace := state.issuedAddressSpace
      mailbox := setOption state.mailbox object none
      issued := setBool state.issued object true
      sendHistory := state.sendHistory }
  rcases hstate with ⟨hcaps, hissued, hmail, hdead, hhistory⟩
  have hsubject : state.capabilities.subjects subject = true := by simp_all
  have hobjectFree : state.capabilities.objects object = false := by simp_all
  refine ⟨?_, ?_, ?_, ?_, hhistory⟩
  · rcases hcaps with ⟨hslots, hderivations, hunique, hspaces⟩
    have hslotRange : Capability.slotInRange state.capabilities subject slot = true := by
      simp_all
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro candidate candidateSlot capability hslot
      by_cases htarget : candidate = subject ∧ candidateSlot = slot
      · rcases htarget with ⟨rfl, rfl⟩
        have hcapability : capability =
            (⟨object, .endpoint, endpointRootRights,
              state.capabilities.nextIdentity, none⟩ : Capability.Capability) := by
          simpa [Capability.installRoot, Capability.install, activate] using hslot.symm
        subst capability
        refine ⟨by simpa [Capability.installRoot, Capability.install, activate] using hsubject,
          by simp [Capability.installRoot, Capability.install, activate, setBool],
          by simp [Capability.installRoot, Capability.install, activate],
          by simp [Capability.rightsValid, endpointRootRights], Nat.lt_succ_self _, ?_, trivial⟩
        simp [Capability.installRoot, Capability.install, activate]
      · have hold : state.capabilities.slots candidate candidateSlot = some capability := by
          simpa [Capability.installRoot, Capability.install, activate, htarget] using hslot
        rcases hslots candidate candidateSlot capability hold with
          ⟨hsub, hlive, hkind, hrights, hid, hentry, hedge⟩
        have hne : capability.object ≠ object := by
          intro heq; subst object; simp_all
        refine ⟨by simpa [Capability.installRoot, Capability.install, activate] using hsub,
          by simpa [Capability.installRoot, Capability.install, activate, setBool, hne] using hlive,
          by simpa [Capability.installRoot, Capability.install, activate, hne] using hkind,
          hrights, Nat.lt_succ_of_lt hid, ?_, ?_⟩
        · simp [Capability.installRoot, Capability.install, activate, Nat.ne_of_lt hid, hentry]
        · cases hp : capability.parent <;> simp only [hp] at hedge ⊢
          rename_i parent
          rcases hedge with ⟨hparent, pp, pr, hpentry, hsubset⟩
          refine ⟨hparent, pp, pr, ?_, hsubset⟩
          simp [Capability.installRoot, Capability.install, activate,
            Nat.ne_of_lt (Nat.lt_trans hparent hid), hpentry]
    · intro identity parent candidateObject kind rights hentry
      by_cases hnew : identity = state.capabilities.nextIdentity
      · subst identity
        simp [Capability.installRoot, Capability.install, activate] at hentry
        rcases hentry with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨Nat.lt_succ_self _, trivial⟩
      · have hold := hderivations identity parent candidateObject kind rights (by
            simpa [Capability.installRoot, Capability.install, activate, hnew] using hentry)
        refine ⟨Nat.lt_succ_of_lt hold.1, ?_⟩
        cases parent with
        | none => trivial
        | some parentIdentity =>
            rcases hold.2 with ⟨hparent, pp, pr, hpentry, hsubset⟩
            refine ⟨hparent, pp, pr, ?_, hsubset⟩
            simp [Capability.installRoot, Capability.install, activate,
              Nat.ne_of_lt (Nat.lt_trans hparent hold.1), hpentry]
    · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
      by_cases hl : left = subject ∧ leftSlot = slot
      · by_cases hr : right = subject ∧ rightSlot = slot
        · exact ⟨hl.1.trans hr.1.symm, hl.2.trans hr.2.symm⟩
        · rcases hl with ⟨rfl, rfl⟩
          have hleftCap : leftCap =
              (⟨object, .endpoint, endpointRootRights,
                state.capabilities.nextIdentity, none⟩ : Capability.Capability) := by
            symm
            simpa [Capability.installRoot, Capability.install, activate] using hleft
          subst leftCap
          have hrc := hslots right rightSlot rightCap (by
            simpa [Capability.installRoot, Capability.install, activate, hr] using hright)
          have : state.capabilities.nextIdentity = rightCap.identity := by
            simpa using hid
          omega
      · by_cases hr : right = subject ∧ rightSlot = slot
        · rcases hr with ⟨rfl, rfl⟩
          have hrightCap : rightCap =
              (⟨object, .endpoint, endpointRootRights,
                state.capabilities.nextIdentity, none⟩ : Capability.Capability) := by
            symm
            simpa [Capability.installRoot, Capability.install, activate] using hright
          subst rightCap
          have hlc := hslots left leftSlot leftCap (by
            simpa [Capability.installRoot, Capability.install, activate, hl] using hleft)
          have : leftCap.identity = state.capabilities.nextIdentity := by
            simpa using hid
          omega
        · exact hunique left leftSlot leftCap right rightSlot rightCap
            (by simpa [Capability.installRoot, Capability.install, activate, hl] using hleft)
            (by simpa [Capability.installRoot, Capability.install, activate, hr] using hright) hid
    · intro candidate candidateSlot hout
      change state.capabilities.slotCapacity candidate ≤ candidateSlot at hout
      by_cases htarget : candidate = subject ∧ candidateSlot = slot
      · rcases htarget with ⟨rfl, rfl⟩
        have hlt : candidateSlot < state.capabilities.slotCapacity candidate := by
          simpa [Capability.slotInRange] using hslotRange
        omega
      · simpa [Capability.installRoot, Capability.install, activate, htarget] using
          hspaces candidate candidateSlot hout
  · intro candidate hlive hkind
    by_cases heq : candidate = object
    · subst candidate
      simp [setBool]
    · have hliveOld : state.capabilities.objects candidate = true := by
        simpa [Capability.installRoot, Capability.install, activate, setBool, heq] using hlive
      have hkindOld : state.capabilities.kinds candidate = some .endpoint := by
        simpa [Capability.installRoot, Capability.install, activate, heq] using hkind
      simpa [setBool, heq] using hissued candidate hliveOld hkindOld
  · intro candidate envelope hfound
    have hne : candidate ≠ object := by
      intro heq
      subst candidate
      simp [setOption] at hfound
    have hold := hmail candidate envelope (by simpa [setOption, hne] using hfound)
    exact ⟨by simpa [Capability.installRoot, Capability.install, activate, setBool, hne] using hold.1,
      by simpa [Capability.installRoot, Capability.install, activate, hne] using hold.2.1, hold.2.2⟩
  · intro candidate hnotlive
    by_cases heq : candidate = object
    · subst candidate
      simp [setOption]
    · have hold : state.capabilities.objects candidate ≠ true := by
        intro hlive
        apply hnotlive
        simpa [Capability.installRoot, Capability.install, activate, setBool, heq] using hlive
      simpa [setOption, heq] using hdead candidate hold

/-- Every accepted send preserves the composite endpoint invariant. -/
theorem send_preserves_wellFormed (state : State) caller slot payload
    (hstate : WellFormed state) :
    WellFormed (send state caller slot payload).state := by
  simp only [send]
  split <;> try simpa [reject] using hstate
  next cap hlookup =>
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    next hfree =>
      change WellFormed
        { capabilities := state.capabilities
          allocator := state.allocator
          binding := state.binding
          issuedAddressSpace := state.issuedAddressSpace
          mailbox := setOption state.mailbox cap.object
            (some { endpoint := cap.object, sender := caller, payload })
          issued := state.issued
          sendHistory := appendHistory state.sendHistory cap.object
            { endpoint := cap.object, sender := caller, payload } }
      rcases hstate with ⟨hcaps, hissued, hmail, hdead, hhistory⟩
      have hslot := Capability.lookup_found_slot state.capabilities caller slot cap hlookup
      have hcap := hcaps.1 caller slot cap hslot
      have hkind : cap.kind = .endpoint := by simp_all
      refine ⟨hcaps, hissued, ?_, ?_, ?_⟩
      · intro object envelope hfound
        by_cases heq : object = cap.object
        · subst object
          have henv : envelope =
              ({ endpoint := cap.object, sender := caller, payload := payload } : Envelope) := by
            simpa [setOption] using hfound.symm
          subst envelope
          exact ⟨hcap.2.1, by simpa [hkind] using hcap.2.2.1, rfl,
            by simp [appendHistory]⟩
        · have hold := hmail object envelope (by simpa [setOption, heq] using hfound)
          simpa [appendHistory, heq] using hold
      · intro object hnotlive
        have heq : object ≠ cap.object := by
          intro h
          subst object
          exact hnotlive hcap.2.1
        simpa [setOption, heq] using hdead object hnotlive
      · intro object envelope hmember
        by_cases heq : object = cap.object
        · subst object
          simp [appendHistory] at hmember
          rcases hmember with hmember | rfl
          · exact hhistory cap.object envelope hmember
          · rfl
        · exact hhistory object envelope (by simpa [appendHistory, heq] using hmember)

/-- Every receive transition preserves the composite endpoint invariant. -/
theorem receive_preserves_wellFormed (state : State) caller slot
    (hstate : WellFormed state) :
    WellFormed (receive state caller slot).state := by
  simp only [receive]
  split <;> try simpa [rejectReceive] using hstate
  next cap hlookup =>
    split <;> try simpa [rejectReceive] using hstate
    split <;> try simpa [rejectReceive] using hstate
    split <;> try simpa [rejectReceive] using hstate
    split <;> try simpa [rejectReceive] using hstate
    split <;> try simpa [rejectReceive] using hstate
    next envelope hqueued =>
      change WellFormed
        { capabilities := state.capabilities
          allocator := state.allocator
          binding := state.binding
          issuedAddressSpace := state.issuedAddressSpace
          mailbox := setOption state.mailbox cap.object none
          issued := state.issued
          sendHistory := state.sendHistory }
      rcases hstate with ⟨hcaps, hissued, hmail, hdead, hhistory⟩
      refine ⟨hcaps, hissued, ?_, ?_, hhistory⟩
      · intro object found hfound
        by_cases heq : object = cap.object
        · subst object
          simp [setOption] at hfound
        · exact hmail object found (by simpa [setOption, heq] using hfound)
      · intro object hnotlive
        by_cases heq : object = cap.object
        · subst object
          simp [setOption]
        · simpa [setOption, heq] using hdead object hnotlive

/-- Every destroy transition preserves the composite endpoint invariant. -/
theorem destroy_preserves_wellFormed (state : State) subject slot
    (hstate : WellFormed state) :
    WellFormed (destroy state subject slot).state := by
  simp only [destroy]
  split <;> try simpa [reject] using hstate
  next cap hlookup =>
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    split <;> try simpa [reject] using hstate
    change WellFormed
      { capabilities := retire state.capabilities cap.object
        allocator := state.allocator
        binding := state.binding
        issuedAddressSpace := state.issuedAddressSpace
        mailbox := setOption state.mailbox cap.object none
        issued := state.issued
        sendHistory := state.sendHistory }
    rcases hstate with ⟨hcaps, hissued, hmail, hdead, hhistory⟩
    refine ⟨?_, ?_, ?_, ?_, hhistory⟩
    · rcases hcaps with ⟨hslots, hderivations, hunique, hspaces⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro candidate candidateSlot found hslot
        cases hold : state.capabilities.slots candidate candidateSlot with
        | none => simp [retire, hold] at hslot
        | some existing =>
          by_cases heq : existing.object = cap.object
          · simp [retire, hold, heq] at hslot
          · have hfound : found = existing := by
              simpa [retire, hold, heq] using hslot.symm
            subst found
            rcases hslots candidate candidateSlot existing hold with
              ⟨hsub, hlive, hkind, hrest⟩
            exact ⟨hsub, by simpa [retire, setBool, heq] using hlive,
              by simpa [retire, heq] using hkind, hrest⟩
      · simpa [Capability.DerivationsWellFormed, retire] using hderivations
      · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
        have oldLeft : state.capabilities.slots left leftSlot = some leftCap := by
          cases hold : state.capabilities.slots left leftSlot with
          | none => simp [retire, hold] at hleft
          | some existing =>
            by_cases heq : existing.object = cap.object
            · simp [retire, hold, heq] at hleft
            · have : leftCap = existing := by
                simpa [retire, hold, heq] using hleft.symm
              simp [this] at hold ⊢
        have oldRight : state.capabilities.slots right rightSlot = some rightCap := by
          cases hold : state.capabilities.slots right rightSlot with
          | none => simp [retire, hold] at hright
          | some existing =>
            by_cases heq : existing.object = cap.object
            · simp [retire, hold, heq] at hright
            · have : rightCap = existing := by
                simpa [retire, hold, heq] using hright.symm
              simp [this] at hold ⊢
        exact hunique left leftSlot leftCap right rightSlot rightCap oldLeft oldRight hid
      · intro candidate candidateSlot hout
        have hempty := hspaces candidate candidateSlot hout
        simp [retire, hempty]
    · intro object hlive hkind
      have hne : object ≠ cap.object := by
        intro heq
        subst object
        simp [retire, setBool] at hlive
      apply hissued object
      · simpa [retire, setBool, hne] using hlive
      · simpa [retire, hne] using hkind
    · intro object envelope hfound
      have hne : object ≠ cap.object := by
        intro heq
        subst object
        simp [setOption] at hfound
      have hold := hmail object envelope (by simpa [setOption, hne] using hfound)
      exact ⟨by simpa [retire, setBool, hne] using hold.1,
        by simpa [retire, hne] using hold.2.1, hold.2.2⟩
    · intro object hnotlive
      by_cases heq : object = cap.object
      · subst object
        simp [setOption]
      · have hold : state.capabilities.objects object ≠ true := by
          intro hlive
          apply hnotlive
          simpa [retire, setBool, heq] using hlive
        simpa [setOption, heq] using hdead object hold

/-- Accepted send is possible only with current send authority for its endpoint. -/
theorem accepted_send_authorized (state : State) caller slot payload
    (h : (send state caller slot payload).result = .accepted) :
    ∃ object, Capability.HasAuthority state.capabilities caller object .send := by
  simp only [send] at h
  split at h <;> try contradiction
  next cap hlookup =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    have hsend : cap.rights.send = true := by
      cases hright : cap.rights.send <;> simp_all
    exact ⟨cap.object, slot, cap,
      Capability.lookup_found_slot state.capabilities caller slot cap hlookup, rfl,
      by simpa [Capability.hasRight, Capability.permits] using hsend⟩

/-- Accepted receive is possible only with current receive authority. -/
theorem delivered_receive_authorized (state : State) caller slot envelope
    (h : (receive state caller slot).result = .delivered envelope) :
    ∃ object, Capability.HasAuthority state.capabilities caller object .receive := by
  simp only [receive] at h
  split at h <;> try contradiction
  next cap hlookup =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    have hreceive : cap.rights.receive = true := by
      cases hright : cap.rights.receive <;> simp_all
    exact ⟨cap.object, slot, cap,
      Capability.lookup_found_slot state.capabilities caller slot cap hlookup, rfl,
      by simpa [Capability.hasRight, Capability.permits] using hreceive⟩

/-- The sender recorded by an accepted send is the trusted caller, not a word. -/
theorem accepted_send_records_caller (state : State) caller slot payload
    (h : (send state caller slot payload).result = .accepted) :
    ∃ object, (send state caller slot payload).state.mailbox object =
      some { endpoint := object, sender := caller, payload := payload } := by
  simp only [send] at h
  split at h <;> try contradiction
  next cap hlookup =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    exact ⟨cap.object, by simp [send, hlookup, setOption, *]⟩

/-- Every queued envelope in a reachable state was introduced by a concrete,
accepted send event from an earlier reachable state. -/
theorem reachable_mailbox_has_accepted_send (state : State) (hreach : Reachable state)
    object envelope (hmail : state.mailbox object = some envelope) :
    ∃ prior caller slot payload, Reachable prior ∧
      (send prior caller slot payload).result = .accepted ∧
      (send prior caller slot payload).state.mailbox object = some envelope ∧
      envelope = { endpoint := object, sender := caller, payload := payload } := by
  induction hreach with
  | initial state _ empty => simp [empty object] at hmail
  | withoutSend prior next _ _ noIntroduction ih =>
      exact ih (noIntroduction object envelope hmail)
  | acceptedSend prior eventCaller eventSlot eventPayload _ accepted _ ih =>
      simp only [send] at accepted
      split at accepted <;> try contradiction
      next cap hlookup =>
        split at accepted <;> try contradiction
        split at accepted <;> try contradiction
        split at accepted <;> try contradiction
        split at accepted <;> try contradiction
        split at accepted <;> try contradiction
        by_cases heq : object = cap.object
        · subst object
          have henv : envelope =
              ({ endpoint := cap.object, sender := eventCaller, payload := eventPayload } : Envelope) := by
            simpa [send, hlookup, setOption, *] using hmail.symm
          subst envelope
          exact ⟨prior, eventCaller, eventSlot, eventPayload,
            by assumption, by simp [send, hlookup, *],
            by simp [send, hlookup, setOption, *], rfl⟩
        · apply ih
          simpa [send, hlookup, setOption, heq, *] using hmail

/-- Delivery has event provenance from an accepted send in the reachable
execution, and that event records its trusted caller in the envelope. -/
theorem delivered_has_send_provenance (state : State) caller slot envelope
    (hreach : Reachable state)
    (h : (receive state caller slot).result = .delivered envelope) :
    ∃ prior sender senderSlot payload, Reachable prior ∧
      (send prior sender senderSlot payload).result = .accepted ∧
      (send prior sender senderSlot payload).state.mailbox envelope.endpoint = some envelope ∧
      envelope.sender = sender := by
  have hmail : ∃ object, state.mailbox object = some envelope := by
    simp only [receive] at h
    split at h <;> try contradiction
    next cap hlookup =>
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      next queued hqueued =>
        injection h with heq
        subst queued
        exact ⟨cap.object, hqueued⟩
  obtain ⟨object, hmailbox⟩ := hmail
  obtain ⟨prior, sender, senderSlot, payload, hprior, haccepted, hevent, henvelope⟩ :=
    reachable_mailbox_has_accepted_send state hreach object envelope hmailbox
  have hendpoint : envelope.endpoint = object := by
    cases hreach with
    | initial _ hwell _ => exact (hwell.2.2.1 object envelope hmailbox).2.2.1
    | withoutSend _ _ _ hwell _ => exact (hwell.2.2.1 object envelope hmailbox).2.2.1
    | acceptedSend _ _ _ _ _ _ hwell =>
        exact (hwell.2.2.1 object envelope hmailbox).2.2.1
  have hsender : envelope.sender = sender := by simp [henvelope]
  subst object
  exact ⟨prior, sender, senderSlot, payload, hprior, haccepted, hevent, hsender⟩

/-- Destruction clears queued data and every installed capability for the endpoint. -/
theorem destroy_clears (state : State) subject slot
    (h : (destroy state subject slot).result = .accepted) :
    ∃ object, (destroy state subject slot).state.mailbox object = none ∧
      (destroy state subject slot).state.capabilities.objects object = false ∧
      ∀ candidate candidateSlot cap,
        (destroy state subject slot).state.capabilities.slots candidate candidateSlot = some cap →
        cap.object ≠ object := by
  simp only [destroy] at h
  split at h <;> try contradiction
  next cap hlookup =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    refine ⟨cap.object, by simp [destroy, hlookup, setOption, *],
      by simp [destroy, hlookup, retire, setBool, *], ?_⟩
    intro candidate candidateSlot found hslot heq
    cases hs : state.capabilities.slots candidate candidateSlot with
    | none => simp [destroy, hlookup, retire, hs, *] at hslot
    | some existing =>
      by_cases hobject : existing.object = cap.object
      · simp [destroy, hlookup, retire, hs, hobject, *] at hslot
      · have : existing = found := by
          simpa [destroy, hlookup, retire, hs, hobject, *] using hslot
        subst found
        exact hobject heq

/-- Shared delegation cannot introduce any right absent from the source authority. -/
theorem delegate_no_authority_amplification (state : State) actor source destination
    destinationSlot rights candidate object right
    (h : Capability.HasAuthority
      (delegate state actor source destination destinationSlot rights).1.capabilities
      candidate object right) :
    Capability.HasAuthority state.capabilities candidate object right ∨
      Capability.HasAuthority state.capabilities actor object right := by
  exact Capability.copy_no_authority_amplification state.capabilities actor source destination
    destinationSlot rights candidate object right h

private def subjects : SubjectId → Bool := fun subject => subject < 3
private def memoryCap : Capability.Capability :=
  { object := 7, kind := .memory, rights := Capability.allRights }
private def initialCaps : Capability.State :=
  { subjects
    objects := fun object => object = 7
    kinds := fun object => if object = 7 then some .memory else none
    slots := fun subject slot => if subject = 0 ∧ slot = 9 then some memoryCap else none }
private def initial : State :=
  { capabilities := initialCaps
    allocator := { frames := [], status := fun _ => .reserved }
    binding := fun _ => none
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none, issued := fun _ => false
    sendHistory := fun _ => [] }
private def root := (create initial 10 0 0).state
private def sendOnly : Capability.Rights := { send := true }
private def receiveOnly : Capability.Rights := { receive := true }
private def withSender := (delegate root 0 0 1 0 sendOnly).1
private def withBoth := (delegate withSender 0 0 2 0 receiveOnly).1
private def payload : Payload := { word0 := 10, word1 := 0 }
private def sent := (send withBoth 1 0 payload).state

-- Successful round trip and capacity-one FIFO behavior.
example : (send withBoth 1 0 payload).result = .accepted := by native_decide
example : (send sent 1 0 payload).result = .rejected .full := by native_decide
example : (receive sent 2 0).result =
    .delivered { endpoint := 10, sender := 1, payload } := by native_decide
example : (receive withBoth 2 0).result = .rejected .empty := by native_decide
-- Send-only and receive-only delegation do not amplify authority.
example : (receive withBoth 1 0).result = .rejected .missingReceive := by native_decide
example : (send withBoth 2 0 payload).result = .rejected .missingSend := by native_decide
-- The payload may contain an object ID or forged sender word, but sender is trusted context.
example : (send withBoth 1 0 { word0 := 2, word1 := 10 }).state.mailbox 10 =
    some { endpoint := 10, sender := 1, payload := { word0 := 2, word1 := 10 } } := by
  native_decide
-- Wrong-kind handles fail closed.
example : (send root 0 9 payload).result = .rejected .staleHandle := by native_decide
-- Revocation before use removes the delegated endpoint authority.
private def revokedSender := (revoke withSender 0 0 1 0).1
example : (send revokedSender 1 0 payload).result = .rejected .staleHandle := by native_decide

-- End-to-end replay through the real send consumer: revoke generation 2,
-- install a different endpoint at the same slot, and reject the delayed handle.
private def rootHandle : CapabilityHandle.Handle := { slot := 0, identity := 1 }
private def oldSenderHandle : CapabilityHandle.Handle := { slot := 0, identity := 2 }
private def handleRevokedSender :=
  (revokeHandle withSender 0 rootHandle 1 oldSenderHandle).1
private def replacementSender := (create handleRevokedSender 11 1 0).state
private def replacementHandle : CapabilityHandle.Handle := { slot := 0, identity := 3 }
example : (sendHandle replacementSender 1 oldSenderHandle payload).result =
    .rejected .staleHandle := by native_decide
example : (sendHandle replacementSender 1 replacementHandle payload).result = .accepted := by
  native_decide
-- A sender cannot preserve authority by delegating before its lineage is revoked.
private def grantSend : Capability.Rights := { send := true, grant := true }
private def senderParent := (delegate root 0 0 1 0 grantSend).1
private def senderChild := (delegate senderParent 1 0 2 1 sendOnly).1
private def subtreeRevokedSender := (revokeSubtree senderChild 0 0 1 0).1
example : (send subtreeRevokedSender 1 0 payload).result = .rejected .staleHandle := by
  native_decide
example : (send subtreeRevokedSender 2 1 payload).result = .rejected .staleHandle := by
  native_decide
-- Destroy clears a pending message; the stale handle and retired ID cannot be replayed.
private def destroyed := (destroy sent 0 0).state
example : destroyed.mailbox 10 = none := by native_decide
example : (receive destroyed 2 0).result = .rejected .staleHandle := by native_decide
example : (destroy destroyed 0 0).result = .rejected .staleHandle := by native_decide
example : (create destroyed 10 0 0).result = .rejected .objectAlreadyIssued := by native_decide
-- A retired identifier from the composed address-space lifecycle is also unavailable.
private def retiredAddressSpaceHistory : State :=
  { initial with issuedAddressSpace := fun object => object = 11 }
example : (create retiredAddressSpaceHistory 11 0 0).result =
    .rejected .objectAlreadyIssued := by native_decide

end LeanOS.EndpointIPC
