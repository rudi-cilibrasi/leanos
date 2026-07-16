import LeanOS.EndpointIPC

/-!
# Sealed capability transfer over endpoint IPC

This bounded sequential model composes the endpoint mailbox with the one
authoritative capability derivation store.  An offer allocates an identity and
derivation record, but does not put the capability in any subject slot.  Thus
the sealed descendant cannot authorize an operation before atomic receipt.
-/
namespace LeanOS.CapabilityTransfer

open LeanOS
abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId
abbrev SlotId := Capability.SlotId

structure Sealed where
  identity : Nat
  parent : Nat
  /-- Trusted caller at offer time; never decoded from the payload. -/
  sender : SubjectId
  object : ObjectId
  kind : Capability.ObjectKind
  rights : Capability.Rights
  deriving DecidableEq, Repr

structure State extends toEndpointState : EndpointIPC.State where
  /-- At most one sealed descendant, indexed by its capacity-one mailbox. -/
  pending : ObjectId → Option Sealed

def WellFormed (state : State) : Prop :=
  EndpointIPC.WellFormed state.toEndpointState ∧
  ∀ endpoint transfer, state.pending endpoint = some transfer →
    (∃ envelope, state.mailbox endpoint = some envelope) ∧
    state.capabilities.objects transfer.object = true ∧
    state.capabilities.kinds transfer.object = some transfer.kind ∧
    Capability.rightsValid transfer.kind transfer.rights = true ∧
    state.capabilities.derivations transfer.identity =
      some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) ∧
    (∃ parentParent parentRights,
      state.capabilities.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) ∧
      Capability.rightsSubset transfer.rights parentRights = true) ∧
    transfer.parent < transfer.identity ∧ transfer.identity < state.capabilities.nextIdentity ∧
    (∀ subject slot cap, state.capabilities.slots subject slot = some cap →
      cap.identity ≠ transfer.identity)

/-- Observer-visible events. Payload data is retained, but it never supplies an
authority-bearing identifier. -/
inductive Event where
  | offered (endpoint identity : Nat) (sender : SubjectId) (payload : EndpointIPC.Payload)
  | received (endpoint identity : Nat) (receiver : SubjectId) (slot : SlotId)
  | canceled (endpoint identity : Nat)
  deriving DecidableEq, Repr

inductive OfferError where
  | invalidSubject | staleEndpoint | wrongEndpointKind | missingSend | retiredEndpoint | full
  | staleSource | missingGrant | emptyRights | rightsNotSubset
  deriving DecidableEq, Repr

inductive AcceptError where
  | invalidSubject | staleEndpoint | wrongEndpointKind | missingReceive | retiredEndpoint | empty
  | outOfRange | occupiedSlot | canceled
  deriving DecidableEq, Repr

inductive Result (ε : Type) where | accepted | rejected (reason : ε)
  deriving DecidableEq, Repr

structure Outcome (ε : Type) where
  state : State
  result : Result ε

def reject (state : State) (reason : ε) : Outcome ε := { state, result := .rejected reason }

def setPending (values : ObjectId → Option Sealed) endpoint value :=
  fun candidate => if candidate = endpoint then value else values candidate

/-- Offer one attenuated authority. Object, parent, and sender all come from
trusted slots/context; payload words remain inert. -/
def offer (state : State) (caller : SubjectId) (endpointSlot sourceSlot : SlotId)
    (payload : EndpointIPC.Payload) (rights : Capability.Rights) : Outcome OfferError :=
  match Capability.lookup state.capabilities caller endpointSlot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleEndpoint
  | .found endpointCap =>
    if endpointCap.kind != .endpoint then reject state .wrongEndpointKind
    else if !endpointCap.rights.send then reject state .missingSend
    else if state.capabilities.objects endpointCap.object != true then reject state .retiredEndpoint
    else if state.capabilities.kinds endpointCap.object != some .endpoint then reject state .retiredEndpoint
    else if (state.mailbox endpointCap.object).isSome then reject state .full
    else match Capability.lookup state.capabilities caller sourceSlot with
      | .invalidSubject => reject state .invalidSubject
      | .staleSlot => reject state .staleSource
      | .found source =>
        if !source.rights.grant then reject state .missingGrant
        else if !Capability.rightsValid source.kind rights then reject state .emptyRights
        else if !Capability.rightsSubset rights source.rights then reject state .rightsNotSubset
        else
          let identity := state.capabilities.nextIdentity
          let sealed : Sealed :=
            ⟨identity, source.identity, caller, source.object, source.kind, rights⟩
          let envelope : EndpointIPC.Envelope :=
            { endpoint := endpointCap.object, sender := caller, payload }
          { state := { state with
              capabilities := { state.capabilities with
                nextIdentity := identity + 1
                derivations := fun candidate => if candidate = identity then
                  some (some source.identity, source.object, source.kind, rights)
                  else state.capabilities.derivations candidate }
              mailbox := EndpointIPC.setOption state.mailbox endpointCap.object (some envelope)
              sendHistory := EndpointIPC.appendHistory state.sendHistory endpointCap.object envelope
              pending := setPending state.pending endpointCap.object (some sealed) }
            result := .accepted }

/-- Atomically consume the envelope and install its sealed descendant in the
trusted receiver's chosen empty slot. -/
def accept (state : State) (caller : SubjectId) (endpointSlot destinationSlot : SlotId) :
    Outcome AcceptError :=
  match Capability.lookup state.capabilities caller endpointSlot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleEndpoint
  | .found endpointCap =>
    if endpointCap.kind != .endpoint then reject state .wrongEndpointKind
    else if !endpointCap.rights.receive then reject state .missingReceive
    else if state.capabilities.objects endpointCap.object != true then reject state .retiredEndpoint
    else if state.capabilities.kinds endpointCap.object != some .endpoint then reject state .retiredEndpoint
    else match state.mailbox endpointCap.object with
      | none => reject state .empty
      | some _ =>
        if !Capability.slotInRange state.capabilities caller destinationSlot then
          reject state .outOfRange
        else if (state.capabilities.slots caller destinationSlot).isSome then
          reject state .occupiedSlot
        else match state.pending endpointCap.object with
          | none => reject state .canceled
          | some transfer =>
            if state.capabilities.objects transfer.object != true then reject state .canceled
            else if state.capabilities.kinds transfer.object != some transfer.kind then reject state .canceled
            else if state.capabilities.derivations transfer.identity !=
                some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) then
              reject state .canceled
            else if !Capability.rightsValid transfer.kind transfer.rights then reject state .canceled
            else
              let nextEndpoint : EndpointIPC.State :=
                { state.toEndpointState with
                  capabilities := Capability.install state.capabilities caller destinationSlot
                    ⟨transfer.object, transfer.kind, transfer.rights,
                      transfer.identity, some transfer.parent⟩
                  mailbox := EndpointIPC.setOption state.mailbox endpointCap.object none }
              { state :=
                  { toEndpointState := nextEndpoint
                    pending := setPending state.pending endpointCap.object none }
                result := .accepted }

/-- Remove offers selected by a lifetime/revocation policy. Derivation records
remain as append-only history, but no canceled identity can be installed. -/
def cancelWhere (state : State) (selected : Sealed → Bool) : State :=
  { state with
    mailbox := fun endpoint =>
      match state.pending endpoint with
      | some transfer => if selected transfer then none else state.mailbox endpoint
      | none => state.mailbox endpoint
    pending := fun endpoint =>
      match state.pending endpoint with
      | some transfer => if selected transfer then none else some transfer
      | none => none }

/-- Sender termination cancels its unaccepted offers. Receiver termination
needs no special record: the receiver is selected only by trusted accept
context and a terminated subject cannot pass capability lookup. -/
def terminateSender (state : State) (subject : SubjectId) : State :=
  cancelWhere state (fun transfer => transfer.sender = subject)

/-- Whole-object retirement invalidates every offer for that object. -/
def retireObject (state : State) (object : ObjectId) : State :=
  cancelWhere state (fun transfer => transfer.object = object)

/-- Endpoint destruction removes both its capacity-one envelope and any offer
whose transferred object is that endpoint. -/
def destroyEndpoint (state : State) (endpoint : ObjectId) : State :=
  let canceled := retireObject state endpoint
  { canceled with
    mailbox := EndpointIPC.setOption canceled.mailbox endpoint none
    pending := setPending canceled.pending endpoint none }

/-- A transitive revocation atomically clears installed descendants in the
authoritative store and sealed descendants in mailboxes. -/
noncomputable def revokeSubtree (state : State) (actor authoritySlot victim victimSlot : Nat) :
    State × Capability.Result :=
  match Capability.lookup state.capabilities victim victimSlot with
  | .found target =>
      let outcome := Capability.revokeSubtree state.capabilities actor authoritySlot victim victimSlot
      if outcome.result = .accepted then
        let canceled := cancelWhere state
          (fun transfer => Capability.descendsFrom state.capabilities transfer.identity target.identity
            state.capabilities.nextIdentity)
        ({ canceled with capabilities := outcome.state }, outcome.result)
      else (state, outcome.result)
  | _ => (state, (Capability.revokeSubtree state.capabilities actor authoritySlot victim victimSlot).result)

/-- Successful receipt consumes exactly its mailbox and installs its sealed
identity in the trusted caller's chosen slot. -/
theorem accepted_installs_exactly_once state caller endpointSlot destinationSlot
    (h : (accept state caller endpointSlot destinationSlot).result = .accepted) :
    ∃ endpoint transfer,
      state.pending endpoint = some transfer ∧
      (accept state caller endpointSlot destinationSlot).state.pending endpoint = none ∧
      (accept state caller endpointSlot destinationSlot).state.mailbox endpoint = none ∧
      (accept state caller endpointSlot destinationSlot).state.capabilities.slots
        caller destinationSlot = some
          ⟨transfer.object, transfer.kind, transfer.rights,
            transfer.identity, some transfer.parent⟩ := by
  simp only [accept] at h ⊢
  split at h <;> try contradiction
  next endpointCap hlookup =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    next envelope hmail =>
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      next transfer hpending =>
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        refine ⟨endpointCap.object, transfer, hpending, ?_, ?_, ?_⟩ <;>
          simp [setPending, EndpointIPC.setOption, Capability.install, *]

/-- Conservation follows directly from the strengthened pending invariant:
every sealed right is an attenuated child of its recorded parent. -/
theorem pending_rights_conserved state endpoint transfer
    (hstate : WellFormed state) (h : state.pending endpoint = some transfer) :
    ∃ parentParent parentRights,
      state.capabilities.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) ∧
      Capability.rightsSubset transfer.rights parentRights = true := by
  exact (hstate.2 endpoint transfer h).2.2.2.2.2.1

end LeanOS.CapabilityTransfer
