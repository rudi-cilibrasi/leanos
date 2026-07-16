import LeanOS.EndpointIPC

/-!
# Sealed capability transfer over endpoint IPC

This bounded sequential model composes the endpoint mailbox with the one
authoritative capability derivation store.  An offer allocates an identity and
derivation record, but does not put the capability in any subject slot.  Thus
the sealed descendant cannot authorize an operation before atomic receipt.
-/
namespace LeanOS.CapabilityTransfer

set_option linter.unusedSimpArgs false

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
    (∃ envelope, state.mailbox endpoint = some envelope ∧
      envelope.endpoint = endpoint ∧ envelope.sender = transfer.sender) ∧
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
      cap.identity ≠ transfer.identity) ∧
    (∀ other otherTransfer, state.pending other = some otherTransfer →
      otherTransfer.identity = transfer.identity → other = endpoint)

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

inductive AcceptResult where
  | delivered (envelope : EndpointIPC.Envelope)
  | rejected (reason : AcceptError)
  deriving DecidableEq, Repr

structure AcceptOutcome where
  state : State
  result : AcceptResult

def rejectAccept (state : State) (reason : AcceptError) : AcceptOutcome :=
  { state, result := .rejected reason }

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
    AcceptOutcome :=
  match Capability.lookup state.capabilities caller endpointSlot with
  | .invalidSubject => rejectAccept state .invalidSubject
  | .staleSlot => rejectAccept state .staleEndpoint
  | .found endpointCap =>
    if endpointCap.kind != .endpoint then rejectAccept state .wrongEndpointKind
    else if !endpointCap.rights.receive then rejectAccept state .missingReceive
    else if state.capabilities.objects endpointCap.object != true then rejectAccept state .retiredEndpoint
    else if state.capabilities.kinds endpointCap.object != some .endpoint then rejectAccept state .retiredEndpoint
    else match state.mailbox endpointCap.object with
      | none => rejectAccept state .empty
      | some envelope =>
        if !Capability.slotInRange state.capabilities caller destinationSlot then
          rejectAccept state .outOfRange
        else if (state.capabilities.slots caller destinationSlot).isSome then
          rejectAccept state .occupiedSlot
        else match state.pending endpointCap.object with
          | none => rejectAccept state .canceled
          | some transfer =>
            if state.capabilities.objects transfer.object != true then rejectAccept state .canceled
            else if state.capabilities.kinds transfer.object != some transfer.kind then rejectAccept state .canceled
            else if state.capabilities.derivations transfer.identity !=
                some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) then
              rejectAccept state .canceled
            else if !Capability.rightsValid transfer.kind transfer.rights then rejectAccept state .canceled
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
                result := .delivered envelope }

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

/-- Subject termination in this composition updates the authoritative subject
and slot store and cancels every envelope sent by that subject atomically. -/
def terminateSender (state : State) (subject : SubjectId) : State :=
  let transitioned : State := { state with
    capabilities := { state.capabilities with
      subjects := fun candidate => if candidate = subject then false
        else state.capabilities.subjects candidate
      slots := fun holder slot => if holder = subject then none
        else state.capabilities.slots holder slot } }
  cancelWhere transitioned (fun transfer => transfer.sender = subject)

/-- Retire a memory object through the authoritative allocator/lifetime
transition, then cancel its sealed descendants only when release succeeds. -/
def retireObject (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome MemoryLifecycle.ReleaseError :=
  match Capability.lookup state.capabilities subject slot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleSlot
  | .found cap =>
    let memoryState : MemoryLifecycle.State :=
      { capabilities := state.capabilities, allocator := state.allocator
        binding := state.binding, issued := state.issued }
    let released := MemoryLifecycle.release memoryState subject slot
    match released.result with
    | .rejected reason => reject state reason
    | .accepted =>
      let endpointState : EndpointIPC.State :=
        { capabilities := released.state.capabilities
          allocator := released.state.allocator
          binding := released.state.binding
          issued := released.state.issued
          issuedAddressSpace := state.issuedAddressSpace
          mailbox := state.mailbox
          sendHistory := state.sendHistory }
      let transitioned : State := { toEndpointState := endpointState, pending := state.pending }
      { state := cancelWhere transitioned (fun transfer => transfer.object = cap.object)
        result := .accepted }

/-- Destroy an endpoint through `EndpointIPC.destroy`, then cancel the
endpoint mailbox record and offers transferring that endpoint only on success. -/
def destroyEndpoint (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome EndpointIPC.DestroyError :=
  match Capability.lookup state.capabilities subject slot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleHandle
  | .found cap =>
    let destroyed := EndpointIPC.destroy state.toEndpointState subject slot
    match destroyed.result with
    | .rejected reason => reject state reason
    | .accepted =>
      let transitioned : State :=
        { toEndpointState := destroyed.state, pending := state.pending }
      let canceled := cancelWhere transitioned (fun transfer => transfer.object = cap.object)
      { state := { canceled with pending := setPending canceled.pending cap.object none }
        result := .accepted }

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

/-- Reserving an append-only derivation identity without installing it in a
slot preserves the authoritative capability invariant. -/
private theorem reserve_preserves_capabilityWellFormed (caps : Capability.State)
    (source : Capability.Capability) (rights : Capability.Rights)
    (hcaps : Capability.WellFormed caps)
    (hsource : ∃ subject slot, caps.slots subject slot = some source)
    (_hvalid : Capability.rightsValid source.kind rights = true)
    (hsubset : Capability.rightsSubset rights source.rights = true) :
    Capability.WellFormed { caps with
      nextIdentity := caps.nextIdentity + 1
      derivations := fun candidate => if candidate = caps.nextIdentity then
        some (some source.identity, source.object, source.kind, rights)
        else caps.derivations candidate } := by
  rcases hsource with ⟨subject, slot, hslot⟩
  rcases hcaps with ⟨hslots, hderivations, hunique, hspaces⟩
  have hs := hslots subject slot source hslot
  refine ⟨?_, ?_, hunique, hspaces⟩
  · intro holder candidateSlot cap hfound
    rcases hslots holder candidateSlot cap hfound with
      ⟨hlive, hobject, hkind, hrights, hid, hentry, hedge⟩
    refine ⟨hlive, hobject, hkind, hrights, Nat.lt_succ_of_lt hid, ?_, ?_⟩
    · simp [Nat.ne_of_lt hid, hentry]
    · cases hp : cap.parent <;> simp only [hp] at hedge ⊢
      rename_i parent
      rcases hedge with ⟨hparent, parentParent, parentRights, hpentry, hrightsSubset⟩
      refine ⟨hparent, parentParent, parentRights, ?_, hrightsSubset⟩
      simp [Nat.ne_of_lt (Nat.lt_trans hparent hid), hpentry]
  · intro identity parent object kind recordedRights hentry
    by_cases hnew : identity = caps.nextIdentity
    · subst identity
      simp at hentry
      rcases hentry with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨Nat.lt_succ_self _, hs.2.2.2.2.1, source.parent, source.rights,
        by simpa [Nat.ne_of_lt hs.2.2.2.2.1] using hs.2.2.2.2.2.1, hsubset⟩
    · have hold := hderivations identity parent object kind recordedRights (by
          simpa [hnew] using hentry)
      refine ⟨Nat.lt_succ_of_lt hold.1, ?_⟩
      cases parent with
      | none => trivial
      | some parentIdentity =>
          rcases hold.2 with ⟨hparent, parentParent, parentRights, hpentry, hrightsSubset⟩
          refine ⟨hparent, parentParent, parentRights, ?_, hrightsSubset⟩
          simp [Nat.ne_of_lt (Nat.lt_trans hparent hold.1), hpentry]

/-- Installing a previously reserved, globally unique identity into an empty
bounded slot preserves the authoritative capability invariant. -/
private theorem install_reserved_preserves_capabilityWellFormed
    (caps : Capability.State) (subject slot : Nat) (transfer : Sealed)
    (hcaps : Capability.WellFormed caps)
    (hsubject : caps.subjects subject = true)
    (hrange : Capability.slotInRange caps subject slot = true)
    (hempty : caps.slots subject slot = none)
    (hobject : caps.objects transfer.object = true)
    (hkind : caps.kinds transfer.object = some transfer.kind)
    (hrights : Capability.rightsValid transfer.kind transfer.rights = true)
    (hid : transfer.identity < caps.nextIdentity)
    (hparentLt : transfer.parent < transfer.identity)
    (hentry : caps.derivations transfer.identity =
      some (some transfer.parent, transfer.object, transfer.kind, transfer.rights))
    (hparent : ∃ parentParent parentRights,
      caps.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) ∧
      Capability.rightsSubset transfer.rights parentRights = true)
    (huniqueId : ∀ holder candidateSlot cap, caps.slots holder candidateSlot = some cap →
      cap.identity ≠ transfer.identity) :
    Capability.WellFormed (Capability.install caps subject slot
      ⟨transfer.object, transfer.kind, transfer.rights,
        transfer.identity, some transfer.parent⟩) := by
  rcases hcaps with ⟨hslots, hderivations, hunique, hspaces⟩
  refine ⟨?_, by simpa only [Capability.DerivationsWellFormed, Capability.install] using
    hderivations, ?_, ?_⟩
  · intro holder candidateSlot cap hslot
    by_cases htarget : holder = subject ∧ candidateSlot = slot
    · rcases htarget with ⟨rfl, rfl⟩
      have : cap = ⟨transfer.object, transfer.kind, transfer.rights,
          transfer.identity, some transfer.parent⟩ := by
        simpa [Capability.install] using hslot.symm
      subst cap
      exact ⟨by simpa [Capability.install] using hsubject, hobject, hkind, hrights,
        hid, by simpa [Capability.install] using hentry, ⟨hparentLt, hparent⟩⟩
    · have hold : caps.slots holder candidateSlot = some cap := by
        simpa [Capability.install, htarget] using hslot
      rcases hslots holder candidateSlot cap hold with
        ⟨hlive, hliveObject, hcapKind, hcapRights, hcapId, hcapEntry, hedge⟩
      exact ⟨by simpa [Capability.install] using hlive, hliveObject, hcapKind,
        hcapRights, hcapId, by simpa [Capability.install] using hcapEntry, hedge⟩
  · intro left leftSlot leftCap right rightSlot rightCap hleft hright heq
    by_cases hl : left = subject ∧ leftSlot = slot
    · by_cases hr : right = subject ∧ rightSlot = slot
      · exact ⟨hl.1.trans hr.1.symm, hl.2.trans hr.2.symm⟩
      · rcases hl with ⟨rfl, rfl⟩
        have hleftId : leftCap.identity = transfer.identity := by
          have : leftCap = ⟨transfer.object, transfer.kind, transfer.rights,
              transfer.identity, some transfer.parent⟩ := by
            simpa [Capability.install] using hleft.symm
          simp [this]
        have hold := huniqueId right rightSlot rightCap
          (by simpa [Capability.install, hr] using hright)
        exact False.elim (hold (heq.symm.trans hleftId))
    · by_cases hr : right = subject ∧ rightSlot = slot
      · rcases hr with ⟨rfl, rfl⟩
        have hrightId : rightCap.identity = transfer.identity := by
          have : rightCap = ⟨transfer.object, transfer.kind, transfer.rights,
              transfer.identity, some transfer.parent⟩ := by
            simpa [Capability.install] using hright.symm
          simp [this]
        exact False.elim (huniqueId left leftSlot leftCap
          (by simpa [Capability.install, hl] using hleft) (heq.trans hrightId))
      · exact hunique left leftSlot leftCap right rightSlot rightCap
          (by simpa [Capability.install, hl] using hleft)
          (by simpa [Capability.install, hr] using hright) heq
  · intro holder candidateSlot hout
    by_cases htarget : holder = subject ∧ candidateSlot = slot
    · rcases htarget with ⟨rfl, rfl⟩
      change caps.slotCapacity holder ≤ candidateSlot at hout
      exact False.elim (Nat.not_lt_of_ge hout
        (by simpa [Capability.slotInRange] using hrange))
    · simpa [Capability.install, htarget] using hspaces holder candidateSlot hout

set_option maxHeartbeats 800000 in
theorem offer_rejected_unchanged state caller endpointSlot sourceSlot payload rights reason
    (h : (offer state caller endpointSlot sourceSlot payload rights).result = .rejected reason) :
    (offer state caller endpointSlot sourceSlot payload rights).state = state := by
  simp only [offer] at h ⊢
  split <;> try simp_all [reject]
  next endpointCap =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    next source =>
      split <;> try simp_all [reject]
      split <;> try simp_all [reject]
      split <;> simp_all [reject]

set_option maxHeartbeats 800000 in
theorem accept_rejected_unchanged state caller endpointSlot destinationSlot reason
    (h : (accept state caller endpointSlot destinationSlot).result = .rejected reason) :
    (accept state caller endpointSlot destinationSlot).state = state := by
  simp only [accept] at h ⊢
  split <;> try simp_all [rejectAccept]
  next endpointCap =>
    split <;> try simp_all [rejectAccept]
    split <;> try simp_all [rejectAccept]
    split <;> try simp_all [rejectAccept]
    split <;> try simp_all [rejectAccept]
    split <;> try simp_all [rejectAccept]
    next envelope =>
      split <;> try simp_all [rejectAccept]
      split <;> try simp_all [rejectAccept]
      split <;> try simp_all [rejectAccept]
      next transfer =>
        split <;> try simp_all [rejectAccept]
        split <;> try simp_all [rejectAccept]
        split <;> try simp_all [rejectAccept]
        split <;> simp_all [rejectAccept]

/-- Successful receipt consumes exactly its mailbox and installs its sealed
identity in the trusted caller's chosen slot. -/
theorem delivered_installs_exactly_once state caller endpointSlot destinationSlot envelope
    (h : (accept state caller endpointSlot destinationSlot).result = .delivered envelope) :
    ∃ endpoint transfer,
      state.pending endpoint = some transfer ∧
      state.mailbox endpoint = some envelope ∧
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
        cases h
        refine ⟨endpointCap.object, transfer, hpending, hmail, ?_, ?_, ?_⟩ <;>
          simp [setPending, EndpointIPC.setOption, Capability.install, *]

/-- Delivery returns the exact envelope stored before the transition. In
particular, neither payload word participates in selecting installed authority. -/
theorem delivered_envelope_and_payload_independent state caller endpointSlot destinationSlot envelope
    (h : (accept state caller endpointSlot destinationSlot).result = .delivered envelope) :
    ∃ endpoint transfer,
      state.mailbox endpoint = some envelope ∧
      state.pending endpoint = some transfer ∧
      (accept state caller endpointSlot destinationSlot).state.capabilities.slots
        caller destinationSlot = some
          ⟨transfer.object, transfer.kind, transfer.rights,
            transfer.identity, some transfer.parent⟩ := by
  obtain ⟨endpoint, transfer, hpending, hmail, _, _, hslot⟩ :=
    delivered_installs_exactly_once state caller endpointSlot destinationSlot envelope h
  exact ⟨endpoint, transfer, hmail, hpending, hslot⟩

/-- Conservation follows directly from the strengthened pending invariant:
every sealed right is an attenuated child of its recorded parent. -/
theorem pending_rights_conserved state endpoint transfer
    (hstate : WellFormed state) (h : state.pending endpoint = some transfer) :
    ∃ parentParent parentRights,
      state.capabilities.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) ∧
      Capability.rightsSubset transfer.rights parentRights = true := by
  exact (hstate.2 endpoint transfer h).2.2.2.2.2.1

/-- For a well-formed pre-state, delivery installs the exact attenuated
descendant recorded beside the returned envelope. Payload is absent from every
authority-bearing equality. -/
theorem delivered_authority_conserved state caller endpointSlot destinationSlot envelope
    (hstate : WellFormed state)
    (h : (accept state caller endpointSlot destinationSlot).result = .delivered envelope) :
    ∃ endpoint, ∃ transfer : Sealed, ∃ parentParent parentRights,
      state.mailbox endpoint = some envelope ∧
      state.capabilities.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) ∧
      Capability.rightsSubset transfer.rights parentRights = true ∧
      (accept state caller endpointSlot destinationSlot).state.capabilities.slots
        caller destinationSlot = some
          ⟨transfer.object, transfer.kind, transfer.rights,
            transfer.identity, some transfer.parent⟩ := by
  obtain ⟨endpoint, transfer, hmail, hpending, hslot⟩ :=
    delivered_envelope_and_payload_independent state caller endpointSlot destinationSlot envelope h
  obtain ⟨parentParent, parentRights, hparent, hsubset⟩ :=
    pending_rights_conserved state endpoint transfer hstate hpending
  exact ⟨endpoint, transfer, parentParent, parentRights, hmail, hparent, hsubset, hslot⟩

end LeanOS.CapabilityTransfer
