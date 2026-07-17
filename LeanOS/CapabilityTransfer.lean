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

/-- Observer-visible events. Payload data is retained, but it never supplies an
authority-bearing identifier. -/
inductive Event where
  | dataSent (endpoint : ObjectId) (sender : SubjectId) (payload : EndpointIPC.Payload)
  | dataReceived (endpoint : ObjectId) (receiver : SubjectId)
  | offered (endpoint identity : Nat) (sender : SubjectId) (payload : EndpointIPC.Payload)
  | received (endpoint identity : Nat) (receiver : SubjectId) (slot : SlotId)
  | canceled (endpoint identity : Nat)
  deriving DecidableEq, Repr

structure Trace where
  events : ObjectId → List Event

structure State extends toEndpointState : EndpointIPC.State where
  /-- At most one sealed descendant, indexed by its capacity-one mailbox. -/
  pending : ObjectId → Option Sealed
  /-- Append-only observer trace, partitioned by endpoint so bulk cleanup does
  not require enumerating the functional endpoint namespace. -/
  trace : Trace := ⟨fun _ => []⟩

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

inductive OfferError where
  | invalidSubject | staleEndpoint | wrongEndpointKind | missingSend | retiredEndpoint | full
  | staleSource | missingGrant | emptyRights | rightsNotSubset | generationExhausted
  deriving DecidableEq, Repr

inductive AcceptError where
  | invalidSubject | staleEndpoint | wrongEndpointKind | missingReceive | retiredEndpoint | empty
  | outOfRange | occupiedSlot | canceled | generationExhausted
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

/-- Append one event to the endpoint-local observer trace. Keeping this update
behind a named operation prevents unrelated transition proofs from expanding
the functional trace representation. -/
def record (state : State) (endpoint : ObjectId) (event : Event) : State :=
  { state with
    trace := ⟨fun candidate => if candidate = endpoint then
      state.trace.events candidate ++ [event]
    else state.trace.events candidate⟩ }

/-- The accepted receipt update, kept separate from validation so rejection
proofs do not unfold the trace and capability-store mutations. -/
def deliver (state : State) (caller destinationSlot : Nat)
    (endpointCap : Capability.Capability) (envelope : EndpointIPC.Envelope)
    (transfer : Sealed) : AcceptOutcome :=
  let nextEndpoint : EndpointIPC.State :=
    { state.toEndpointState with
      capabilities := Capability.install state.capabilities caller destinationSlot
        ⟨transfer.object, transfer.kind, transfer.rights,
          transfer.identity, some transfer.parent⟩
      mailbox := EndpointIPC.setOption state.mailbox endpointCap.object none }
  { state := record
      { toEndpointState := nextEndpoint
        pending := setPending state.pending endpointCap.object none
        trace := state.trace }
      endpointCap.object
      (.received endpointCap.object transfer.identity caller destinationSlot)
    result := .delivered envelope }

/-- Consume an envelope that has no sealed descendant.  This is deliberately a
separate update from `deliver`: data receipt never inspects or changes a
destination capability slot. -/
def deliverData (state : State) (caller : SubjectId)
    (endpointCap : Capability.Capability) (envelope : EndpointIPC.Envelope) : AcceptOutcome :=
  { state := record
      { state with mailbox := EndpointIPC.setOption state.mailbox endpointCap.object none }
      endpointCap.object (.dataReceived endpointCap.object caller)
    result := .delivered envelope }

/-- Composite data-only send.  Callers must use this wrapper rather than
mutating the embedded endpoint state, so attachment metadata and the mailbox
remain one atomic tagged state. -/
def sendData (state : State) (caller : SubjectId) (endpointSlot : SlotId)
    (payload : EndpointIPC.Payload) : Outcome EndpointIPC.SendError :=
  let sent := EndpointIPC.send state.toEndpointState caller endpointSlot payload
  match sent.result with
  | .rejected reason => reject state reason
  | .accepted =>
      match Capability.lookup state.capabilities caller endpointSlot with
      | .found endpointCap =>
          { state := record
              { toEndpointState := sent.state, pending := state.pending, trace := state.trace }
              endpointCap.object (.dataSent endpointCap.object caller payload)
            result := .accepted }
      | _ => reject state .staleHandle

/-- Generation-checked holder-facing data send. Reusing the numbered endpoint
slot cannot redirect an old request to a replacement endpoint. -/
def sendDataHandle (state : State) (caller : SubjectId)
    (endpoint : CapabilityHandle.Handle) (payload : EndpointIPC.Payload) :
    Outcome EndpointIPC.SendError :=
  match CapabilityHandle.resolve state.capabilities caller endpoint .endpoint with
  | .error .invalidSubject => reject state .invalidSubject
  | .error _ => reject state .staleHandle
  | .ok _ => sendData state caller endpoint.slot payload

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
          { state := record { state with
              capabilities := { state.capabilities with
                nextIdentity := identity + 1
                derivations := fun candidate => if candidate = identity then
                  some (some source.identity, source.object, source.kind, rights)
                  else state.capabilities.derivations candidate }
              mailbox := EndpointIPC.setOption state.mailbox endpointCap.object (some envelope)
              sendHistory := EndpointIPC.appendHistory state.sendHistory endpointCap.object envelope
              pending := setPending state.pending endpointCap.object (some sealed) }
              endpointCap.object (.offered endpointCap.object identity caller payload)
            result := .accepted }

/-- Holder-facing offer. Both authority-consuming references are generation
checked before the raw-slot transition runs, so reusing either numbered slot
cannot redirect an old request to replacement authority. `sourceKind` is
trusted operation metadata, not payload data. -/
def offerHandles (state : State) (caller : SubjectId)
    (endpoint source : CapabilityHandle.Handle)
    (sourceKind : Capability.ObjectKind) (payload : EndpointIPC.Payload)
    (rights : Capability.Rights) : Outcome OfferError :=
  match CapabilityHandle.resolve state.capabilities caller endpoint .endpoint with
  | .error .invalidSubject => reject state .invalidSubject
  | .error .kindMismatch => reject state .wrongEndpointKind
  | .error _ => reject state .staleEndpoint
  | .ok _ =>
      match CapabilityHandle.resolve state.capabilities caller source sourceKind with
      | .error .invalidSubject => reject state .invalidSubject
      | .error _ => reject state .staleSource
      | .ok _ =>
          if state.capabilities.nextIdentity = 0 ∨
              CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity then
            reject state .generationExhausted
          else offer state caller endpoint.slot source.slot payload rights

/-- Userspace capability-transfer boundary. Both opaque words are decoded and
resolved in the trusted caller's capability space before the internal slot
transition can observe either authority. -/
def offerWords (state : State) (caller : SubjectId)
    (endpointWord sourceWord : UInt64) (sourceKind : Capability.ObjectKind)
    (payload : EndpointIPC.Payload) (rights : Capability.Rights) : Outcome OfferError :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord .endpoint with
  | .error (.denied .invalidSubject) => reject state .invalidSubject
  | .error (.denied .kindMismatch) => reject state .wrongEndpointKind
  | .error _ => reject state .staleEndpoint
  | .ok endpoint =>
      match CapabilityHandle.resolveCurrent state.capabilities { caller } sourceWord sourceKind with
      | .error (.denied .invalidSubject) => reject state .invalidSubject
      | .error _ => reject state .staleSource
      | .ok source =>
          if state.capabilities.nextIdentity = 0 ∨
              CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity then
            reject state .generationExhausted
          else offer state caller endpoint.handle.slot source.handle.slot payload rights

/-- Acceptance at the userspace transfer boundary records both successful
full-word resolutions before the raw-slot transition. -/
theorem offerWords_accepted_resolves state caller endpointWord sourceWord sourceKind
    payload rights
    (haccepted : (offerWords state caller endpointWord sourceWord sourceKind
      payload rights).result = .accepted) :
    ∃ endpoint source,
      CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord .endpoint =
        .ok endpoint ∧
      CapabilityHandle.resolveCurrent state.capabilities { caller } sourceWord sourceKind =
        .ok source ∧
      (offer state caller endpoint.handle.slot source.handle.slot payload rights).result =
        .accepted := by
  cases hendpoint : CapabilityHandle.resolveCurrent state.capabilities
      { caller } endpointWord .endpoint with
  | error reason =>
      cases reason with
      | malformed decodeReason => simp [offerWords, hendpoint, reject] at haccepted
      | denied resolveReason =>
          cases resolveReason <;> simp [offerWords, hendpoint, reject] at haccepted
  | ok endpoint =>
      cases hsource : CapabilityHandle.resolveCurrent state.capabilities
          { caller } sourceWord sourceKind with
      | error reason =>
          cases reason with
          | malformed decodeReason =>
              simp [offerWords, hendpoint, hsource, reject] at haccepted
          | denied resolveReason =>
              cases resolveReason <;>
                simp [offerWords, hendpoint, hsource, reject] at haccepted
      | ok source =>
          by_cases hgeneration : state.capabilities.nextIdentity = 0 ∨
              CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity
          · simp [offerWords, hendpoint, hsource, hgeneration, reject] at haccepted
          · exact ⟨endpoint, source, rfl, rfl,
              by simpa [offerWords, hendpoint, hsource, hgeneration] using haccepted⟩

/-- An accepted userspace offer reserves an identity inside the canonical
48-bit generation domain, so every usable destination slot can encode the
eventual installed descendant without truncation. -/
theorem offerWords_accepted_generation_encodable state caller endpointWord sourceWord sourceKind
    payload rights destinationSlot
    (hslot : destinationSlot < CapabilityHandle.slotReserved)
    (haccepted : (offerWords state caller endpointWord sourceWord sourceKind
      payload rights).result = .accepted) :
    ∃ word, CapabilityHandle.encode
      { slot := destinationSlot, identity := state.capabilities.nextIdentity } = some word := by
  cases hendpoint : CapabilityHandle.resolveCurrent state.capabilities
      { caller } endpointWord .endpoint with
  | error reason =>
      cases reason with
      | malformed decodeReason => simp [offerWords, hendpoint, reject] at haccepted
      | denied resolveReason =>
          cases resolveReason <;> simp [offerWords, hendpoint, reject] at haccepted
  | ok endpoint =>
      cases hsource : CapabilityHandle.resolveCurrent state.capabilities
          { caller } sourceWord sourceKind with
      | error reason =>
          cases reason with
          | malformed decodeReason =>
              simp [offerWords, hendpoint, hsource, reject] at haccepted
          | denied resolveReason =>
              cases resolveReason <;>
                simp [offerWords, hendpoint, hsource, reject] at haccepted
      | ok source =>
          by_cases hexhausted : state.capabilities.nextIdentity = 0 ∨
              CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity
          · simp [offerWords, hendpoint, hsource, hexhausted, reject] at haccepted
          · have hpositive : 0 < state.capabilities.nextIdentity :=
              Nat.pos_of_ne_zero (fun hzero => hexhausted (Or.inl hzero))
            have hgeneration : state.capabilities.nextIdentity <
                CapabilityHandle.generationReserved :=
              Nat.lt_of_not_ge (fun hge => hexhausted (Or.inr hge))
            refine ⟨UInt64.ofNat (destinationSlot +
              state.capabilities.nextIdentity * CapabilityHandle.slotRadix), ?_⟩
            simp [CapabilityHandle.encode, CapabilityHandle.Encodable,
              hslot, hpositive, hgeneration]

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
        match state.pending endpointCap.object with
        | none => deliverData state caller endpointCap envelope
        | some transfer =>
          if !Capability.slotInRange state.capabilities caller destinationSlot then
            rejectAccept state .outOfRange
          else if (state.capabilities.slots caller destinationSlot).isSome then
            rejectAccept state .occupiedSlot
          else
            if state.capabilities.objects transfer.object != true then rejectAccept state .canceled
            else if state.capabilities.kinds transfer.object != some transfer.kind then rejectAccept state .canceled
            else if state.capabilities.derivations transfer.identity !=
                some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) then
              rejectAccept state .canceled
            else if !Capability.rightsValid transfer.kind transfer.rights then rejectAccept state .canceled
            else deliver state caller destinationSlot endpointCap envelope transfer

/-- Holder-facing receipt. The endpoint generation is selected before the
raw-slot transition; the destination remains an empty slot chosen for output,
so it intentionally has no pre-existing generation handle. -/
def acceptHandle (state : State) (caller : SubjectId)
    (endpoint : CapabilityHandle.Handle) (destinationSlot : SlotId) : AcceptOutcome :=
  match CapabilityHandle.resolve state.capabilities caller endpoint .endpoint with
  | .error .invalidSubject => rejectAccept state .invalidSubject
  | .error .kindMismatch => rejectAccept state .wrongEndpointKind
  | .error _ => rejectAccept state .staleEndpoint
  | .ok endpointCap =>
      match state.pending endpointCap.object with
        | some transfer =>
            if CapabilityHandle.slotReserved ≤ destinationSlot then
              rejectAccept state .outOfRange
            else if transfer.identity = 0 ∨
                CapabilityHandle.generationReserved ≤ transfer.identity then
              rejectAccept state .generationExhausted
            else accept state caller endpoint.slot destinationSlot
        | none => accept state caller endpoint.slot destinationSlot

/-- Userspace receipt boundary. The destination is only an empty bounded output
slot; the authority-consuming endpoint reference must be a canonical word. -/
def acceptWord (state : State) (caller : SubjectId) (endpointWord : UInt64)
    (destinationSlot : SlotId) : AcceptOutcome :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord .endpoint with
  | .error (.denied .invalidSubject) => rejectAccept state .invalidSubject
  | .error (.denied .kindMismatch) => rejectAccept state .wrongEndpointKind
  | .error _ => rejectAccept state .staleEndpoint
  | .ok endpoint =>
      match state.pending endpoint.capability.object with
        | some transfer =>
            if CapabilityHandle.slotReserved ≤ destinationSlot then
              rejectAccept state .outOfRange
            else if transfer.identity = 0 ∨
                CapabilityHandle.generationReserved ≤ transfer.identity then
              rejectAccept state .generationExhausted
            else accept state caller endpoint.handle.slot destinationSlot
        | none => accept state caller endpoint.handle.slot destinationSlot

/-- Every delivered userspace receipt selected a canonical endpoint word. If
the mailbox carried sealed authority, its destination and exact pending
generation also admit a canonical installed-handle encoding. -/
theorem acceptWord_delivered_boundary_encodable state caller endpointWord destinationSlot envelope
    (hdelivered : (acceptWord state caller endpointWord destinationSlot).result =
      .delivered envelope) :
    ∃ endpoint,
      CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord .endpoint =
        .ok endpoint ∧
      (match state.pending endpoint.capability.object with
        | none => True
        | some transfer => destinationSlot < CapabilityHandle.slotReserved ∧
            ∃ word, CapabilityHandle.encode
              { slot := destinationSlot, identity := transfer.identity } = some word) := by
  cases hendpoint : CapabilityHandle.resolveCurrent state.capabilities
      { caller } endpointWord .endpoint with
  | error reason =>
      cases reason with
      | malformed decodeReason => simp [acceptWord, hendpoint, rejectAccept] at hdelivered
      | denied resolveReason =>
          cases resolveReason <;> simp [acceptWord, hendpoint, rejectAccept] at hdelivered
  | ok endpoint =>
      refine ⟨endpoint, rfl, ?_⟩
      cases hpending : state.pending endpoint.capability.object with
      | none => simp [hpending]
      | some transfer =>
          by_cases hslot : CapabilityHandle.slotReserved ≤ destinationSlot
          · simp [acceptWord, hendpoint, hslot, hpending, rejectAccept] at hdelivered
          · refine ⟨Nat.lt_of_not_ge hslot, ?_⟩
            by_cases hexhausted : transfer.identity = 0 ∨
                CapabilityHandle.generationReserved ≤ transfer.identity
            · simp [acceptWord, hendpoint, hslot, hpending, hexhausted,
                rejectAccept] at hdelivered
            · have hpositive : 0 < transfer.identity :=
                Nat.pos_of_ne_zero (fun hzero => hexhausted (Or.inl hzero))
              have hgeneration : transfer.identity < CapabilityHandle.generationReserved :=
                Nat.lt_of_not_ge (fun hge => hexhausted (Or.inr hge))
              refine ⟨UInt64.ofNat (destinationSlot +
                transfer.identity * CapabilityHandle.slotRadix), ?_⟩
              simp [CapabilityHandle.encode, CapabilityHandle.Encodable,
                Nat.lt_of_not_ge hslot, hpositive, hgeneration]

theorem offerHandles_stale_source_rejected state caller endpoint source sourceKind
    payload rights endpointCap
    (hendpoint : CapabilityHandle.resolve state.capabilities caller endpoint .endpoint =
      .ok endpointCap)
    (hsource : CapabilityHandle.resolve state.capabilities caller source sourceKind =
      .error .staleHandle) :
    (offerHandles state caller endpoint source sourceKind payload rights).result =
      .rejected .staleSource := by
  simp [offerHandles, hendpoint, hsource, reject]

/-- A rejected data-only send is fully atomic, including its observer trace. -/
theorem sendData_rejected_unchanged state caller endpointSlot payload reason
    (h : (sendData state caller endpointSlot payload).result = .rejected reason) :
    (sendData state caller endpointSlot payload).state = state := by
  simp only [sendData] at h ⊢
  split <;> try simp_all [reject]
  next sent hsent =>
    split <;> simp_all [reject]

/-- Every accepted data-only send appends exactly its public send event to the
endpoint selected by trusted caller authority. -/
theorem sendData_accepted_records state caller endpointSlot payload
    (h : (sendData state caller endpointSlot payload).result = .accepted) :
    ∃ endpointCap,
      Capability.lookup state.capabilities caller endpointSlot = .found endpointCap ∧
      (sendData state caller endpointSlot payload).state.trace.events endpointCap.object =
        state.trace.events endpointCap.object ++
          [.dataSent endpointCap.object caller payload] := by
  simp only [sendData] at h ⊢
  split at h <;> try contradiction
  next sent hsent =>
    split at h <;> try contradiction
    next endpointCap hlookup =>
      cases h
      refine ⟨endpointCap, hlookup, ?_⟩
      simp [record]

/-- In a well-formed composite state, an accepted data-only send cannot reuse
an endpoint carrying sealed attachment metadata.  Its selected endpoint remains
explicitly untagged, so the matching receive takes the data-only path. -/
theorem sendData_accepted_unattached state caller endpointSlot payload
    (hstate : WellFormed state)
    (h : (sendData state caller endpointSlot payload).result = .accepted) :
    ∃ endpointCap,
      Capability.lookup state.capabilities caller endpointSlot = .found endpointCap ∧
      (sendData state caller endpointSlot payload).state.pending endpointCap.object = none := by
  simp only [sendData] at h ⊢
  split at h <;> try contradiction
  next sent hsent =>
    split at h <;> try contradiction
    next endpointCap hlookup =>
      cases h
      refine ⟨endpointCap, hlookup, ?_⟩
      simp only [record]
      change state.pending endpointCap.object = none
      have hempty : state.mailbox endpointCap.object = none := by
        simp only [EndpointIPC.send] at hsent
        split at hsent <;> try contradiction
        next cap hcap =>
          split at hsent <;> try contradiction
          split at hsent <;> try contradiction
          split at hsent <;> try contradiction
          split at hsent <;> try contradiction
          split at hsent <;> try contradiction
          next hfree =>
            have : cap = endpointCap := by
              rw [hcap] at hlookup
              cases hlookup
              rfl
            subst cap
            cases hm : state.mailbox endpointCap.object with
            | none => rfl
            | some _ => simp [hm] at hfree
      cases hpending : state.pending endpointCap.object with
      | none => rfl
      | some transfer =>
          obtain ⟨envelope, hmail, _⟩ := (hstate.2 endpointCap.object transfer hpending).1
          simp [hempty] at hmail

private theorem endpointSend_capabilities_unchanged state caller slot payload :
    (EndpointIPC.send state caller slot payload).state.capabilities = state.capabilities := by
  simp only [EndpointIPC.send]
  split <;> try rfl
  next cap hlookup =>
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> rfl

private theorem endpointSend_preserves_occupied_mailbox state caller slot payload endpoint envelope
    (hmail : state.mailbox endpoint = some envelope) :
    (EndpointIPC.send state caller slot payload).state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.send]
  split <;> try simpa [EndpointIPC.reject] using hmail
  next cap hlookup =>
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    next hfree =>
      have hne : endpoint ≠ cap.object := by
        intro heq
        subst endpoint
        simp [hmail] at hfree
      simpa [EndpointIPC.setOption, hne] using hmail

/-- Data-only send preserves the complete composite invariant, not merely the
embedded endpoint invariant. In particular, an accepted send cannot overwrite
the mailbox corresponding to any existing sealed attachment. -/
theorem sendData_preserves_wellFormed state caller endpointSlot payload
    (hstate : WellFormed state) :
    WellFormed (sendData state caller endpointSlot payload).state := by
  simp only [sendData]
  split <;> try simpa [reject] using hstate
  next sent hsent =>
    split <;> try simpa [reject] using hstate
    next endpointCap hlookup =>
      refine ⟨?_, ?_⟩
      · simpa [record] using
          EndpointIPC.send_preserves_wellFormed state.toEndpointState caller endpointSlot payload
            hstate.1
      · intro endpoint transfer hpending
        simp only [record] at hpending ⊢
        have hold := hstate.2 endpoint transfer hpending
        rcases hold with ⟨⟨envelope, hmail, hendpoint, hsender⟩, hrest⟩
        rw [endpointSend_capabilities_unchanged] at ⊢
        exact ⟨⟨envelope,
          endpointSend_preserves_occupied_mailbox _ _ _ _ _ _ hmail,
          hendpoint, hsender⟩, hrest⟩

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
      | none => none
    trace := ⟨fun endpoint =>
      match state.pending endpoint with
      | some transfer => if selected transfer then
          state.trace.events endpoint ++ [.canceled endpoint transfer.identity]
        else state.trace.events endpoint
      | none => state.trace.events endpoint⟩ }

/-- Cancel offers made by one sender without claiming to terminate that
subject.  Authoritative termination belongs to `SubjectLifecycle`, whose
ownership and scheduling state is deliberately not embedded in this model. -/
def cancelSenderOffers (state : State) (subject : SubjectId) : State :=
  cancelWhere state (fun transfer => transfer.sender = subject)

/-- Sender-offer cancellation changes exactly those pending records whose
trusted sender is the selected subject. -/
theorem cancelSenderOffers_pending state subject endpoint transfer
    (h : state.pending endpoint = some transfer) :
    (cancelSenderOffers state subject).pending endpoint =
      if transfer.sender = subject then none else some transfer := by
  simp [cancelSenderOffers, cancelWhere, h]

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
      let transitioned : State :=
        { toEndpointState := endpointState, pending := state.pending, trace := state.trace }
      { state := cancelWhere transitioned (fun transfer => transfer.object = cap.object)
        result := .accepted }

/-- Generation-checked holder-facing memory retirement. -/
def retireObjectHandle (state : State) (subject : SubjectId)
    (handle : CapabilityHandle.Handle) : Outcome MemoryLifecycle.ReleaseError :=
  match CapabilityHandle.resolve state.capabilities subject handle .memory with
  | .error .invalidSubject => reject state .invalidSubject
  | .error .kindMismatch => reject state .kindMismatch
  | .error _ => reject state .staleSlot
  | .ok _ => retireObject state subject handle.slot

/-- Userspace memory-retirement boundary using the shared canonical decoder. -/
def retireObjectWord (state : State) (subject : SubjectId) (word : UInt64) :
    Outcome MemoryLifecycle.ReleaseError :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller := subject } word .memory with
  | .error (.denied .invalidSubject) => reject state .invalidSubject
  | .error (.denied .kindMismatch) => reject state .kindMismatch
  | .error _ => reject state .staleSlot
  | .ok resolution => retireObject state subject resolution.handle.slot

/-- Cancel the attachment occupying one endpoint, independent of the kind or
object carried by that attachment. -/
def cancelEndpointOffer (state : State) (endpoint : ObjectId) : State :=
  match state.pending endpoint with
  | none => state
  | some transfer => record
      { state with
        mailbox := EndpointIPC.setOption state.mailbox endpoint none
        pending := setPending state.pending endpoint none }
      endpoint (.canceled endpoint transfer.identity)

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
      let endpointCanceled := cancelEndpointOffer state cap.object
      let canceled := cancelWhere endpointCanceled (fun transfer => transfer.object = cap.object)
      let nextEndpoint : EndpointIPC.State :=
        { destroyed.state with mailbox := canceled.mailbox }
      let next : State :=
        { toEndpointState := nextEndpoint
          pending := canceled.pending
          trace := canceled.trace }
      { state := next, result := .accepted }

/-- Generation-checked holder-facing endpoint destruction. -/
def destroyEndpointHandle (state : State) (subject : SubjectId)
    (handle : CapabilityHandle.Handle) : Outcome EndpointIPC.DestroyError :=
  match CapabilityHandle.resolve state.capabilities subject handle .endpoint with
  | .error .invalidSubject => reject state .invalidSubject
  | .error .kindMismatch => reject state .wrongKind
  | .error _ => reject state .staleHandle
  | .ok _ => destroyEndpoint state subject handle.slot

/-- Userspace endpoint-destruction boundary using the same canonical word
decoder as map, IPC send/receive, and capability transfer. -/
def destroyEndpointWord (state : State) (subject : SubjectId) (word : UInt64) :
    Outcome EndpointIPC.DestroyError :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller := subject } word .endpoint with
  | .error (.denied .invalidSubject) => reject state .invalidSubject
  | .error (.denied .kindMismatch) => reject state .wrongKind
  | .error _ => reject state .staleHandle
  | .ok resolution => destroyEndpoint state subject resolution.handle.slot

/-- Decode or generation denial at destruction is state preserving and cannot
reach the raw endpoint-lifetime transition. -/
theorem destroyEndpointWord_resolution_rejected_unchanged state subject word reason
    (hresolve : CapabilityHandle.resolveCurrent state.capabilities
      { caller := subject } word .endpoint = .error reason) :
    (destroyEndpointWord state subject word).state = state := by
  cases reason with
  | malformed decodeReason => simp [destroyEndpointWord, hresolve, reject]
  | denied resolveReason =>
      cases resolveReason <;> simp [destroyEndpointWord, hresolve, reject]

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

/-- Generation-checked holder-facing transitive revocation. Both the authority
and selected lineage root are bound to their installed generations. -/
noncomputable def revokeSubtreeHandles (state : State) (actor : SubjectId)
    (authority : CapabilityHandle.Handle) (kind : Capability.ObjectKind)
    (victim : SubjectId) (target : CapabilityHandle.Handle) : State × Capability.Result :=
  match CapabilityHandle.resolve state.capabilities actor authority kind with
  | .error reason => (state, .rejected (CapabilityHandle.denial reason))
  | .ok _ =>
      match CapabilityHandle.resolve state.capabilities victim target kind with
      | .error reason => (state, .rejected (CapabilityHandle.denial reason))
      | .ok _ => revokeSubtree state actor authority.slot victim target.slot

/-- Userspace composite-revocation boundary. Both words are decoded and
generation-resolved before installed and sealed descendants can be canceled. -/
noncomputable def revokeSubtreeWords (state : State) (actor : SubjectId)
    (authorityWord : UInt64) (kind : Capability.ObjectKind)
    (victim : SubjectId) (targetWord : UInt64) : State × Capability.Result :=
  match CapabilityHandle.resolveCurrent state.capabilities
      { caller := actor } authorityWord kind with
  | .error (.denied reason) => (state, .rejected (CapabilityHandle.denial reason))
  | .error (.malformed _) => (state, .rejected .staleSlot)
  | .ok authority =>
      match CapabilityHandle.resolveCurrent state.capabilities
          { caller := victim } targetWord kind with
      | .error (.denied reason) => (state, .rejected (CapabilityHandle.denial reason))
      | .error (.malformed _) => (state, .rejected .staleSlot)
      | .ok target => revokeSubtree state actor authority.handle.slot victim target.handle.slot

/-- Accepted composite revocation records both exact word resolutions before
the internal installed-plus-sealed subtree transition. -/
theorem revokeSubtreeWords_accepted_resolves state actor authorityWord kind victim targetWord
    (haccepted : (revokeSubtreeWords state actor authorityWord kind victim targetWord).2 =
      .accepted) :
    ∃ authority target,
      CapabilityHandle.resolveCurrent state.capabilities
        { caller := actor } authorityWord kind = .ok authority ∧
      CapabilityHandle.resolveCurrent state.capabilities
        { caller := victim } targetWord kind = .ok target ∧
      (revokeSubtree state actor authority.handle.slot victim target.handle.slot).2 =
        .accepted := by
  cases hauthority : CapabilityHandle.resolveCurrent state.capabilities
      { caller := actor } authorityWord kind with
  | error reason =>
      cases reason with
      | malformed decodeReason =>
          simp [revokeSubtreeWords, hauthority] at haccepted
      | denied resolveReason =>
          cases resolveReason <;> simp [revokeSubtreeWords, hauthority] at haccepted
  | ok authority =>
      cases htarget : CapabilityHandle.resolveCurrent state.capabilities
          { caller := victim } targetWord kind with
      | error reason =>
          cases reason with
          | malformed decodeReason =>
              simp [revokeSubtreeWords, hauthority, htarget] at haccepted
          | denied resolveReason =>
              cases resolveReason <;>
                simp [revokeSubtreeWords, hauthority, htarget] at haccepted
      | ok target =>
          exact ⟨authority, target, rfl, rfl,
            by simpa [revokeSubtreeWords, hauthority, htarget] using haccepted⟩

/-- A malformed or denied composite-revocation authority word preserves the
entire transfer, mailbox, derivation, and capability state. -/
theorem revokeSubtreeWords_authority_rejected_unchanged state actor authorityWord kind victim
    targetWord reason
    (hresolve : CapabilityHandle.resolveCurrent state.capabilities
      { caller := actor } authorityWord kind = .error reason) :
    (revokeSubtreeWords state actor authorityWord kind victim targetWord).1 = state := by
  cases reason with
  | malformed decodeReason => simp [revokeSubtreeWords, hresolve]
  | denied resolveReason => cases resolveReason <;> simp [revokeSubtreeWords, hresolve]

/-- Once authority resolves, a malformed or denied lineage-root word still
preserves the complete composite state. -/
theorem revokeSubtreeWords_target_rejected_unchanged state actor authorityWord kind victim
    targetWord authority reason
    (hauthority : CapabilityHandle.resolveCurrent state.capabilities
      { caller := actor } authorityWord kind = .ok authority)
    (htarget : CapabilityHandle.resolveCurrent state.capabilities
      { caller := victim } targetWord kind = .error reason) :
    (revokeSubtreeWords state actor authorityWord kind victim targetWord).1 = state := by
  cases reason with
  | malformed decodeReason => simp [revokeSubtreeWords, hauthority, htarget]
  | denied resolveReason =>
      cases resolveReason <;> simp [revokeSubtreeWords, hauthority, htarget]

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

/- Reserving a derivation changes no endpoint lifetime data.  Factoring this
out keeps the composite offer proof focused on the new mailbox/pending pair. -/
private theorem reserve_preserves_endpointWellFormed (state : EndpointIPC.State)
    (source : Capability.Capability) (rights : Capability.Rights)
    (hstate : EndpointIPC.WellFormed state)
    (hsource : ∃ subject slot, state.capabilities.slots subject slot = some source)
    (hvalid : Capability.rightsValid source.kind rights = true)
    (hsubset : Capability.rightsSubset rights source.rights = true) :
    EndpointIPC.WellFormed { state with
      capabilities := { state.capabilities with
        nextIdentity := state.capabilities.nextIdentity + 1
        derivations := fun candidate => if candidate = state.capabilities.nextIdentity then
          some (some source.identity, source.object, source.kind, rights)
          else state.capabilities.derivations candidate } } := by
  rcases hstate with ⟨hcaps, hissued, hmail, hdead, hhistory⟩
  refine ⟨reserve_preserves_capabilityWellFormed state.capabilities source rights
    hcaps hsource hvalid hsubset, hissued, hmail, hdead, hhistory⟩

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
/-- An accepted offer reserves exactly one sealed child of the trusted source
slot, and the recorded rights are an attenuated subset of that parent's rights. -/
theorem offer_accepted_records_attenuated state caller endpointSlot sourceSlot payload rights
    (h : (offer state caller endpointSlot sourceSlot payload rights).result = .accepted) :
    ∃ endpointCap source,
      Capability.lookup state.capabilities caller endpointSlot = .found endpointCap ∧
      Capability.lookup state.capabilities caller sourceSlot = .found source ∧
      (offer state caller endpointSlot sourceSlot payload rights).state.pending
          endpointCap.object = some
            ⟨state.capabilities.nextIdentity, source.identity, caller,
              source.object, source.kind, rights⟩ ∧
      (offer state caller endpointSlot sourceSlot payload rights).state.capabilities.derivations
          state.capabilities.nextIdentity =
            some (some source.identity, source.object, source.kind, rights) ∧
      Capability.rightsSubset rights source.rights = true := by
  simp only [offer] at h ⊢
  split at h <;> try contradiction
  next endpointCap hendpoint =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    next source hsource =>
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      refine ⟨endpointCap, source, hendpoint, hsource, ?_, ?_, by simp_all⟩
      · simp_all [offer, record, setPending]
      · simp_all [offer, record]

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
      split <;> try simp_all [rejectAccept, deliverData]
      split <;> try simp_all [rejectAccept]
      split <;> try simp_all [rejectAccept]
      next transfer =>
        split <;> try simp_all [rejectAccept]
        split <;> try simp_all [rejectAccept]
        split <;> try simp_all [rejectAccept]
        split <;> simp_all [rejectAccept, deliver]

set_option maxHeartbeats 800000 in
/-- Receipt preserves the authoritative capability invariant.  In the attached
case this is the proof that moving a reserved identity into the trusted
receiver's empty slot does not create a malformed or duplicate live
capability; data-only receipt and every rejection leave the store unchanged. -/
theorem accept_preserves_capabilityWellFormed state caller endpointSlot destinationSlot
    (hstate : WellFormed state) :
    Capability.WellFormed
      (accept state caller endpointSlot destinationSlot).state.capabilities := by
  simp only [accept]
  split <;> try simpa [rejectAccept] using hstate.1.1
  next endpointCap hlookup =>
    split <;> try simpa [rejectAccept] using hstate.1.1
    split <;> try simpa [rejectAccept] using hstate.1.1
    split <;> try simpa [rejectAccept] using hstate.1.1
    split <;> try simpa [rejectAccept] using hstate.1.1
    split <;> try simpa [rejectAccept] using hstate.1.1
    next envelope hmail =>
      split
      next hpending =>
        simpa [deliverData, record] using hstate.1.1
      next transfer hpending =>
        split <;> try simpa [rejectAccept] using hstate.1.1
        next hrange =>
          split <;> try simpa [rejectAccept] using hstate.1.1
          next hempty =>
            split <;> try simpa [rejectAccept] using hstate.1.1
            next hobject =>
              split <;> try simpa [rejectAccept] using hstate.1.1
              next hkind =>
                split <;> try simpa [rejectAccept] using hstate.1.1
                next hentry =>
                  split <;> try simpa [rejectAccept] using hstate.1.1
                  next hrights =>
                    have hpendingInvariant := hstate.2 endpointCap.object transfer hpending
                    have hendpointSlot := Capability.lookup_found_slot
                      state.capabilities caller endpointSlot endpointCap hlookup
                    have hcaller := hstate.1.1.1 caller endpointSlot endpointCap hendpointSlot
                    apply install_reserved_preserves_capabilityWellFormed
                    · exact hstate.1.1
                    · exact hcaller.1
                    · simpa [Capability.slotInRange] using hrange
                    · simpa using hempty
                    · simpa using hobject
                    · simpa using hkind
                    · simpa using hrights
                    · exact hpendingInvariant.2.2.2.2.2.2.2.1
                    · exact hpendingInvariant.2.2.2.2.2.2.1
                    · simpa using hentry
                    · exact hpendingInvariant.2.2.2.2.2.1
                    · exact hpendingInvariant.2.2.2.2.2.2.2.2.1

/-- Successful receipt consumes exactly its mailbox and installs its sealed
identity in the trusted caller's chosen slot. -/
theorem delivered_installs_exactly_once state caller endpointSlot destinationSlot envelope
    (hattached : ∀ endpoint, state.mailbox endpoint = some envelope →
      state.pending endpoint ≠ none)
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
      split at h
      next transfer hpending =>
        cases h
        exact False.elim (hattached endpointCap.object hmail hpending)
      next transfer hpending =>
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        cases h
        refine ⟨endpointCap.object, transfer, hpending, hmail, ?_, ?_, ?_⟩ <;>
          simp (maxSteps := 500000) [deliver, record, setPending,
            EndpointIPC.setOption, Capability.install, *]

/-- Delivery returns the exact envelope stored before the transition. In
particular, neither payload word participates in selecting installed authority. -/
theorem delivered_envelope_and_payload_independent state caller endpointSlot destinationSlot envelope
    (hattached : ∀ endpoint, state.mailbox endpoint = some envelope →
      state.pending endpoint ≠ none)
    (h : (accept state caller endpointSlot destinationSlot).result = .delivered envelope) :
    ∃ endpoint transfer,
      state.mailbox endpoint = some envelope ∧
      state.pending endpoint = some transfer ∧
      (accept state caller endpointSlot destinationSlot).state.capabilities.slots
        caller destinationSlot = some
          ⟨transfer.object, transfer.kind, transfer.rights,
            transfer.identity, some transfer.parent⟩ := by
  obtain ⟨endpoint, transfer, hpending, hmail, _, _, hslot⟩ :=
    delivered_installs_exactly_once state caller endpointSlot destinationSlot envelope hattached h
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
    (hattached : ∀ endpoint, state.mailbox endpoint = some envelope →
      state.pending endpoint ≠ none)
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
    delivered_envelope_and_payload_independent state caller endpointSlot destinationSlot envelope
      hattached h
  obtain ⟨parentParent, parentRights, hparent, hsubset⟩ :=
    pending_rights_conserved state endpoint transfer hstate hpending
  exact ⟨endpoint, transfer, parentParent, parentRights, hmail, hparent, hsubset, hslot⟩

set_option maxHeartbeats 800000 in
/-- Changing only the inert payload cannot change the reserved derivation or
sealed authority.  The envelopes and observer events may differ because the
payload itself is intentionally visible. -/
theorem offer_authority_payload_independent state caller endpointSlot sourceSlot
    leftPayload rightPayload rights :
    (offer state caller endpointSlot sourceSlot leftPayload rights).state.capabilities =
        (offer state caller endpointSlot sourceSlot rightPayload rights).state.capabilities ∧
      (offer state caller endpointSlot sourceSlot leftPayload rights).state.pending =
        (offer state caller endpointSlot sourceSlot rightPayload rights).state.pending := by
  simp only [offer]
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
      split <;> simp_all [reject, record]

-- Endpoint destruction cancels the attachment occupying that endpoint even
-- when the attachment names a different-kind object.
private def destroyTraceSubjects : SubjectId → Bool := fun subject => subject = 0
private def destroyTraceMemory : Capability.Capability :=
  { object := 7, kind := .memory, rights := Capability.allRights, identity := 0 }
private def destroyTraceCaps : Capability.State :=
  { subjects := destroyTraceSubjects
    objects := fun object => object = 7
    kinds := fun object => if object = 7 then some .memory else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 2 then some destroyTraceMemory else none }
private def destroyTraceInitialEndpoint : EndpointIPC.State :=
  { capabilities := destroyTraceCaps
    allocator := { frames := [], status := fun _ => .reserved }
    binding := fun _ => none
    issued := fun _ => false
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    sendHistory := fun _ => [] }
private def destroyTraceRoot := (EndpointIPC.create destroyTraceInitialEndpoint 10 0 0).state
private def destroyTraceEnvelope : EndpointIPC.Envelope :=
  { endpoint := 10, sender := 0, payload := { word0 := 4, word1 := 71 } }
private def destroyTraceTransfer : Sealed :=
  { identity := 42, parent := 0, sender := 0, object := 7, kind := .memory,
    rights := { read := true } }
private def destroyTraceEndpointTransfer : Sealed :=
  { identity := 43, parent := 1, sender := 0, object := 10, kind := .endpoint,
    rights := { send := true } }
private def destroyTraceState : State :=
  { toEndpointState := { destroyTraceRoot with
      mailbox := EndpointIPC.setOption
        (EndpointIPC.setOption destroyTraceRoot.mailbox 10 (some destroyTraceEnvelope))
        11 (some { destroyTraceEnvelope with endpoint := 11 }) }
    pending := setPending
      (setPending (fun _ => none) 10 (some destroyTraceTransfer))
      11 (some destroyTraceEndpointTransfer)
    trace := ⟨fun _ => []⟩ }

private def replacementSource : Capability.Capability :=
  { object := 8, kind := .memory, rights := Capability.allRights, identity := 44 }

private def replacementEndpoint : Capability.Capability :=
  { object := 10, kind := .endpoint, rights := EndpointIPC.endpointRootRights,
    identity := 45 }

private def destroyTraceEndpointCap : Capability.Capability :=
  { object := 10, kind := .endpoint, rights := EndpointIPC.endpointRootRights,
    identity := 1 }

private def replacementState : State :=
  { destroyTraceState with
    capabilities := Capability.install
      (Capability.clear destroyTraceState.capabilities 0 2) 0 2 replacementSource }

private def replacementEndpointState : State :=
  { destroyTraceState with
    capabilities := Capability.install
      (Capability.clear destroyTraceState.capabilities 0 0) 0 0 replacementEndpoint }

private def usableReplacementCaps : Capability.State :=
  { (Capability.install destroyTraceRoot.capabilities 0 2 replacementSource) with
    objects := fun object => if object = 8 then true else
      destroyTraceRoot.capabilities.objects object
    kinds := fun object =>
      if object = 8 then some .memory else destroyTraceRoot.capabilities.kinds object }

private def usableReplacementState : State :=
  { toEndpointState := { destroyTraceRoot with capabilities := usableReplacementCaps }
    pending := fun _ => none
    trace := ⟨fun _ => []⟩ }

private def exhaustedReplacementState : State :=
  { usableReplacementState with
    capabilities := { usableReplacementState.capabilities with
      nextIdentity := CapabilityHandle.generationReserved } }

private def dataOnlyState : State :=
  { toEndpointState := destroyTraceRoot
    pending := fun _ => none
    trace := ⟨fun _ => []⟩ }

/-- Executable regression: an accepted plain send keeps the endpoint explicitly
untagged, and receipt follows the data-only path without installing authority in
the nominated destination slot. -/
example :
    let payload : EndpointIPC.Payload := { word0 := 71, word1 := 98 }
    let sent := sendData dataOnlyState 0 0 payload
    sent.result = .accepted ∧
      sent.state.pending 10 = none ∧
      (accept sent.state 0 0 1).result =
        .delivered { endpoint := 10, sender := 0, payload := payload } ∧
      (accept sent.state 0 0 1).state.pending 10 = none ∧
      (accept sent.state 0 0 1).state.capabilities.slots 0 1 = none := by
  native_decide

/-- A data-only receipt does not consume or validate the unused destination
slot; only an attached authority needs an encodable output handle. -/
example :
    let endpointWord := UInt64.ofNat 65536
    let payload : EndpointIPC.Payload := { word0 := 71, word1 := 98 }
    let sent := sendData dataOnlyState 0 0 payload
    (acceptWord sent.state 0 endpointWord CapabilityHandle.slotReserved).result =
      .delivered { endpoint := 10, sender := 0, payload := payload } := by
  native_decide

/-- Receipt rejects the reserved destination slot before consuming a valid
sealed envelope. -/
example :
    let endpointWord := UInt64.ofNat 65536
    let sourceWord := UInt64.ofNat 2883586
    let offered := offerWords usableReplacementState 0 endpointWord sourceWord .memory
      { word0 := 71, word1 := 98 } { read := true }
    let received := acceptWord offered.state 0 endpointWord CapabilityHandle.slotReserved
    offered.result = .accepted ∧
      received.result = .rejected .outOfRange ∧
      received.state.pending 10 = offered.state.pending 10 ∧
      received.state.mailbox 10 = offered.state.mailbox 10 := by
  native_decide

/-- Even an invalid sealed identity introduced through the internal raw offer
cannot cross the userspace receipt boundary. -/
example :
    let endpointWord := UInt64.ofNat 65536
    let offered := offer exhaustedReplacementState 0 0 2
      { word0 := 71, word1 := 98 } { read := true }
    let received := acceptWord offered.state 0 endpointWord 1
    offered.result = .accepted ∧
      received.result = .rejected .generationExhausted ∧
      received.state.pending 10 = offered.state.pending 10 ∧
      received.state.mailbox 10 = offered.state.mailbox 10 := by
  native_decide

/-- Generation exhaustion fails closed before an offered descendant can enter
the sealed-transfer state. -/
example :
    let endpointWord := UInt64.ofNat 65536
    let sourceWord := UInt64.ofNat 2883586
    let outcome := offerWords exhaustedReplacementState 0 endpointWord sourceWord .memory
      { word0 := 71, word1 := 98 } { read := true }
    outcome.result = .rejected .generationExhausted ∧
      outcome.state.capabilities.nextIdentity = CapabilityHandle.generationReserved ∧
      outcome.state.pending 10 = exhaustedReplacementState.pending 10 ∧
      outcome.state.mailbox 10 = exhaustedReplacementState.mailbox 10 := by
  native_decide

/-- The public transfer boundary accepts only the canonical words for the
current endpoint and source generations. -/
example :
    let endpointWord := UInt64.ofNat 65536
    let sourceWord := UInt64.ofNat 2883586
    CapabilityHandle.encode (CapabilityHandle.issue 0 destroyTraceEndpointCap) =
        some endpointWord ∧
      CapabilityHandle.encode (CapabilityHandle.issue 2 replacementSource) =
        some sourceWord ∧
      (offerWords usableReplacementState 0 endpointWord sourceWord .memory
        { word0 := 71, word1 := 98 } { read := true }).result = .accepted := by
  native_decide

/-- Replaying the old endpoint word after same-slot replacement is rejected
without changing transfer, mailbox, or capability state. -/
example :
    let oldEndpointWord := UInt64.ofNat 65536
    let outcome := destroyEndpointWord replacementEndpointState 0 oldEndpointWord
    outcome.result = .rejected .staleHandle ∧
      outcome.state.pending 10 = replacementEndpointState.pending 10 ∧
      outcome.state.mailbox 10 = replacementEndpointState.mailbox 10 ∧
      outcome.state.capabilities.slots 0 0 =
        replacementEndpointState.capabilities.slots 0 0 := by
  native_decide

/-- A noncanonical all-reserved word cannot reach endpoint destruction. -/
example :
    let outcome := destroyEndpointWord destroyTraceState 0 (UInt64.ofNat (2 ^ 64 - 1))
    outcome.result = .rejected .staleHandle ∧
      outcome.state.pending 10 = destroyTraceState.pending 10 ∧
      outcome.state.mailbox 10 = destroyTraceState.mailbox 10 ∧
      outcome.state.capabilities.slots 0 0 = destroyTraceState.capabilities.slots 0 0 := by
  native_decide

/-- A concrete clear-plus-same-slot replacement cannot redirect an offer made
with the old source generation, even though raw slot lookup sees the replacement. -/
example :
    let endpointHandle := CapabilityHandle.issue 0 destroyTraceEndpointCap
    let oldSource := CapabilityHandle.issue 2 destroyTraceMemory
    Capability.lookup replacementState.capabilities 0 2 = .found replacementSource ∧
      (offerHandles replacementState 0 endpointHandle oldSource .memory
        { word0 := 8, word1 := 44 } { read := true }).result = .rejected .staleSource := by
  native_decide

/-- The same endpoint replacement attack is denied by every holder-facing
endpoint authority consumer: the raw numbered slot sees the replacement, but
the old generation cannot offer, send, receive, or destroy through it. -/
example :
    let oldEndpoint := CapabilityHandle.issue 0 destroyTraceEndpointCap
    let source := CapabilityHandle.issue 2 destroyTraceMemory
    Capability.lookup replacementEndpointState.capabilities 0 0 =
        .found replacementEndpoint ∧
      (offerHandles replacementEndpointState 0 oldEndpoint source .memory
        { word0 := 71, word1 := 98 } { read := true }).result =
          .rejected .staleEndpoint ∧
      (sendDataHandle replacementEndpointState 0 oldEndpoint
        { word0 := 71, word1 := 98 }).result = .rejected .staleHandle ∧
      (acceptHandle replacementEndpointState 0 oldEndpoint 1).result =
        .rejected .staleEndpoint ∧
      (destroyEndpointHandle replacementEndpointState 0 oldEndpoint).result =
        .rejected .staleHandle := by
  native_decide

example :
    let oldMemory := CapabilityHandle.issue 2 destroyTraceMemory
    Capability.lookup replacementState.capabilities 0 2 = .found replacementSource ∧
      (retireObjectHandle replacementState 0 oldMemory).result = .rejected .staleSlot := by
  native_decide

/-- Transitive revocation also rejects an old authority generation before its
raw slot can select the replacement capability. -/
example :
    let oldMemory := CapabilityHandle.issue 2 destroyTraceMemory
    (revokeSubtreeHandles replacementState 0 oldMemory .memory 0 oldMemory).2 =
      .rejected .staleSlot := by
  rfl

/-- Composite revocation accepts only the canonical current authority and
lineage-root words, and stale replay preserves the installed replacement. -/
example :
    let replacementWord : UInt64 := 44 * 65536 + 2
    (revokeSubtreeWords usableReplacementState 0 replacementWord .memory 0
      replacementWord).2 = .accepted ∧
      (revokeSubtreeWords usableReplacementState 0 replacementWord .memory 0
        replacementWord).1.capabilities.slots 0 2 = none := by
  dsimp [revokeSubtreeWords]
  constructor <;> rfl
example :
    let staleWord : UInt64 := 43 * 65536 + 2
    (revokeSubtreeWords usableReplacementState 0 staleWord .memory 0 staleWord).2 =
        .rejected .staleSlot ∧
      (revokeSubtreeWords usableReplacementState 0 staleWord .memory 0 staleWord).1.capabilities.slots
          0 2 = usableReplacementState.capabilities.slots 0 2 := by
  dsimp [revokeSubtreeWords]
  constructor <;> rfl

example : let outcome := destroyEndpoint destroyTraceState 0 0
    outcome.result = .accepted ∧
      outcome.state.mailbox 10 = none ∧
      outcome.state.pending 10 = none ∧
      outcome.state.trace.events 10 = [.canceled 10 42] ∧
      outcome.state.mailbox 11 = none ∧
      outcome.state.pending 11 = none ∧
      outcome.state.trace.events 11 = [.canceled 11 43] := by
  native_decide

end LeanOS.CapabilityTransfer
