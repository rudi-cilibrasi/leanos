import LeanOS.CompositeUnwinding

/-!
# Composite unwinding: the observer's remaining own operations

`LeanOS.CompositeUnwinding` proves step and output consistency for the
observer's memory, data-IPC, direct-revocation and frame-rule operations.
This module extends both conditions to the observer's capability-identity
operations, sealed transfers, subject creation, and scheduler operations.

**The identity counter is a declared public input.**  `Capability.copy` and
`CapabilityTransfer.offer` draw the identity (the handle generation) of every
new capability from the single global `nextIdentity`.
`CompositeUnwinding.Channels.identity_counter_step_inconsistent` proves that
two states low-equivalent for the observer but with different counters give
distinguishable rows after the observer's own delegation.  The channel cannot
be closed in the view (the observer must present the exact generation in every
later handle word), and closing it in the model (for example by per-subject
identity namespaces) would change the handle generations that the generated
dispatcher (`LeanOS.CompositeDispatcher`) and its replay fix.  So, like the
scheduler choice and the
fail-stop mode, the counter is treated as a public input: `OwnStepCounter`
adds agreement on it to `OwnStep`.  It is a declared channel, not a claimed
absence: the observer learns how many identities the whole system has issued.

**Step consistency** (`own_step_consistent_counter`): under `OwnStepCounter`,
in addition to `CompositeUnwinding.ownStepConsistent`, the observer's
delegation into its own row, its transfer offers, creation of any subject
(including itself), and every scheduler operation except `terminateCurrent`.
`own_step_accept` covers transfer receipt given agreement on the objects that
sealed transfers pending on the observer's endpoints carry
(`CarriedAgree`): receipt makes the carried object part of the observer's
authority, an information flow authorized by the sender's offer.

**Output consistency** (`own_output_consistent_counter`): in addition to
`CompositeUnwinding.ownOutputConsistent`, transfer offer and receipt, subtree
revocation of the observer's own slot (rights attenuate along derivations, so
its runtime-safety check reads only the revoked capability), creation and
termination of the observer itself, `scheduleNext`, and `terminateCurrent`;
`own_output_consistent_scheduler` adds `scheduleYield`, `scheduleTick`, and
`scheduleRemove` when the two states also agree on the ready queue and its
capacity (`SchedulerPublic`, the scheduler's choice as a public input).

**Composition** (`own_run_noninterference_counter`): the operations in both
families compose into classical noninterference for runs of the observer's own
operations, now including its own delegations, offers, and `scheduleNext`.
-/
namespace LeanOS.CompositeOwnSteps

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId

/-- `OwnStep` together with agreement on the declared public capability-identity
counter. -/
structure OwnStepCounter (observer : SubjectId) (left right : CompositeState) : Prop
    extends OwnStep observer left right where
  counter : left.capabilities.nextIdentity = right.capabilities.nextIdentity

/-! ## Delegation into the observer's own row -/

theorem copy_accepted_state (a : Capability.State) (actor source destination destinationSlot)
    (rights : Capability.Rights)
    (haccepted : (Capability.copy a actor source destination destinationSlot rights).result =
      .accepted) :
    ∃ cap, Capability.lookup a actor source = .found cap ∧
      (Capability.copy a actor source destination destinationSlot rights).state =
        Capability.install
          { a with
            nextIdentity := a.nextIdentity + 1
            derivations := fun identity =>
              if identity = a.nextIdentity then
                some (some cap.identity, cap.object, cap.kind, rights)
              else a.derivations identity }
          destination destinationSlot
          { identity := a.nextIdentity, parent := some cap.identity,
            object := cap.object, kind := cap.kind, rights := rights } := by
  unfold Capability.copy at haccepted ⊢
  split at haccepted
  · simp [Capability.reject] at haccepted
  · simp [Capability.reject] at haccepted
  · rename_i cap hfound
    refine ⟨cap, hfound, ?_⟩
    repeat' split at haccepted
    all_goals simp_all [Capability.reject]

theorem copy_frame_self (a : Capability.State) actor source destination destinationSlot
    (rights : Capability.Rights) :
    let next := (Capability.copy a actor source destination destinationSlot rights).state
    next.subjects = a.subjects ∧ next.slotCapacity = a.slotCapacity ∧
      next.objects = a.objects ∧ next.kinds = a.kinds := by
  simp only [Capability.copy]
  repeat' split
  all_goals simp [Capability.reject, Capability.install]

theorem copy_nextIdentity (a : Capability.State) actor source destination destinationSlot
    (rights : Capability.Rights) :
    (Capability.copy a actor source destination destinationSlot rights).state.nextIdentity =
      match (Capability.copy a actor source destination destinationSlot rights).result with
      | .accepted => a.nextIdentity + 1
      | .rejected _ => a.nextIdentity := by
  simp only [Capability.copy]
  repeat' split
  all_goals simp_all [Capability.reject, Capability.install]

/-- The observer's delegation into its own row is step consistent once the
two states agree on the public identity counter. -/
theorem own_step_copy_self {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (source destinationSlot : Nat)
    (rights : Capability.Rights) :
    LowEquiv observer
      (applyOperation left (.capabilityCopy source observer destinationSlot rights))
      (applyOperation right (.capabilityCopy source observer destinationSlot rights)) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  have hresult := copy_self_congr left.capabilities right.capabilities observer source
    destinationSlot rights h.lookup h.low.live h.low.capacity
    (fun slot hslot => (h.low.slot slot (h.low.capacity ▸ hslot)).1)
  simp only [applyOperation, hLs, hRs]
  rw [hresult]
  cases hres : (Capability.copy right.capabilities observer source observer destinationSlot
      rights).result with
  | rejected reason => exact h.low
  | accepted =>
      simp only
      obtain ⟨capL, hfoundL, hstateL⟩ := copy_accepted_state _ _ _ _ _ _ (hresult.trans hres)
      obtain ⟨capR, hfoundR, hstateR⟩ := copy_accepted_state _ _ _ _ _ _ hres
      have hcap : capL = capR := by
        rw [h.lookup source, hfoundR] at hfoundL
        cases hfoundL
        rfl
      subst hcap
      obtain ⟨hLsub, hLcap, hLobj, hLkind⟩ := copy_frame_self left.capabilities observer source
        observer destinationSlot rights
      obtain ⟨hRsub, hRcap, hRobj, hRkind⟩ := copy_frame_self right.capabilities observer source
        observer destinationSlot rights
      have hnames : Names left observer capL.object = true :=
        names_of_lookup left observer source capL hfoundL
      have hcapacity := h.low.capacity
      apply lowEquiv_installCopiedCapabilities h.low _ _ hLobj hLkind hRobj hRkind
      · rw [hLsub, hRsub]
        exact h.low.live
      · rw [hLcap, hRcap]
        exact hcapacity
      · rw [hstateL, hstateR]
        simp only [Capability.capabilitySpace, Capability.install, h.counter, hcapacity]
        apply List.map_congr_left
        intro candidate hmem
        rw [List.mem_range] at hmem
        by_cases hslot : candidate = destinationSlot
        · simp [hslot]
        · simp only [hslot, and_false, ↓reduceIte]
          exact (h.low.slot candidate (hcapacity ▸ hmem)).1
      · intro cap hmem
        rw [hstateL] at hmem
        simp only [Capability.capabilitySpace, Capability.install, List.mem_map,
          List.mem_range] at hmem
        obtain ⟨candidate, hrange, hslot⟩ := hmem
        by_cases hdest : candidate = destinationSlot
        · simp only [hdest, and_self, ↓reduceIte, Option.some.injEq] at hslot
          rw [← hslot]
          exact hnames
        · simp only [hdest, and_false, ↓reduceIte] at hslot
          have hrow : some cap ∈ row left observer := by
            rw [List.mem_iff_getElem?]
            refine ⟨candidate, ?_⟩
            rw [row_getElem? left observer candidate (hLcap ▸ hrange), hslot]
          simp only [Names, List.any_eq_true]
          exact ⟨some cap, hrow, by simp⟩

/-! ## Publishing a transfer state -/

theorem observe_installTransfers_eq (observer : SubjectId) (state : CompositeState)
    (transfers : CapabilityTransfer.State) :
    observe observer (installTransfers state transfers) =
      { observe observer state with
        live := transfers.capabilities.subjects observer
        capacity := transfers.capabilities.slotCapacity observer
        row := Capability.capabilitySpace transfers.capabilities observer
        named := (Capability.capabilitySpace transfers.capabilities observer).map
          (Option.map fun cap =>
            { CompositeObservation.objectView state cap.object with
              live := transfers.capabilities.objects cap.object
              kind := transfers.capabilities.kinds cap.object
              mailbox := transfers.mailbox cap.object
              sealed := transfers.pending cap.object }) } :=
  rfl

/-- Two low-equivalent states that publish transfer states agreeing on the
observer's row and on every object it names afterwards stay low-equivalent.
An object named only afterwards must have the same view on both sides. -/
theorem lowEquiv_installTransfers {observer : SubjectId} {left right : CompositeState}
    (hlow : LowEquiv observer left right) (leftTransfers rightTransfers : CapabilityTransfer.State)
    (hlive : leftTransfers.capabilities.subjects observer =
      rightTransfers.capabilities.subjects observer)
    (hcapacity : leftTransfers.capabilities.slotCapacity observer =
      rightTransfers.capabilities.slotCapacity observer)
    (hrow : Capability.capabilitySpace leftTransfers.capabilities observer =
      Capability.capabilitySpace rightTransfers.capabilities observer)
    (hnamed : ∀ cap, some cap ∈ Capability.capabilitySpace leftTransfers.capabilities observer →
      CompositeObservation.objectView left cap.object =
          CompositeObservation.objectView right cap.object ∧
        leftTransfers.capabilities.objects cap.object =
          rightTransfers.capabilities.objects cap.object ∧
        leftTransfers.capabilities.kinds cap.object =
          rightTransfers.capabilities.kinds cap.object ∧
        leftTransfers.mailbox cap.object = rightTransfers.mailbox cap.object ∧
        leftTransfers.pending cap.object = rightTransfers.pending cap.object) :
    LowEquiv observer (installTransfers left leftTransfers)
      (installTransfers right rightTransfers) := by
  unfold LowEquiv
  rw [observe_installTransfers_eq, observe_installTransfers_eq]
  have hnamedList :
      (Capability.capabilitySpace leftTransfers.capabilities observer).map
          (Option.map fun cap =>
            { CompositeObservation.objectView left cap.object with
              live := leftTransfers.capabilities.objects cap.object
              kind := leftTransfers.capabilities.kinds cap.object
              mailbox := leftTransfers.mailbox cap.object
              sealed := leftTransfers.pending cap.object }) =
        (Capability.capabilitySpace rightTransfers.capabilities observer).map
          (Option.map fun cap =>
            { CompositeObservation.objectView right cap.object with
              live := rightTransfers.capabilities.objects cap.object
              kind := rightTransfers.capabilities.kinds cap.object
              mailbox := rightTransfers.mailbox cap.object
              sealed := rightTransfers.pending cap.object }) := by
    rw [← hrow]
    apply List.map_congr_left
    intro slot hmem
    cases slot with
    | none => rfl
    | some cap =>
        obtain ⟨hview, hobjects, hkinds, hmailbox, hpending⟩ := hnamed cap hmem
        simp only [Option.map_some, hview, hobjects, hkinds, hmailbox, hpending]
  rw [hnamedList, hlive, hcapacity, hrow, hlow]

/-- The transfer store published by the composite is the published capability
and endpoint state. -/
theorem transfers_published {state : CompositeState} (hcoherent : state.Coherent) :
    state.transfers.capabilities = state.capabilities ∧
      state.transfers.mailbox = state.ipc.endpoints.mailbox := by
  refine ⟨(ipcCapabilitiesPublished_of_coherent hcoherent).2, ?_⟩
  rw [show state.transfers.mailbox = state.transfers.toEndpointState.mailbox from rfl,
    hcoherent.2.2.2.2.2.2.2.2.2.1]

/-- Low-equivalent coherent states agree on the transfer view of every object
the observer names. -/
theorem ownStep_transferObject {observer left right} (h : OwnStep observer left right)
    (object : ObjectId) (hnames : Names left observer object = true) :
    left.transfers.capabilities.objects object = right.transfers.capabilities.objects object ∧
      left.transfers.capabilities.kinds object = right.transfers.capabilities.kinds object ∧
      left.transfers.mailbox object = right.transfers.mailbox object ∧
      left.transfers.pending object = right.transfers.pending object := by
  obtain ⟨hLcaps, hLmail⟩ := transfers_published h.leftWF.1
  obtain ⟨hRcaps, hRmail⟩ := transfers_published h.rightWF.1
  have hview := h.low.namedView object hnames
  rw [hLcaps, hRcaps, hLmail, hRmail]
  exact ⟨congrArg ObjectView.live hview, congrArg ObjectView.kind hview,
    congrArg ObjectView.mailbox hview, congrArg ObjectView.sealed hview⟩

theorem ownStep_transferLookup {observer left right} (h : OwnStep observer left right)
    (slot : Nat) :
    Capability.lookup left.transfers.capabilities observer slot =
      Capability.lookup right.transfers.capabilities observer slot := by
  rw [(transfers_published h.leftWF.1).1, (transfers_published h.rightWF.1).1]
  exact h.lookup slot

theorem ownStep_transferResolve {observer left right} (h : OwnStep observer left right)
    (word : UInt64) (kind : Capability.ObjectKind) :
    CapabilityHandle.resolveCurrent left.transfers.capabilities { caller := observer } word kind =
      CapabilityHandle.resolveCurrent right.transfers.capabilities { caller := observer } word
        kind := by
  rw [(transfers_published h.leftWF.1).1, (transfers_published h.rightWF.1).1]
  exact h.low.resolveCurrent word kind

theorem ownStep_transferLookupObject {observer left right} (h : OwnStep observer left right)
    (slot : Nat) (cap : Capability.Capability)
    (hfound : Capability.lookup right.transfers.capabilities observer slot = .found cap) :
    left.transfers.capabilities.objects cap.object =
        right.transfers.capabilities.objects cap.object ∧
      left.transfers.capabilities.kinds cap.object =
        right.transfers.capabilities.kinds cap.object ∧
      left.transfers.mailbox cap.object = right.transfers.mailbox cap.object := by
  rw [← (ownStep_transferLookup h) slot, (transfers_published h.leftWF.1).1] at hfound
  have hnames := names_of_lookup left observer slot cap hfound
  obtain ⟨hobjects, hkinds, hmailbox, _⟩ := (ownStep_transferObject h) cap.object hnames
  exact ⟨hobjects, hkinds, hmailbox⟩

theorem OwnStepCounter.transferCounter {observer left right}
    (h : OwnStepCounter observer left right) :
    left.transfers.capabilities.nextIdentity = right.transfers.capabilities.nextIdentity := by
  rw [(transfers_published h.leftWF.1).1, (transfers_published h.rightWF.1).1]
  exact h.counter

/-- A transfer state with the same subjects, slots, objects and kinds as the
published capabilities leaves the observer's row and the named objects'
registry fields unchanged. -/
theorem transfer_row_named {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (leftNext rightNext : CapabilityTransfer.State)
    (hleft : leftNext.capabilities.subjects = left.transfers.capabilities.subjects ∧
      leftNext.capabilities.slotCapacity = left.transfers.capabilities.slotCapacity ∧
      leftNext.capabilities.slots = left.transfers.capabilities.slots ∧
      leftNext.capabilities.objects = left.transfers.capabilities.objects ∧
      leftNext.capabilities.kinds = left.transfers.capabilities.kinds)
    (hright : rightNext.capabilities.subjects = right.transfers.capabilities.subjects ∧
      rightNext.capabilities.slotCapacity = right.transfers.capabilities.slotCapacity ∧
      rightNext.capabilities.slots = right.transfers.capabilities.slots ∧
      rightNext.capabilities.objects = right.transfers.capabilities.objects ∧
      rightNext.capabilities.kinds = right.transfers.capabilities.kinds)
    (hobject : ∀ object, Names left observer object = true →
      leftNext.mailbox object = rightNext.mailbox object ∧
        leftNext.pending object = rightNext.pending object) :
    LowEquiv observer (installTransfers left leftNext) (installTransfers right rightNext) := by
  obtain ⟨hLcaps, _⟩ := transfers_published h.leftWF.1
  obtain ⟨hRcaps, _⟩ := transfers_published h.rightWF.1
  obtain ⟨hLsub, hLcap, hLslots, hLobj, hLkind⟩ := hleft
  obtain ⟨hRsub, hRcap, hRslots, hRobj, hRkind⟩ := hright
  rw [hLcaps] at hLsub hLcap hLslots hLobj hLkind
  rw [hRcaps] at hRsub hRcap hRslots hRobj hRkind
  have hspaceL : Capability.capabilitySpace leftNext.capabilities observer = row left observer := by
    simp only [Capability.capabilitySpace, row, hLcap, hLslots]
  have hspaceR : Capability.capabilitySpace rightNext.capabilities observer =
      row right observer := by
    simp only [Capability.capabilitySpace, row, hRcap, hRslots]
  apply lowEquiv_installTransfers h.low
  · rw [hLsub, hRsub]
    exact h.low.live
  · rw [hLcap, hRcap]
    exact h.low.capacity
  · rw [hspaceL, hspaceR]
    exact h.low.rowEq
  · intro cap hmem
    rw [hspaceL] at hmem
    have hnames : Names left observer cap.object = true := by
      simp only [Names, List.any_eq_true]
      exact ⟨some cap, hmem, by simp⟩
    obtain ⟨hobjects, hkinds, _, _⟩ := (ownStep_transferObject h) cap.object hnames
    rw [(transfers_published h.leftWF.1).1, (transfers_published h.rightWF.1).1]
      at hobjects hkinds
    obtain ⟨hmailbox, hpending⟩ := hobject cap.object hnames
    refine ⟨h.low.namedView cap.object hnames, ?_, ?_, hmailbox, hpending⟩
    · rw [hLobj, hRobj]
      exact hobjects
    · rw [hLkind, hRkind]
      exact hkinds

/-! ## Transfer offers

`CapabilityTransfer.offer` is restated as a small validation (`offerCheck`)
followed by one accepted update (`offerAccepted`).  Congruence is proved on
the validation, so no proof case-splits the large accepted record. -/

/-- The validation performed by `CapabilityTransfer.offer`. -/
def offerCheck (state : CapabilityTransfer.State) (caller : SubjectId)
    (endpointSlot sourceSlot : Nat) (rights : Capability.Rights) :
    Except CapabilityTransfer.OfferError (Capability.Capability × Capability.Capability) :=
  match Capability.lookup state.capabilities caller endpointSlot with
  | .invalidSubject => .error .invalidSubject
  | .staleSlot => .error .staleEndpoint
  | .found endpointCap =>
    if endpointCap.kind != .endpoint then .error .wrongEndpointKind
    else if !endpointCap.rights.send then .error .missingSend
    else if state.capabilities.objects endpointCap.object != true then .error .retiredEndpoint
    else if state.capabilities.kinds endpointCap.object != some .endpoint then
      .error .retiredEndpoint
    else if (state.mailbox endpointCap.object).isSome then .error .full
    else match Capability.lookup state.capabilities caller sourceSlot with
      | .invalidSubject => .error .invalidSubject
      | .staleSlot => .error .staleSource
      | .found source =>
        if !source.rights.grant then .error .missingGrant
        else if !Capability.rightsValid source.kind rights then .error .emptyRights
        else if !Capability.rightsSubset rights source.rights then .error .rightsNotSubset
        else .ok (endpointCap, source)

/-- The accepted update performed by `CapabilityTransfer.offer`. -/
def offerAccepted (state : CapabilityTransfer.State) (caller : SubjectId)
    (endpointCap source : Capability.Capability) (payload : EndpointIPC.Payload)
    (rights : Capability.Rights) : CapabilityTransfer.State :=
  let identity := state.capabilities.nextIdentity
  let sealed : CapabilityTransfer.Sealed :=
    ⟨identity, source.identity, caller, source.object, source.kind, rights⟩
  let envelope : EndpointIPC.Envelope :=
    { endpoint := endpointCap.object, sender := caller, payload }
  CapabilityTransfer.record { state with
      capabilities := { state.capabilities with
        nextIdentity := identity + 1
        derivations := fun candidate => if candidate = identity then
          some (some source.identity, source.object, source.kind, rights)
          else state.capabilities.derivations candidate }
      mailbox := EndpointIPC.setOption state.mailbox endpointCap.object (some envelope)
      sendHistory := EndpointIPC.appendHistory state.sendHistory endpointCap.object envelope
      pending := CapabilityTransfer.setPending state.pending endpointCap.object (some sealed) }
    endpointCap.object (.offered endpointCap.object identity caller payload)

theorem offer_eq (state : CapabilityTransfer.State) caller endpointSlot sourceSlot payload
    (rights : Capability.Rights) :
    CapabilityTransfer.offer state caller endpointSlot sourceSlot payload rights =
      match offerCheck state caller endpointSlot sourceSlot rights with
      | .error reason => CapabilityTransfer.reject state reason
      | .ok (endpointCap, source) =>
          { state := offerAccepted state caller endpointCap source payload rights
            result := .accepted } := by
  unfold CapabilityTransfer.offer offerCheck
  cases Capability.lookup state.capabilities caller endpointSlot with
  | invalidSubject => rfl
  | staleSlot => rfl
  | found endpointCap =>
    simp only
    by_cases c1 : (endpointCap.kind != .endpoint) = true
    · simp only [c1, ↓reduceIte, Bool.false_eq_true]
    simp only [c1, ↓reduceIte, Bool.false_eq_true]
    by_cases c2 : (!endpointCap.rights.send) = true
    · simp only [c2, ↓reduceIte, Bool.false_eq_true]
    simp only [c2, ↓reduceIte, Bool.false_eq_true]
    by_cases c3 : (state.capabilities.objects endpointCap.object != true) = true
    · simp only [c3, ↓reduceIte, Bool.false_eq_true]
    simp only [c3, ↓reduceIte, Bool.false_eq_true]
    by_cases c4 : (state.capabilities.kinds endpointCap.object != some .endpoint) = true
    · simp only [c4, ↓reduceIte, Bool.false_eq_true]
    simp only [c4, ↓reduceIte, Bool.false_eq_true]
    by_cases c5 : (state.mailbox endpointCap.object).isSome = true
    · simp only [c5, ↓reduceIte, Bool.false_eq_true]
    simp only [c5, ↓reduceIte, Bool.false_eq_true]
    cases Capability.lookup state.capabilities caller sourceSlot with
    | invalidSubject => rfl
    | staleSlot => rfl
    | found source =>
      simp only
      by_cases c6 : (!source.rights.grant) = true
      · simp only [c6, ↓reduceIte, Bool.false_eq_true]
      simp only [c6, ↓reduceIte, Bool.false_eq_true]
      by_cases c7 : (!Capability.rightsValid source.kind rights) = true
      · simp only [c7, ↓reduceIte, Bool.false_eq_true]
      simp only [c7, ↓reduceIte, Bool.false_eq_true]
      by_cases c8 : (!Capability.rightsSubset rights source.rights) = true
      · simp only [c8, ↓reduceIte, Bool.false_eq_true]
      simp only [c8, ↓reduceIte, Bool.false_eq_true]
      rfl

/-- The validation performed by `CapabilityTransfer.offerWords`. -/
def offerWordsCheck (state : CapabilityTransfer.State) (caller : SubjectId)
    (endpointWord sourceWord : UInt64) (sourceKind : Capability.ObjectKind)
    (rights : Capability.Rights) :
    Except CapabilityTransfer.OfferError (Capability.Capability × Capability.Capability) :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord .endpoint with
  | .error (.denied .invalidSubject) => .error .invalidSubject
  | .error (.denied .kindMismatch) => .error .wrongEndpointKind
  | .error _ => .error .staleEndpoint
  | .ok endpoint =>
      match CapabilityHandle.resolveCurrent state.capabilities { caller } sourceWord sourceKind with
      | .error (.denied .invalidSubject) => .error .invalidSubject
      | .error _ => .error .staleSource
      | .ok source =>
          if state.capabilities.nextIdentity = 0 ∨
              CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity then
            .error .generationExhausted
          else offerCheck state caller endpoint.handle.slot source.handle.slot rights

theorem offerWords_eq (state : CapabilityTransfer.State) caller endpointWord sourceWord
    sourceKind payload (rights : Capability.Rights) :
    CapabilityTransfer.offerWords state caller endpointWord sourceWord sourceKind payload rights =
      match offerWordsCheck state caller endpointWord sourceWord sourceKind rights with
      | .error reason => CapabilityTransfer.reject state reason
      | .ok (endpointCap, source) =>
          { state := offerAccepted state caller endpointCap source payload rights
            result := .accepted } := by
  unfold CapabilityTransfer.offerWords offerWordsCheck
  generalize CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord
    .endpoint = endpoint
  generalize CapabilityHandle.resolveCurrent state.capabilities { caller } sourceWord
    sourceKind = source
  rcases endpoint with ((_ | _) | (_ | _ | _ | _)) | endpoint <;> try rfl
  rcases source with ((_ | _) | (_ | _ | _ | _)) | source <;> try rfl
  simp only
  split
  · rfl
  · exact offer_eq state caller _ _ payload rights

/-- What the transfer validations read about the caller: its row through
lookup and handle resolution, the registry and mailbox of every object a
found capability names, and the identity counter. -/
structure CallerInputs (a b : CapabilityTransfer.State) (caller : SubjectId) : Prop where
  resolve : ∀ word kind,
    CapabilityHandle.resolveCurrent a.capabilities { caller } word kind =
      CapabilityHandle.resolveCurrent b.capabilities { caller } word kind
  lookup : ∀ slot, Capability.lookup a.capabilities caller slot =
    Capability.lookup b.capabilities caller slot
  object : ∀ slot cap, Capability.lookup b.capabilities caller slot = .found cap →
    a.capabilities.objects cap.object = b.capabilities.objects cap.object ∧
      a.capabilities.kinds cap.object = b.capabilities.kinds cap.object ∧
      a.mailbox cap.object = b.mailbox cap.object ∧
      a.pending cap.object = b.pending cap.object
  slotCapacity : a.capabilities.slotCapacity caller = b.capabilities.slotCapacity caller
  slots : ∀ slot, slot < b.capabilities.slotCapacity caller →
    a.capabilities.slots caller slot = b.capabilities.slots caller slot

theorem offerCheck_congr (a b : CapabilityTransfer.State) caller (hinputs : CallerInputs a b caller)
    endpointSlot sourceSlot (rights : Capability.Rights) :
    offerCheck a caller endpointSlot sourceSlot rights =
      offerCheck b caller endpointSlot sourceSlot rights := by
  unfold offerCheck
  rw [hinputs.lookup endpointSlot, hinputs.lookup sourceSlot]
  cases hfound : Capability.lookup b.capabilities caller endpointSlot with
  | invalidSubject => rfl
  | staleSlot => rfl
  | found endpointCap =>
      obtain ⟨hobjects, hkinds, hmailbox, _⟩ := hinputs.object endpointSlot endpointCap hfound
      simp only [hobjects, hkinds, hmailbox]

theorem offerWordsCheck_congr (a b : CapabilityTransfer.State) caller
    (hinputs : CallerInputs a b caller)
    (hnext : a.capabilities.nextIdentity = b.capabilities.nextIdentity)
    endpointWord sourceWord sourceKind (rights : Capability.Rights) :
    offerWordsCheck a caller endpointWord sourceWord sourceKind rights =
      offerWordsCheck b caller endpointWord sourceWord sourceKind rights := by
  unfold offerWordsCheck
  rw [hinputs.resolve endpointWord, hinputs.resolve sourceWord, hnext]
  simp only [offerCheck_congr a b caller hinputs]

/-- Coherent low-equivalent states give the observer the same transfer
inputs. -/
theorem ownStep_callerInputs {observer left right} (h : OwnStep observer left right) :
    CallerInputs left.transfers right.transfers observer where
  resolve := fun word kind => (ownStep_transferResolve h) word kind
  lookup := (ownStep_transferLookup h)
  object := fun slot cap hfound => by
    rw [← (ownStep_transferLookup h) slot, (transfers_published h.leftWF.1).1] at hfound
    exact (ownStep_transferObject h) cap.object (names_of_lookup left observer slot cap hfound)
  slotCapacity := by
    rw [(transfers_published h.leftWF.1).1, (transfers_published h.rightWF.1).1]
    exact h.low.capacity
  slots := fun slot hslot => by
    rw [(transfers_published h.leftWF.1).1, (transfers_published h.rightWF.1).1] at *
    exact (h.low.slot slot (h.low.capacity ▸ hslot)).1

/-- The transfer-offer result the observer sees. -/
theorem offerWords_result (state : CapabilityTransfer.State) caller endpointWord sourceWord
    sourceKind payload (rights : Capability.Rights) :
    (CapabilityTransfer.offerWords state caller endpointWord sourceWord sourceKind payload
        rights).result =
      match offerWordsCheck state caller endpointWord sourceWord sourceKind rights with
      | .error reason => .rejected reason
      | .ok _ => .accepted := by
  rw [offerWords_eq]
  generalize offerWordsCheck state caller endpointWord sourceWord sourceKind rights = check
  rcases check with reason | ⟨endpointCap, source⟩ <;> rfl

theorem applyOperation_transferOffer (state : CompositeState) endpointWord sourceWord
    sourceKind payload (rights : Capability.Rights) :
    applyOperation state (.transferOffer endpointWord sourceWord sourceKind payload rights) =
      match offerWordsCheck state.transfers state.execution.core.context.currentSubject
          endpointWord sourceWord sourceKind rights with
      | .error _ => state
      | .ok (endpointCap, source) =>
          installTransfers state (offerAccepted state.transfers
            state.execution.core.context.currentSubject endpointCap source payload rights) := by
  simp only [applyOperation, offerWords_eq]
  generalize offerWordsCheck state.transfers state.execution.core.context.currentSubject
    endpointWord sourceWord sourceKind rights = check
  rcases check with reason | ⟨endpointCap, source⟩ <;> rfl

/-- **Step consistency of the observer's transfer offer** (counter public). -/
theorem own_step_offer {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (endpointWord sourceWord : UInt64)
    (sourceKind : Capability.ObjectKind) (payload : EndpointIPC.Payload)
    (rights : Capability.Rights) :
    LowEquiv observer
      (applyOperation left (.transferOffer endpointWord sourceWord sourceKind payload rights))
      (applyOperation right (.transferOffer endpointWord sourceWord sourceKind payload rights)) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  rw [applyOperation_transferOffer, applyOperation_transferOffer, hLs, hRs,
    offerWordsCheck_congr _ _ observer (ownStep_callerInputs h.toOwnStep) h.transferCounter]
  cases offerWordsCheck right.transfers observer endpointWord sourceWord sourceKind rights with
  | error reason => exact h.low
  | ok caps =>
      obtain ⟨endpointCap, source⟩ := caps
      apply transfer_row_named h.toOwnStep
        (offerAccepted left.transfers observer endpointCap source payload rights)
        (offerAccepted right.transfers observer endpointCap source payload rights)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      intro object hnames
      obtain ⟨_, _, hmailbox, hpending⟩ := (ownStep_transferObject h.toOwnStep) object hnames
      simp only [offerAccepted, CapabilityTransfer.record, EndpointIPC.setOption,
        CapabilityTransfer.setPending, h.transferCounter]
      constructor
      · split
        · rfl
        · exact hmailbox
      · split
        · rfl
        · exact hpending

/-- **Output consistency of the observer's transfer offer** (counter public). -/
theorem own_output_offer {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (endpointWord sourceWord : UInt64)
    (sourceKind : Capability.ObjectKind) (payload : EndpointIPC.Payload)
    (rights : Capability.Rights) :
    operationReply left (.transferOffer endpointWord sourceWord sourceKind payload rights) =
      operationReply right (.transferOffer endpointWord sourceWord sourceKind payload rights) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  simp only [operationReply, hLs, hRs, offerWords_result,
    offerWordsCheck_congr _ _ observer (ownStep_callerInputs h.toOwnStep) h.transferCounter]

theorem nextIdentity_transferOffer {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (endpointWord sourceWord : UInt64)
    (sourceKind : Capability.ObjectKind) (payload : EndpointIPC.Payload)
    (rights : Capability.Rights) :
    (applyOperation left (.transferOffer endpointWord sourceWord sourceKind payload
        rights)).capabilities.nextIdentity =
      (applyOperation right (.transferOffer endpointWord sourceWord sourceKind payload
        rights)).capabilities.nextIdentity := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  rw [applyOperation_transferOffer, applyOperation_transferOffer, hLs, hRs,
    offerWordsCheck_congr _ _ observer (ownStep_callerInputs h.toOwnStep) h.transferCounter]
  cases offerWordsCheck right.transfers observer endpointWord sourceWord sourceKind rights with
  | error reason => exact h.counter
  | ok caps =>
      simp only [installTransfers, offerAccepted, CapabilityTransfer.record]
      rw [h.transferCounter]

/-! ## Transfer receipt -/

/-- The validation performed by `CapabilityTransfer.accept`.  A successful
validation returns the endpoint capability, the queued envelope, and the
sealed transfer it carries, if any. -/
def acceptCheck (state : CapabilityTransfer.State) (caller : SubjectId)
    (endpointSlot destinationSlot : Nat) :
    Except CapabilityTransfer.AcceptError
      (Capability.Capability × EndpointIPC.Envelope × Option CapabilityTransfer.Sealed) :=
  match Capability.lookup state.capabilities caller endpointSlot with
  | .invalidSubject => .error .invalidSubject
  | .staleSlot => .error .staleEndpoint
  | .found endpointCap =>
    if endpointCap.kind != .endpoint then .error .wrongEndpointKind
    else if !endpointCap.rights.receive then .error .missingReceive
    else if state.capabilities.objects endpointCap.object != true then .error .retiredEndpoint
    else if state.capabilities.kinds endpointCap.object != some .endpoint then
      .error .retiredEndpoint
    else match state.mailbox endpointCap.object with
      | none => .error .empty
      | some envelope =>
        match state.pending endpointCap.object with
        | none => .ok (endpointCap, envelope, none)
        | some transfer =>
          if !Capability.slotInRange state.capabilities caller destinationSlot then
            .error .outOfRange
          else if (state.capabilities.slots caller destinationSlot).isSome then
            .error .occupiedSlot
          else if state.capabilities.objects transfer.object != true then .error .canceled
          else if state.capabilities.kinds transfer.object != some transfer.kind then
            .error .canceled
          else if state.capabilities.derivations transfer.identity !=
              some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) then
            .error .canceled
          else if !Capability.rightsValid transfer.kind transfer.rights then .error .canceled
          else .ok (endpointCap, envelope, some transfer)

/-- The update selected by a receipt validation. -/
def acceptOutcome (state : CapabilityTransfer.State) (caller destinationSlot : Nat) :
    Except CapabilityTransfer.AcceptError
      (Capability.Capability × EndpointIPC.Envelope × Option CapabilityTransfer.Sealed) →
    CapabilityTransfer.AcceptOutcome
  | .error reason => CapabilityTransfer.rejectAccept state reason
  | .ok (endpointCap, envelope, none) =>
      CapabilityTransfer.deliverData state caller endpointCap envelope
  | .ok (endpointCap, envelope, some transfer) =>
      CapabilityTransfer.deliver state caller destinationSlot endpointCap envelope transfer

theorem accept_eq (state : CapabilityTransfer.State) caller endpointSlot destinationSlot :
    CapabilityTransfer.accept state caller endpointSlot destinationSlot =
      acceptOutcome state caller destinationSlot
        (acceptCheck state caller endpointSlot destinationSlot) := by
  unfold CapabilityTransfer.accept acceptCheck
  cases Capability.lookup state.capabilities caller endpointSlot with
  | invalidSubject => rfl
  | staleSlot => rfl
  | found endpointCap =>
    simp only
    by_cases c1 : (endpointCap.kind != .endpoint) = true
    · simp only [c1, ↓reduceIte, Bool.false_eq_true]; rfl
    simp only [c1, ↓reduceIte, Bool.false_eq_true]
    by_cases c2 : (!endpointCap.rights.receive) = true
    · simp only [c2, ↓reduceIte, Bool.false_eq_true]; rfl
    simp only [c2, ↓reduceIte, Bool.false_eq_true]
    by_cases c3 : (state.capabilities.objects endpointCap.object != true) = true
    · simp only [c3, ↓reduceIte, Bool.false_eq_true]; rfl
    simp only [c3, ↓reduceIte, Bool.false_eq_true]
    by_cases c4 : (state.capabilities.kinds endpointCap.object != some .endpoint) = true
    · simp only [c4, ↓reduceIte, Bool.false_eq_true]; rfl
    simp only [c4, ↓reduceIte, Bool.false_eq_true]
    cases state.mailbox endpointCap.object with
    | none => rfl
    | some envelope =>
      simp only
      cases state.pending endpointCap.object with
      | none => rfl
      | some transfer =>
        simp only
        by_cases c5 : (!Capability.slotInRange state.capabilities caller destinationSlot) = true
        · simp only [c5, ↓reduceIte, Bool.false_eq_true]; rfl
        simp only [c5, ↓reduceIte, Bool.false_eq_true]
        by_cases c6 : (state.capabilities.slots caller destinationSlot).isSome = true
        · simp only [c6, ↓reduceIte, Bool.false_eq_true]; rfl
        simp only [c6, ↓reduceIte, Bool.false_eq_true]
        by_cases c7 : (state.capabilities.objects transfer.object != true) = true
        · simp only [c7, ↓reduceIte, Bool.false_eq_true]; rfl
        simp only [c7, ↓reduceIte, Bool.false_eq_true]
        by_cases c8 : (state.capabilities.kinds transfer.object != some transfer.kind) = true
        · simp only [c8, ↓reduceIte, Bool.false_eq_true]; rfl
        simp only [c8, ↓reduceIte, Bool.false_eq_true]
        by_cases c9 : (state.capabilities.derivations transfer.identity !=
            some (some transfer.parent, transfer.object, transfer.kind, transfer.rights)) = true
        · simp only [c9, ↓reduceIte, Bool.false_eq_true]; rfl
        simp only [c9, ↓reduceIte, Bool.false_eq_true]
        by_cases c10 : (!Capability.rightsValid transfer.kind transfer.rights) = true
        · simp only [c10, ↓reduceIte, Bool.false_eq_true]; rfl
        simp only [c10, ↓reduceIte, Bool.false_eq_true]
        rfl

/-- The validation performed by `CapabilityTransfer.acceptWord`. -/
def acceptWordCheck (state : CapabilityTransfer.State) (caller : SubjectId)
    (endpointWord : UInt64) (destinationSlot : Nat) :
    Except CapabilityTransfer.AcceptError
      (Capability.Capability × EndpointIPC.Envelope × Option CapabilityTransfer.Sealed) :=
  match CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord .endpoint with
  | .error (.denied .invalidSubject) => .error .invalidSubject
  | .error (.denied .kindMismatch) => .error .wrongEndpointKind
  | .error _ => .error .staleEndpoint
  | .ok endpoint =>
      match state.pending endpoint.capability.object with
        | some transfer =>
            if CapabilityHandle.slotReserved ≤ destinationSlot then .error .outOfRange
            else if transfer.identity = 0 ∨
                CapabilityHandle.generationReserved ≤ transfer.identity then
              .error .generationExhausted
            else acceptCheck state caller endpoint.handle.slot destinationSlot
        | none => acceptCheck state caller endpoint.handle.slot destinationSlot

theorem acceptWord_eq (state : CapabilityTransfer.State) caller endpointWord destinationSlot :
    CapabilityTransfer.acceptWord state caller endpointWord destinationSlot =
      acceptOutcome state caller destinationSlot
        (acceptWordCheck state caller endpointWord destinationSlot) := by
  unfold CapabilityTransfer.acceptWord acceptWordCheck
  generalize CapabilityHandle.resolveCurrent state.capabilities { caller } endpointWord
    .endpoint = endpoint
  rcases endpoint with ((_ | _) | (_ | _ | _ | _)) | endpoint <;> try rfl
  simp only
  cases state.pending endpoint.capability.object with
  | none => exact accept_eq state caller _ destinationSlot
  | some transfer =>
      simp only
      split
      · rfl
      · split
        · rfl
        · exact accept_eq state caller _ destinationSlot

/-- Every pending sealed transfer names a live object of its kind and its
recorded derivation; `CapabilityTransfer.WellFormed` provides this. -/
def PendingValid (state : CapabilityTransfer.State) : Prop :=
  ∀ endpoint transfer, state.pending endpoint = some transfer →
    state.capabilities.objects transfer.object = true ∧
      state.capabilities.kinds transfer.object = some transfer.kind ∧
      state.capabilities.derivations transfer.identity =
        some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) ∧
      Capability.rightsValid transfer.kind transfer.rights = true

theorem pendingValid_of_wellFormed {state : CapabilityTransfer.State}
    (hstate : CapabilityTransfer.WellFormed state) : PendingValid state := by
  intro endpoint transfer hpending
  obtain ⟨_, hobject, hkind, hrights, hderivation, _⟩ := hstate.2 endpoint transfer hpending
  exact ⟨hobject, hkind, hderivation, hrights⟩

theorem acceptCheck_congr (a b : CapabilityTransfer.State) caller
    (hinputs : CallerInputs a b caller) (ha : PendingValid a) (hb : PendingValid b)
    endpointSlot destinationSlot :
    acceptCheck a caller endpointSlot destinationSlot =
      acceptCheck b caller endpointSlot destinationSlot := by
  unfold acceptCheck
  rw [hinputs.lookup endpointSlot]
  cases hfound : Capability.lookup b.capabilities caller endpointSlot with
  | invalidSubject => rfl
  | staleSlot => rfl
  | found endpointCap =>
      obtain ⟨hobjects, hkinds, hmailbox, hpending⟩ :=
        hinputs.object endpointSlot endpointCap hfound
      simp only [hobjects, hkinds, hmailbox, hpending, Capability.slotInRange,
        hinputs.slotCapacity]
      cases b.mailbox endpointCap.object with
      | none => rfl
      | some envelope =>
          simp only
          cases hb' : b.pending endpointCap.object with
          | none => rfl
          | some transfer =>
              simp only
              obtain ⟨haobj, hakind, haderiv, _⟩ :=
                ha endpointCap.object transfer (hpending.trans hb')
              obtain ⟨hbobj, hbkind, hbderiv, _⟩ := hb endpointCap.object transfer hb'
              simp only [haobj, hakind, haderiv, hbobj, hbkind, hbderiv]
              by_cases hin : destinationSlot < b.capabilities.slotCapacity caller
              · simp only [hinputs.slots destinationSlot hin]
              · simp only [decide_eq_true_eq, hin, decide_false, Bool.not_false,
                  ↓reduceIte]

theorem acceptWordCheck_congr (a b : CapabilityTransfer.State) caller
    (hinputs : CallerInputs a b caller) (ha : PendingValid a) (hb : PendingValid b)
    endpointWord destinationSlot :
    acceptWordCheck a caller endpointWord destinationSlot =
      acceptWordCheck b caller endpointWord destinationSlot := by
  unfold acceptWordCheck
  rw [hinputs.resolve endpointWord]
  cases hresolve : CapabilityHandle.resolveCurrent b.capabilities { caller } endpointWord
      .endpoint with
  | error reason => rcases reason with (_ | _) | (_ | _ | _ | _) <;> rfl
  | ok endpoint =>
      have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
      obtain ⟨_, _, _, hpending⟩ := hinputs.object _ _ hlookup
      simp only [hpending, acceptCheck_congr a b caller hinputs ha hb]

/-- The receipt result and delivered word are a function of the validation. -/
theorem acceptOutcome_reply (a b : CapabilityTransfer.State) caller destinationSlot check :
    (acceptOutcome a caller destinationSlot check).result =
        (acceptOutcome b caller destinationSlot check).result ∧
      (acceptOutcome a caller destinationSlot check).deliveredWord =
        (acceptOutcome b caller destinationSlot check).deliveredWord := by
  rcases check with reason | ⟨endpointCap, envelope, _ | transfer⟩ <;> exact ⟨rfl, rfl⟩

theorem ownStep_pendingValid {observer left right} (h : OwnStep observer left right) :
    PendingValid left.transfers ∧ PendingValid right.transfers :=
  ⟨pendingValid_of_wellFormed h.leftWF.2.2.2.2.2.2.2.2.2.1,
    pendingValid_of_wellFormed h.rightWF.2.2.2.2.2.2.2.2.2.1⟩

/-- **Output consistency of the observer's transfer receipt.**  The result
and the delivered handle word depend only on the observer's row, its named
endpoints, and (by `CapabilityTransfer.WellFormed`) nothing about the carried
object. -/
theorem own_output_accept {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (endpointWord : UInt64) (destinationSlot : Nat) :
    operationReply left (.transferAccept endpointWord destinationSlot) =
      operationReply right (.transferAccept endpointWord destinationSlot) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  obtain ⟨hLvalid, hRvalid⟩ := (ownStep_pendingValid h)
  simp only [operationReply, hLs, hRs, acceptWord_eq,
    acceptWordCheck_congr _ _ observer (ownStep_callerInputs h) hLvalid hRvalid]
  rw [(acceptOutcome_reply left.transfers right.transfers observer destinationSlot _).1,
    (acceptOutcome_reply left.transfers right.transfers observer destinationSlot _).2]

theorem applyOperation_transferAccept (state : CompositeState) endpointWord destinationSlot :
    applyOperation state (.transferAccept endpointWord destinationSlot) =
      match acceptWordCheck state.transfers state.execution.core.context.currentSubject
          endpointWord destinationSlot with
      | .error _ => state
      | check => installTransfers state (acceptOutcome state.transfers
          state.execution.core.context.currentSubject destinationSlot check).state := by
  simp only [applyOperation, acceptWord_eq]
  generalize acceptWordCheck state.transfers state.execution.core.context.currentSubject
    endpointWord destinationSlot = check
  rcases check with reason | ⟨endpointCap, envelope, _ | transfer⟩ <;> rfl

/-- The objects carried by sealed transfers pending on endpoints the observer
names have the same view in both states.  Receipt makes the carried object
part of the observer's authority; this agreement is the information flow the
sender's offer authorizes. -/
def CarriedAgree (observer : SubjectId) (left right : CompositeState) : Prop :=
  ∀ object transfer, Names left observer object = true →
    left.transfers.pending object = some transfer →
    CompositeObservation.objectView left transfer.object =
      CompositeObservation.objectView right transfer.object

theorem acceptCheck_ok (a : CapabilityTransfer.State) caller endpointSlot destinationSlot
    endpointCap envelope sealed
    (hcheck : acceptCheck a caller endpointSlot destinationSlot =
      .ok (endpointCap, envelope, sealed)) :
    Capability.lookup a.capabilities caller endpointSlot = .found endpointCap ∧
      a.pending endpointCap.object = sealed ∧
      (∀ transfer, sealed = some transfer →
        destinationSlot < a.capabilities.slotCapacity caller ∧
          a.capabilities.slots caller destinationSlot = none) := by
  unfold acceptCheck at hcheck
  cases hfound : Capability.lookup a.capabilities caller endpointSlot with
  | invalidSubject => simp only [hfound] at hcheck; cases hcheck
  | staleSlot => simp only [hfound] at hcheck; cases hcheck
  | found found =>
    simp only [hfound] at hcheck
    by_cases c1 : (found.kind != .endpoint) = true
    · simp only [c1, ↓reduceIte] at hcheck; cases hcheck
    simp only [c1, ↓reduceIte, Bool.false_eq_true] at hcheck
    by_cases c2 : (!found.rights.receive) = true
    · simp only [c2, ↓reduceIte] at hcheck; cases hcheck
    simp only [c2, ↓reduceIte, Bool.false_eq_true] at hcheck
    by_cases c3 : (a.capabilities.objects found.object != true) = true
    · simp only [c3, ↓reduceIte] at hcheck; cases hcheck
    simp only [c3, ↓reduceIte, Bool.false_eq_true] at hcheck
    by_cases c4 : (a.capabilities.kinds found.object != some .endpoint) = true
    · simp only [c4, ↓reduceIte] at hcheck; cases hcheck
    simp only [c4, ↓reduceIte, Bool.false_eq_true] at hcheck
    cases hmail : a.mailbox found.object with
    | none => simp only [hmail] at hcheck; cases hcheck
    | some queued =>
      simp only [hmail] at hcheck
      cases hpending : a.pending found.object with
      | none =>
          simp only [hpending, Except.ok.injEq, Prod.mk.injEq] at hcheck
          obtain ⟨rfl, _, rfl⟩ := hcheck
          exact ⟨rfl, hpending, fun _ h => by cases h⟩
      | some transfer =>
          simp only [hpending] at hcheck
          by_cases c5 : (!Capability.slotInRange a.capabilities caller destinationSlot) = true
          · simp only [c5, ↓reduceIte] at hcheck; cases hcheck
          simp only [c5, ↓reduceIte, Bool.false_eq_true] at hcheck
          by_cases c6 : (a.capabilities.slots caller destinationSlot).isSome = true
          · simp only [c6, ↓reduceIte] at hcheck; cases hcheck
          simp only [c6, ↓reduceIte, Bool.false_eq_true] at hcheck
          by_cases c7 : (a.capabilities.objects transfer.object != true) = true
          · simp only [c7, ↓reduceIte] at hcheck; cases hcheck
          simp only [c7, ↓reduceIte, Bool.false_eq_true] at hcheck
          by_cases c8 : (a.capabilities.kinds transfer.object != some transfer.kind) = true
          · simp only [c8, ↓reduceIte] at hcheck; cases hcheck
          simp only [c8, ↓reduceIte, Bool.false_eq_true] at hcheck
          by_cases c9 : (a.capabilities.derivations transfer.identity !=
              some (some transfer.parent, transfer.object, transfer.kind,
                transfer.rights)) = true
          · simp only [c9, ↓reduceIte] at hcheck; cases hcheck
          simp only [c9, ↓reduceIte, Bool.false_eq_true] at hcheck
          by_cases c10 : (!Capability.rightsValid transfer.kind transfer.rights) = true
          · simp only [c10, ↓reduceIte] at hcheck; cases hcheck
          simp only [c10, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq,
            Prod.mk.injEq] at hcheck
          obtain ⟨rfl, _, rfl⟩ := hcheck
          refine ⟨rfl, hpending, fun _ _ => ⟨?_, ?_⟩⟩
          · simpa [Capability.slotInRange] using c5
          · simpa using c6

theorem acceptWordCheck_ok (a : CapabilityTransfer.State) caller endpointWord destinationSlot
    endpointCap envelope sealed
    (hcheck : acceptWordCheck a caller endpointWord destinationSlot =
      .ok (endpointCap, envelope, sealed)) :
    ∃ slot, Capability.lookup a.capabilities caller slot = .found endpointCap ∧
      a.pending endpointCap.object = sealed ∧
      (∀ transfer, sealed = some transfer →
        destinationSlot < a.capabilities.slotCapacity caller ∧
          a.capabilities.slots caller destinationSlot = none) := by
  unfold acceptWordCheck at hcheck
  split at hcheck
  · cases hcheck
  · cases hcheck
  · cases hcheck
  · split at hcheck
    · split at hcheck
      · cases hcheck
      · split at hcheck
        · cases hcheck
        · exact ⟨_, acceptCheck_ok a caller _ destinationSlot _ _ _ hcheck⟩
    · exact ⟨_, acceptCheck_ok a caller _ destinationSlot _ _ _ hcheck⟩

theorem capabilitySpace_install_self (capabilities : Capability.State) (subject slot : Nat)
    (cap : Capability.Capability) :
    Capability.capabilitySpace (Capability.install capabilities subject slot cap) subject =
      (List.range (capabilities.slotCapacity subject)).map fun candidate =>
        if candidate = slot then some cap else capabilities.slots subject candidate := by
  simp [Capability.capabilitySpace, Capability.install]

/-- **Step consistency of the observer's transfer receipt**, given agreement on
the objects carried to its endpoints.  A data-only receipt (no sealed transfer
pending) needs no such agreement: `CarriedAgree` is only consulted for the
carried object. -/
theorem own_step_accept {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (hcarried : CarriedAgree observer left right)
    (endpointWord : UInt64) (destinationSlot : Nat) :
    LowEquiv observer (applyOperation left (.transferAccept endpointWord destinationSlot))
      (applyOperation right (.transferAccept endpointWord destinationSlot)) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  obtain ⟨hLvalid, hRvalid⟩ := (ownStep_pendingValid h)
  have hcongr := acceptWordCheck_congr _ _ observer (ownStep_callerInputs h) hLvalid hRvalid
    endpointWord destinationSlot
  rw [applyOperation_transferAccept, applyOperation_transferAccept, hLs, hRs, hcongr]
  cases hcheck : acceptWordCheck right.transfers observer endpointWord destinationSlot with
  | error reason => exact h.low
  | ok result =>
      obtain ⟨endpointCap, envelope, sealed⟩ := result
      obtain ⟨slot, hfoundL, hpendingL, hdestL⟩ :=
        acceptWordCheck_ok _ _ _ _ _ _ _ (hcongr.trans hcheck)
      have hLcaps := (transfers_published h.leftWF.1).1
      have hRcaps := (transfers_published h.rightWF.1).1
      have hnamesEndpoint : Names left observer endpointCap.object = true := by
        rw [hLcaps] at hfoundL
        exact names_of_lookup left observer slot endpointCap hfoundL
      cases sealed with
      | none =>
          apply transfer_row_named h
            (CapabilityTransfer.deliverData left.transfers observer endpointCap envelope).state
            (CapabilityTransfer.deliverData right.transfers observer endpointCap envelope).state
            ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
          intro object hnames
          obtain ⟨_, _, hmailbox, hpending⟩ := (ownStep_transferObject h) object hnames
          simp only [CapabilityTransfer.deliverData, CapabilityTransfer.record,
            EndpointIPC.setOption]
          refine ⟨?_, hpending⟩
          split
          · rfl
          · exact hmailbox
      | some transfer =>
          have hview := hcarried endpointCap.object transfer hnamesEndpoint hpendingL
          obtain ⟨hLobj, hLkind, _, _⟩ := hLvalid endpointCap.object transfer hpendingL
          obtain ⟨_, _, _, hRpending⟩ := (ownStep_transferObject h) endpointCap.object hnamesEndpoint
          obtain ⟨hRobj, hRkind, _, _⟩ :=
            hRvalid endpointCap.object transfer (hRpending ▸ hpendingL)
          have hcapacity : left.transfers.capabilities.slotCapacity observer =
              right.transfers.capabilities.slotCapacity observer := by
            rw [hLcaps, hRcaps]
            exact h.low.capacity
          have hslotEq : ∀ candidate, candidate < left.transfers.capabilities.slotCapacity
              observer → left.transfers.capabilities.slots observer candidate =
                right.transfers.capabilities.slots observer candidate := by
            intro candidate hcandidate
            rw [hLcaps, hRcaps] at *
            exact (h.low.slot candidate hcandidate).1
          have hmailboxCarried := congrArg ObjectView.mailbox hview
          have hsealedCarried := congrArg ObjectView.sealed hview
          simp only [CompositeObservation.objectView] at hmailboxCarried hsealedCarried
          rw [← (transfers_published h.leftWF.1).2, ← (transfers_published h.rightWF.1).2]
            at hmailboxCarried
          dsimp only [acceptOutcome]
          apply lowEquiv_installTransfers h.low
          · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
              Capability.install]
            rw [hLcaps, hRcaps]
            exact h.low.live
          · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
              Capability.install]
            exact hcapacity
          · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record]
            rw [capabilitySpace_install_self, capabilitySpace_install_self, hcapacity]
            apply List.map_congr_left
            intro candidate hmem
            rw [List.mem_range] at hmem
            split
            · rfl
            · exact hslotEq candidate (hcapacity ▸ hmem)
          · intro cap hmem
            simp only [CapabilityTransfer.deliver, CapabilityTransfer.record] at hmem
            rw [capabilitySpace_install_self, List.mem_map] at hmem
            obtain ⟨candidate, hrange, hslot⟩ := hmem
            rw [List.mem_range] at hrange
            split at hslot
            · simp only [Option.some.injEq] at hslot
              rw [← hslot]
              refine ⟨hview, ?_, ?_, ?_, ?_⟩
              · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  Capability.install]
                rw [hLobj, hRobj]
              · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  Capability.install]
                rw [hLkind, hRkind]
              · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  EndpointIPC.setOption]
                split
                · rfl
                · exact hmailboxCarried
              · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  CapabilityTransfer.setPending]
                split
                · rfl
                · exact hsealedCarried
            · have hnames : Names left observer cap.object = true := by
                have hrow : some cap ∈ row left observer := by
                  rw [List.mem_iff_getElem?]
                  refine ⟨candidate, ?_⟩
                  rw [hLcaps] at hrange hslot
                  rw [row_getElem? left observer candidate hrange, hslot]
                simp only [Names, List.any_eq_true]
                exact ⟨some cap, hrow, by simp⟩
              obtain ⟨hobjects, hkinds, hmailbox, hpending⟩ :=
                (ownStep_transferObject h) cap.object hnames
              refine ⟨h.low.namedView cap.object hnames, ?_, ?_, ?_, ?_⟩
              · simpa [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  Capability.install] using hobjects
              · simpa [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  Capability.install] using hkinds
              · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  EndpointIPC.setOption]
                split
                · rfl
                · exact hmailbox
              · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
                  CapabilityTransfer.setPending]
                split
                · rfl
                · exact hpending

/-! ## Subject creation of the observer itself -/

/-- The scheduled observer is live, so creating it is rejected and changes
nothing. -/
theorem create_self_rejected {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    SubjectLifecycle.create state.lifecycle observer =
      SubjectLifecycle.reject state.lifecycle .alreadyLive := by
  rcases hstate with ⟨hcoherent, _, _, _, _, _, hscheduler, _⟩
  have hlive := (hscheduler.2.2.2.2 observer (by rw [hcoherent.2.1]; exact hcurrent)).1
  rw [hcoherent.2.1] at hlive
  simp [SubjectLifecycle.create, hlive]

theorem apply_create_self {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    applyOperation state (.createSubject observer) = state := by
  simp only [applyOperation, create_self_rejected hstate hcurrent, SubjectLifecycle.reject]

theorem reply_create_self {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    operationReply state (.createSubject observer) =
      .createSubject (.rejected .alreadyLive) := by
  simp only [operationReply, create_self_rejected hstate hcurrent, SubjectLifecycle.reject]

/-! ## Scheduler operations -/

/-- The composite never applies a raw scheduler selection: `scheduleNext` either
rejects, selects nothing, or is redirected to the resumable switch. -/
theorem apply_scheduleNext (state : CompositeState) :
    applyOperation state .scheduleNext = state := by
  simp only [applyOperation, schedulerDispatch]
  generalize Scheduler.selectNext state.scheduler = outcome
  rcases outcome with ⟨scheduler, (_ | _) | _⟩ <;> rfl

/-- A raw yield is always redirected to the resumable switch. -/
theorem apply_scheduleYield (state : CompositeState) :
    applyOperation state .scheduleYield = state := by
  simp only [applyOperation, schedulerYield]
  generalize Scheduler.yield state.scheduler = outcome
  rcases outcome with ⟨scheduler, _ | _⟩ <;> rfl

theorem apply_scheduleTick (state : CompositeState) :
    applyOperation state .scheduleTick = state := by
  simp only [applyOperation, schedulerTick]
  generalize Scheduler.tick state.scheduler = outcome
  rcases outcome with ⟨scheduler, _ | _⟩ <;> rfl

/-- Queue admission writes only scheduler queues, never a projection the view
reads. -/
theorem observe_apply_scheduleAdd (observer : SubjectId) (state : CompositeState)
    (subject : SubjectId) :
    observe observer (applyOperation state (.scheduleAdd subject)) = observe observer state := by
  simp only [applyOperation]
  split
  · rfl
  · rfl

theorem observe_installSchedulerRemoval (observer : SubjectId) (state : CompositeState)
    (resumable : ResumablePreemption.State) :
    observe observer (installSchedulerRemoval state resumable) =
      { observe observer state with scheduled := resumable.scheduler.lifecycle.current } :=
  rfl

theorem scheduler_remove_accepted_current (scheduler : Scheduler.State) (subject : SubjectId)
    (context : Option Scheduler.TrustedContext)
    (haccepted : (Scheduler.remove scheduler subject).result = .accepted context) :
    (Scheduler.remove scheduler subject).state.lifecycle.current =
      if scheduler.lifecycle.current = some subject then none
      else scheduler.lifecycle.current := by
  unfold Scheduler.remove at haccepted ⊢
  split
  · rfl
  · rename_i hnot
    simp only [hnot, Bool.false_eq_true, ↓reduceIte, Scheduler.reject] at haccepted
    cases haccepted

theorem remove_accepted_current (resumable : ResumablePreemption.State) (subject : SubjectId)
    (context : Option Scheduler.TrustedContext)
    (haccepted : (ResumablePreemption.remove resumable subject).result = .accepted context) :
    (ResumablePreemption.remove resumable subject).state.scheduler.lifecycle.current =
      if resumable.scheduler.lifecycle.current = some subject then none
      else resumable.scheduler.lifecycle.current := by
  unfold ResumablePreemption.remove at haccepted ⊢
  generalize hraw : Scheduler.remove resumable.scheduler subject = raw at haccepted ⊢
  rcases raw with ⟨next, context' | reason⟩
  · dsimp only at haccepted ⊢
    split
    · simp only [ResumablePreemption.removeState]
      rw [← scheduler_remove_accepted_current resumable.scheduler subject context'
        (by rw [hraw]), hraw]
    · split at haccepted
      · contradiction
      · cases haccepted
  · cases haccepted

theorem resumable_lifecycle {state : CompositeState} (hcoherent : state.Coherent) :
    state.resumable.scheduler.lifecycle = state.lifecycle := by
  rw [hcoherent.2.2.2.2.2.2.2.1, hcoherent.2.1]

/-- Removing another subject keeps the scheduled observer, so it leaves the
observer's view unchanged. -/
theorem observe_apply_scheduleRemove_other {observer subject : SubjectId}
    {state : CompositeState} (hcoherent : state.Coherent)
    (hcurrent : state.lifecycle.current = some observer) (hne : observer ≠ subject) :
    observe observer (applyOperation state (.scheduleRemove subject)) =
      observe observer state := by
  simp only [applyOperation]
  split
  · rfl
  · rename_i context haccepted
    rw [observe_installSchedulerRemoval,
      remove_accepted_current _ _ context haccepted, resumable_lifecycle hcoherent, hcurrent]
    simp only [Option.some.injEq, hne, ↓reduceIte]
    rw [← hcurrent]
    rfl

/-- The scheduled observer's removal is always accepted. -/
theorem remove_self_accepted {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    ∃ context, (ResumablePreemption.remove state.resumable observer).result =
      .accepted context := by
  have hlifecycle := resumable_lifecycle hstate.1
  unfold ResumablePreemption.remove
  generalize hraw : Scheduler.remove state.resumable.scheduler observer = raw
  rcases raw with ⟨next, result⟩
  have hqueued : (Scheduler.remove state.resumable.scheduler observer).result = .accepted := by
    simp [Scheduler.remove, hlifecycle, hcurrent]
  rw [hraw] at hqueued
  simp only at hqueued
  subst hqueued
  have hnone := scheduler_remove_accepted_current state.resumable.scheduler observer none
    (by rw [hraw])
  rw [hraw, hlifecycle, hcurrent] at hnone
  simp only [↓reduceIte] at hnone
  simp only
  split
  · exact ⟨none, rfl⟩
  · rename_i hpeer
    exfalso
    apply hpeer
    intro hsome
    simp [ResumablePreemption.removeState, hnone] at hsome

theorem observe_apply_scheduleRemove_self {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    observe observer (applyOperation state (.scheduleRemove observer)) =
      { observe observer state with scheduled := none } := by
  obtain ⟨context, haccepted⟩ := remove_self_accepted hstate hcurrent
  simp only [applyOperation, haccepted]
  rw [observe_installSchedulerRemoval, remove_accepted_current _ _ context haccepted,
    resumable_lifecycle hstate.1, hcurrent]
  simp

/-- **Step consistency of the observer's queue removal**, for any subject. -/
theorem own_step_scheduleRemove {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (subject : SubjectId) :
    LowEquiv observer (applyOperation left (.scheduleRemove subject))
      (applyOperation right (.scheduleRemove subject)) := by
  by_cases hsubject : observer = subject
  · subst hsubject
    unfold LowEquiv
    rw [observe_apply_scheduleRemove_self h.leftWF h.current,
      observe_apply_scheduleRemove_self h.rightWF h.rightCurrent, h.low]
  · exact lowEquiv_of_unchanged h.low
      (observe_apply_scheduleRemove_other h.leftWF.1 h.current hsubject)
      (observe_apply_scheduleRemove_other h.rightWF.1 h.rightCurrent hsubject)

/-- The scheduler state treated as a public input: the ready queue and its
capacity.  The scheduler's choice is a public input of the claim. -/
structure SchedulerPublic (left right : CompositeState) : Prop where
  ready : left.scheduler.ready = right.scheduler.ready
  capacity : left.scheduler.capacity = right.scheduler.capacity

/-- In a well-formed scheduler with a current subject, a raw yield rejects only
for a full queue: every subject it could select owns its address space. -/
theorem yield_result {scheduler : Scheduler.State} {subject : SubjectId}
    (hscheduler : Scheduler.WellFormed scheduler)
    (hcurrent : scheduler.lifecycle.current = some subject) :
    ((Scheduler.yield scheduler).result matches .rejected .queueFull) =
        (scheduler.ready.length == scheduler.capacity) ∧
      ((Scheduler.yield scheduler).result matches .rejected _) =
        (scheduler.ready.length == scheduler.capacity) := by
  obtain ⟨_, _, _, hready, hcurrentOwns⟩ := hscheduler
  have howns : ∀ candidate, candidate ∈ scheduler.ready ++ [subject] →
      scheduler.lifecycle.addressOwner candidate = some candidate := by
    intro candidate hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    have hsome : Scheduler.ownsAddressSpace scheduler candidate ≠ none := by
      rcases hmem with hmem | rfl
      · exact (hready candidate hmem).2.2
      · exact (hcurrentOwns candidate hcurrent).2.2.1
    unfold Scheduler.ownsAddressSpace at hsome
    split at hsome
    · assumption
    · contradiction
  unfold Scheduler.yield
  simp only [hcurrent]
  by_cases hfull : scheduler.ready.length = scheduler.capacity
  · simp [hfull, Scheduler.reject]
  · simp only [hfull, ↓reduceIte]
    have hhead := howns
    cases hlist : scheduler.ready ++ [subject] with
    | nil => simp at hlist
    | cons head rest =>
        have hown := howns head (by rw [hlist]; exact List.mem_cons_self)
        simp only [Scheduler.selectNext, hlist, Scheduler.ownsAddressSpace, hown,
          ↓reduceIte]
        simp [hfull]

theorem schedulerYield_result {state : CompositeState} {observer : SubjectId}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    (schedulerYield state).result =
      if state.scheduler.ready.length = state.scheduler.capacity then .rejected .queueFull
      else .rejected .noResumableContext := by
  have hscheduler : Scheduler.WellFormed state.scheduler := hstate.2.2.2.2.2.2.1
  have hcurrent' : state.scheduler.lifecycle.current = some observer := by
    rw [hstate.1.2.1]
    exact hcurrent
  obtain ⟨hfullIff, hrejectIff⟩ := yield_result hscheduler hcurrent'
  unfold schedulerYield
  generalize hyield : Scheduler.yield state.scheduler = outcome at hfullIff hrejectIff
  rcases outcome with ⟨next, result⟩
  by_cases hfull : state.scheduler.ready.length = state.scheduler.capacity
  · simp only [hfull, beq_self_eq_true] at hfullIff
    rcases result with context | reason
    · simp at hfullIff
    · cases reason <;> simp_all [Scheduler.reject]
  · simp only [hfull, ↓reduceIte]
    have hne : (state.scheduler.ready.length == state.scheduler.capacity) = false := by
      simp [hfull]
    rw [hne] at hrejectIff
    rcases result with context | reason
    · rfl
    · simp at hrejectIff

theorem schedulerTick_result {state : CompositeState} {observer : SubjectId}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    (schedulerTick state).result =
      if state.scheduler.ready.length = state.scheduler.capacity then .rejected .queueFull
      else .rejected .noResumableContext := by
  rw [← schedulerYield_result hstate hcurrent]
  rfl

theorem scheduler_remove_congr (first second : Scheduler.State) (subject : SubjectId)
    (hcurrent : first.lifecycle.current = second.lifecycle.current)
    (hready : first.ready = second.ready) :
    (Scheduler.remove first subject).result = (Scheduler.remove second subject).result ∧
      (Scheduler.remove first subject).state.lifecycle.current =
        (Scheduler.remove second subject).state.lifecycle.current ∧
      (Scheduler.remove first subject).state.ready =
        (Scheduler.remove second subject).state.ready := by
  unfold Scheduler.remove
  simp only [hcurrent, hready]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, hcurrent, hready⟩

theorem remove_result_eq (resumable : ResumablePreemption.State) (subject : SubjectId) :
    (ResumablePreemption.remove resumable subject).result =
      match Scheduler.remove resumable.scheduler subject with
      | { result := .rejected reason, .. } => .rejected (.scheduler reason)
      | { state := scheduler, result := .accepted context } =>
          if _h : scheduler.lifecycle.current.isSome = true → scheduler.ready ≠ [] then
            .accepted context
          else .rejected .noResumablePeer := by
  unfold ResumablePreemption.remove
  generalize Scheduler.remove resumable.scheduler subject = raw
  rcases raw with ⟨next, context | reason⟩
  · dsimp only [ResumablePreemption.removeState]
    split <;> rfl
  · rfl

/-- `scheduleRemove` replies from the current subject and the ready queue
alone. -/
theorem remove_result_congr (first second : ResumablePreemption.State) (subject : SubjectId)
    (hcurrent : first.scheduler.lifecycle.current = second.scheduler.lifecycle.current)
    (hready : first.scheduler.ready = second.scheduler.ready) :
    (ResumablePreemption.remove first subject).result =
      (ResumablePreemption.remove second subject).result := by
  rw [remove_result_eq, remove_result_eq]
  obtain ⟨hresult, hcurrent', hready'⟩ :=
    scheduler_remove_congr first.scheduler second.scheduler subject hcurrent hready
  generalize Scheduler.remove first.scheduler subject = firstRaw at *
  generalize Scheduler.remove second.scheduler subject = secondRaw at *
  rcases firstRaw with ⟨firstNext, firstContext | firstReason⟩ <;>
    rcases secondRaw with ⟨secondNext, secondContext | secondReason⟩ <;>
    simp only at hresult hcurrent' hready' ⊢
  · cases hresult
    rw [hcurrent', hready']
  · cases hresult
  · cases hresult
  · cases hresult
    rfl

/-- **Output consistency of the observer's scheduler operations** that read
only the public scheduler state: `scheduleYield`, `scheduleTick`, and
`scheduleRemove`. -/
theorem own_output_scheduler {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (hpublic : SchedulerPublic left right)
    (operation : Operation)
    (hfamily : (match operation with
      | .scheduleYield | .scheduleTick | .scheduleRemove _ => true
      | _ => false) = true) :
    operationReply left operation = operationReply right operation := by
  cases operation with
  | scheduleYield =>
      simp only [operationReply, schedulerYield_result h.leftWF h.current,
        schedulerYield_result h.rightWF h.rightCurrent, hpublic.ready, hpublic.capacity]
  | scheduleTick =>
      simp only [operationReply, schedulerTick_result h.leftWF h.current,
        schedulerTick_result h.rightWF h.rightCurrent, hpublic.ready, hpublic.capacity]
  | scheduleRemove subject =>
      have hL : left.resumable.scheduler = left.scheduler := h.leftWF.1.2.2.2.2.2.2.2.1
      have hR : right.resumable.scheduler = right.scheduler := h.rightWF.1.2.2.2.2.2.2.2.1
      simp only [operationReply]
      rw [remove_result_congr left.resumable right.resumable subject
        (by rw [resumable_lifecycle h.leftWF.1, resumable_lifecycle h.rightWF.1, h.current,
          h.rightCurrent])
        (by rw [hL, hR, hpublic.ready])]
  | _ => simp at hfamily

/-- `scheduleNext` while the observer is scheduled always rejects as a
duplicate selection. -/
theorem reply_scheduleNext {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    operationReply state .scheduleNext = .scheduler (.rejected .duplicate) := by
  have hcurrent' : state.scheduler.lifecycle.current = some observer := by
    rw [hstate.1.2.1]
    exact hcurrent
  simp [operationReply, schedulerDispatch, Scheduler.selectNext, hcurrent', Scheduler.reject]

/-- `terminateCurrent` by the scheduled observer always terminates it: the
observer is live and issued. -/
theorem reply_terminateCurrent {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    operationReply state .terminateCurrent = .scheduler .accepted := by
  rcases hstate with ⟨hcoherent, _, hlifecycle, _, _, _, hscheduler, _⟩
  have hcurrent' : state.scheduler.lifecycle.current = some observer := by
    rw [hcoherent.2.1]
    exact hcurrent
  have hlive := (hscheduler.2.2.2.2 observer hcurrent').1
  have hissued := hscheduler.1.1 observer hlive
  simp [operationReply, Scheduler.terminateCurrent, hcurrent', SubjectLifecycle.terminate,
    hlive, hissued]

/-- Terminating itself, the scheduled observer is accepted: it is live and
issued. -/
theorem reply_terminate_self {observer : SubjectId} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    operationReply state (.terminateSubject observer) = .terminateSubject .accepted := by
  rcases hstate with ⟨hcoherent, _, hlifecycle, _, _, _, hscheduler, _⟩
  have hcurrent' : state.scheduler.lifecycle.current = some observer := by
    rw [hcoherent.2.1]
    exact hcurrent
  have hlive := (hscheduler.2.2.2.2 observer hcurrent').1
  have hissued := hscheduler.1.1 observer hlive
  rw [hcoherent.2.1] at hlive hissued
  simp [operationReply, SubjectLifecycle.terminate, hlive, hissued]

/-! ## Subtree revocation of the observer's own capability: output

Rights attenuate along every recorded derivation edge, so in a well-formed
capability store every descendant of a capability has a subset of its rights.
The runtime-safety check of subtree revocation therefore reduces to the rights
of the revoked capability itself, which the observer's row shows. -/

theorem rightsSubset_trans {first second third : Capability.Rights}
    (hfirst : Capability.rightsSubset first second = true)
    (hsecond : Capability.rightsSubset second third = true) :
    Capability.rightsSubset first third = true := by
  rcases first with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases second with ⟨b1, b2, b3, b4, b5, b6⟩
  rcases third with ⟨c1, c2, c3, c4, c5, c6⟩
  simp only [Capability.rightsSubset, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    at hfirst hsecond ⊢
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hfirst
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := hsecond
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · cases a1 <;> cases b1 <;> simp_all
  · cases a2 <;> cases b2 <;> simp_all
  · cases a3 <;> cases b3 <;> simp_all
  · cases a4 <;> cases b4 <;> simp_all
  · cases a5 <;> cases b5 <;> simp_all
  · cases a6 <;> cases b6 <;> simp_all

theorem rightsSubset_refl (rights : Capability.Rights) :
    Capability.rightsSubset rights rights = true := by
  rcases rights with ⟨a1, a2, a3, a4, a5, a6⟩
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> rfl

theorem not_critical_of_subset {rights bound : Capability.Rights}
    (hsubset : Capability.rightsSubset rights bound = true)
    (hbound : Capability.hasRuntimeCriticalRight bound = false) :
    Capability.hasRuntimeCriticalRight rights = false := by
  rcases rights with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases bound with ⟨b1, b2, b3, b4, b5, b6⟩
  simp only [Capability.rightsSubset, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    at hsubset
  simp only [Capability.hasRuntimeCriticalRight, Bool.or_eq_false_iff] at hbound ⊢
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, h6⟩ := hsubset
  obtain ⟨⟨⟨g1, g2⟩, g6⟩, g4⟩ := hbound
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · cases a1 <;> simp_all
  · cases a2 <;> simp_all
  · cases a6 <;> simp_all
  · cases a4 <;> simp_all

/-- Every recorded descendant of a capability has a subset of its rights. -/
theorem descendant_rights (state : Capability.State)
    (hderivations : Capability.DerivationsWellFormed state)
    (ancestor : Nat) (ancestorParent : Option Nat) (object : Nat)
    (kind : Capability.ObjectKind) (ancestorRights : Capability.Rights)
    (hancestor : state.derivations ancestor =
      some (ancestorParent, object, kind, ancestorRights)) :
    ∀ fuel identity, Capability.descendsFrom state identity ancestor fuel = true →
      ∀ parent identityObject identityKind rights,
        state.derivations identity = some (parent, identityObject, identityKind, rights) →
        Capability.rightsSubset rights ancestorRights = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro identity hdescends parent identityObject identityKind rights hidentity
      simp only [Capability.descendsFrom, beq_iff_eq] at hdescends
      subst hdescends
      rw [hancestor] at hidentity
      cases hidentity
      exact rightsSubset_refl _
  | succ fuel ih =>
      intro identity hdescends parent identityObject identityKind rights hidentity
      simp only [Capability.descendsFrom] at hdescends
      by_cases hsame : (identity == ancestor) = true
      · simp only [beq_iff_eq] at hsame
        subst hsame
        rw [hancestor] at hidentity
        cases hidentity
        exact rightsSubset_refl _
      · simp only [hsame, Bool.false_eq_true, ↓reduceIte] at hdescends
        rw [hidentity] at hdescends
        cases parent with
        | none => simp at hdescends
        | some parentIdentity =>
            simp only at hdescends
            obtain ⟨_, parentParent, parentRights, hparent, hsubset⟩ :=
              (hderivations identity (some parentIdentity) identityObject identityKind rights
                hidentity).2
            exact rightsSubset_trans hsubset
              (ih parentIdentity hdescends parentParent identityObject identityKind
                parentRights hparent)

/-- In a well-formed store, the runtime-safety check of a subtree revocation
is decided by the rights of the revoked capability alone. -/
theorem subtreeSafe_eq (state : Capability.State) (hstate : Capability.WellFormed state)
    (victim slot : Nat) (target : Capability.Capability)
    (hfound : Capability.lookup state victim slot = .found target) :
    Capability.subtreeRevocationRuntimeSafe state victim slot =
      !Capability.hasRuntimeCriticalRight target.rights := by
  rcases hstate with ⟨hslots, hderivations, _, _⟩
  have hslot := Capability.lookup_found_slot state victim slot target hfound
  obtain ⟨_, _, _, _, hidentity, htarget, _⟩ := hslots victim slot target hslot
  simp only [Capability.subtreeRevocationRuntimeSafe, hfound]
  cases hcritical : Capability.hasRuntimeCriticalRight target.rights with
  | true =>
      simp only [Bool.not_true, List.all_eq_false]
      refine ⟨target.identity, List.mem_range.mpr hidentity, ?_⟩
      have hself : Capability.descendsFrom state target.identity target.identity
          state.nextIdentity = true := by
        cases state.nextIdentity <;> simp [Capability.descendsFrom]
      simp [hself, htarget, hcritical]
  | false =>
      simp only [Bool.not_false, List.all_eq_true]
      intro identity _
      split
      · rename_i hdescends
        split
        · rename_i parent identityObject identityKind rights hderivation
          have hsubset := descendant_rights state hderivations target.identity target.parent
            target.object target.kind target.rights htarget state.nextIdentity identity
            hdescends parent identityObject identityKind rights hderivation
          simp [not_critical_of_subset hsubset hcritical]
        · rfl
      · rfl

theorem revokeSubtreeRuntimeSafe_self_congr (a b : Capability.State)
    (ha : Capability.WellFormed a) (hb : Capability.WellFormed b) (observer : SubjectId)
    (authoritySlot victimSlot : Nat)
    (hlookup : ∀ slot, Capability.lookup a observer slot = Capability.lookup b observer slot) :
    (Capability.revokeSubtreeRuntimeSafe a observer authoritySlot observer victimSlot).result =
      (Capability.revokeSubtreeRuntimeSafe b observer authoritySlot observer victimSlot).result := by
  have hsafe : Capability.subtreeRevocationRuntimeSafe a observer victimSlot =
      Capability.subtreeRevocationRuntimeSafe b observer victimSlot := by
    cases hfound : Capability.lookup b observer victimSlot with
    | found target =>
        rw [subtreeSafe_eq a ha observer victimSlot target ((hlookup victimSlot).trans hfound),
          subtreeSafe_eq b hb observer victimSlot target hfound]
    | invalidSubject =>
        simp [Capability.subtreeRevocationRuntimeSafe, hfound, hlookup victimSlot]
    | staleSlot =>
        simp [Capability.subtreeRevocationRuntimeSafe, hfound, hlookup victimSlot]
  simp only [Capability.revokeSubtreeRuntimeSafe, Capability.revokeSubtree,
    hlookup authoritySlot, hlookup victimSlot, hsafe]
  repeat' split
  all_goals simp_all [Capability.reject]

/-- **Output consistency of the observer's subtree revocation of its own
slot.** -/
theorem reply_revokeSubtree_self {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (authoritySlot victimSlot : Nat) :
    operationReply left (.capabilityRevokeSubtree authoritySlot observer victimSlot) =
      operationReply right (.capabilityRevokeSubtree authoritySlot observer victimSlot) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  simp only [operationReply, hLs, hRs]
  rw [revokeSubtreeRuntimeSafe_self_congr left.capabilities right.capabilities
    h.leftWF.2.2.2.1 h.rightWF.2.2.2.1 observer authoritySlot victimSlot h.lookup]

/-! ## The extended step-consistency family -/

/-- The observer's own operations for which step consistency holds once the
identity counter is public.  Not in it: `transferAccept` (`own_step_accept`
needs agreement on the carried object), the observer's own termination and
interrupts (`LeanOS.CompositeOwnTermination` proves them from the stronger
`AuthoritativeRuntimeWellFormed`), termination of another subject and subtree
revocation (channels in `LeanOS.CompositeChannels` and
`LeanOS.CompositeSwitchedChannels`), and `resumePreempt`. -/
def ownStepConsistentCounter (observer : SubjectId) : Operation → Bool
  | .capabilityCopy _ _ _ _ => true
  | .transferOffer _ _ _ _ _ => true
  | .createSubject _ => true
  | .scheduleAdd _ | .scheduleRemove _ | .scheduleNext | .scheduleYield | .scheduleTick => true
  | operation => ownStepConsistent observer operation

/-- **Step consistency for the observer's own operations, identity counter
public.** -/
theorem own_step_consistent_counter {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (operation : Operation)
    (hfamily : ownStepConsistentCounter observer operation = true) :
    LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  cases operation with
  | capabilityCopy source destination destinationSlot rights =>
      by_cases hdestination : destination = observer
      · subst hdestination
        exact lowEquiv_gate_of_apply h.low h.mode
          (own_step_copy_self h source destinationSlot rights)
      · exact own_step_consistent h.toOwnStep _
          (by simp [ownStepConsistent, hdestination])
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact lowEquiv_gate_of_apply h.low h.mode
        (own_step_offer h endpointWord sourceWord sourceKind payload rights)
  | createSubject subject =>
      by_cases hsubject : subject = observer
      · subst hsubject
        exact lowEquiv_gate_of_apply h.low h.mode (by
          rw [apply_create_self h.leftWF h.current, apply_create_self h.rightWF h.rightCurrent]
          exact h.low)
      · exact own_step_consistent h.toOwnStep _ (by simp [ownStepConsistent, hsubject])
  | scheduleAdd subject =>
      exact lowEquiv_gate_of_apply h.low h.mode (lowEquiv_of_unchanged h.low
        (observe_apply_scheduleAdd observer left subject)
        (observe_apply_scheduleAdd observer right subject))
  | scheduleRemove subject =>
      exact lowEquiv_gate_of_apply h.low h.mode (own_step_scheduleRemove h.toOwnStep subject)
  | scheduleNext =>
      exact lowEquiv_gate_of_apply h.low h.mode (by
        rw [apply_scheduleNext, apply_scheduleNext]
        exact h.low)
  | scheduleYield =>
      exact lowEquiv_gate_of_apply h.low h.mode (by
        rw [apply_scheduleYield, apply_scheduleYield]
        exact h.low)
  | scheduleTick =>
      exact lowEquiv_gate_of_apply h.low h.mode (by
        rw [apply_scheduleTick, apply_scheduleTick]
        exact h.low)
  | interrupt frame => exact own_step_consistent h.toOwnStep _ hfamily
  | nmi raw context => exact own_step_consistent h.toOwnStep _ hfamily
  | selectUserReturn purpose => exact own_step_consistent h.toOwnStep _ hfamily
  | userReturn request => exact own_step_consistent h.toOwnStep _ hfamily
  | syscall call => exact own_step_consistent h.toOwnStep _ hfamily
  | ipc call => exact own_step_consistent h.toOwnStep _ hfamily
  | resumePreempt frame registers => exact own_step_consistent h.toOwnStep _ hfamily
  | transferAccept endpointWord destinationSlot =>
      exact own_step_consistent h.toOwnStep _ hfamily
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact own_step_consistent h.toOwnStep _ hfamily
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact own_step_consistent h.toOwnStep _ hfamily
  | map slot page permissions => exact own_step_consistent h.toOwnStep _ hfamily
  | unmap page => exact own_step_consistent h.toOwnStep _ hfamily
  | protect page permissions => exact own_step_consistent h.toOwnStep _ hfamily
  | terminateSubject subject => exact own_step_consistent h.toOwnStep _ hfamily
  | terminateCurrent => exact own_step_consistent h.toOwnStep _ hfamily
  | restart => exact own_step_consistent h.toOwnStep _ hfamily

/-- **Step consistency of the observer's transfer receipt** on the gate. -/
theorem own_step_accept_gate {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (hcarried : CarriedAgree observer left right)
    (endpointWord : UInt64) (destinationSlot : Nat) :
    LowEquiv observer
      (authoritativeGate left (.ordinary (.transferAccept endpointWord destinationSlot))).state
      (authoritativeGate right (.ordinary (.transferAccept endpointWord destinationSlot))).state :=
  lowEquiv_gate_of_apply h.low h.mode (own_step_accept h hcarried endpointWord destinationSlot)

/-! ## The extended output-consistency family -/

/-- The observer's own operations for which output consistency holds once the
identity counter is public.  Creation, termination, and queue admission of
another subject, `capabilityRevoke` and `capabilityRevokeSubtree` of another
subject's slot, and delegation to another subject read state outside the view
(`LeanOS.CompositeChannels`). -/
def ownOutputConsistentCounter (observer : SubjectId) : Operation → Bool
  | .transferOffer _ _ _ _ _ | .transferAccept _ _ => true
  | .createSubject subject => subject == observer
  | .terminateSubject subject => subject == observer
  | .capabilityRevokeSubtree _ victim _ => victim == observer
  | .scheduleNext | .terminateCurrent => true
  | operation => ownOutputConsistent observer operation

theorem not_nmi_of {operation : Operation}
    (hnot : (match operation with | .nmi _ _ => false | _ => true) = true) :
    ∀ raw context, operation ≠ .nmi raw context := by
  intro raw context heq
  subst heq
  simp at hnot

/-- **Output consistency for the observer's own operations, identity counter
public.** -/
theorem own_output_consistent_counter {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (operation : Operation)
    (hfamily : ownOutputConsistentCounter observer operation = true) :
    (authoritativeGate left (.ordinary operation)).result =
      (authoritativeGate right (.ordinary operation)).result := by
  cases operation with
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
        (own_output_offer h endpointWord sourceWord sourceKind payload rights)
  | transferAccept endpointWord destinationSlot =>
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
        (own_output_accept h.toOwnStep endpointWord destinationSlot)
  | createSubject subject =>
      simp only [ownOutputConsistentCounter, beq_iff_eq] at hfamily
      subst hfamily
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode (by
        rw [reply_create_self h.leftWF h.current, reply_create_self h.rightWF h.rightCurrent])
  | scheduleNext =>
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode (by
        rw [reply_scheduleNext h.leftWF h.current, reply_scheduleNext h.rightWF h.rightCurrent])
  | terminateCurrent =>
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode (by
        rw [reply_terminateCurrent h.leftWF h.current,
          reply_terminateCurrent h.rightWF h.rightCurrent])
  | interrupt frame => exact own_output_consistent h.toOwnStep _ hfamily
  | nmi raw context => exact own_output_consistent h.toOwnStep _ hfamily
  | selectUserReturn purpose => exact own_output_consistent h.toOwnStep _ hfamily
  | userReturn request => exact own_output_consistent h.toOwnStep _ hfamily
  | syscall call => exact own_output_consistent h.toOwnStep _ hfamily
  | ipc call => exact own_output_consistent h.toOwnStep _ hfamily
  | resumePreempt frame registers => exact own_output_consistent h.toOwnStep _ hfamily
  | capabilityCopy source destination destinationSlot rights =>
      exact own_output_consistent h.toOwnStep _ hfamily
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact own_output_consistent h.toOwnStep _ hfamily
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      simp only [ownOutputConsistentCounter, beq_iff_eq] at hfamily
      subst hfamily
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
        (reply_revokeSubtree_self h.toOwnStep authoritySlot victimSlot)
  | map slot page permissions => exact own_output_consistent h.toOwnStep _ hfamily
  | unmap page => exact own_output_consistent h.toOwnStep _ hfamily
  | protect page permissions => exact own_output_consistent h.toOwnStep _ hfamily
  | terminateSubject subject =>
      simp only [ownOutputConsistentCounter, beq_iff_eq] at hfamily
      subst hfamily
      exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode (by
        rw [reply_terminate_self h.leftWF h.current, reply_terminate_self h.rightWF h.rightCurrent])
  | scheduleAdd subject => exact own_output_consistent h.toOwnStep _ hfamily
  | scheduleRemove subject => exact own_output_consistent h.toOwnStep _ hfamily
  | scheduleYield => exact own_output_consistent h.toOwnStep _ hfamily
  | scheduleTick => exact own_output_consistent h.toOwnStep _ hfamily
  | restart => exact own_output_consistent h.toOwnStep _ hfamily

/-- The scheduler operations whose output is consistent once the scheduler
state is a public input. -/
def schedulerOutputConsistent : Operation → Bool
  | .scheduleYield | .scheduleTick | .scheduleRemove _ => true
  | _ => false

/-- **Output consistency of the observer's scheduler operations**, with the
ready queue and its capacity public (the scheduler's choice as a public
input). -/
theorem own_output_consistent_scheduler {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (hpublic : SchedulerPublic left right)
    (operation : Operation) (hfamily : schedulerOutputConsistent operation = true) :
    (authoritativeGate left (.ordinary operation)).result =
      (authoritativeGate right (.ordinary operation)).result := by
  cases operation <;> simp only [schedulerOutputConsistent] at hfamily <;>
    first
      | exact absurd hfamily (by decide)
      | exact authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
          (own_output_scheduler h hpublic _ rfl)

/-! ## Classical noninterference for the observer's own runs, extended -/

/-- Operations that are both step and output consistent once the identity
counter is public. -/
def ownTraceFamilyCounter (observer : SubjectId) (operation : Operation) : Bool :=
  ownStepConsistentCounter observer operation && ownOutputConsistentCounter observer operation

theorem revokeRuntimeSafe_nextIdentity (capabilities : Capability.State) actor authoritySlot
    victim victimSlot :
    (Capability.revokeRuntimeSafe capabilities actor authoritySlot victim
      victimSlot).state.nextIdentity = capabilities.nextIdentity := by
  simp only [Capability.revokeRuntimeSafe, Capability.revoke]
  repeat' split
  all_goals simp_all [Capability.reject, Capability.clear]

/-- The operations of `ownTraceFamily` never issue an identity. -/
theorem apply_nextIdentity_of_ownTraceFamily (observer : SubjectId) (state : CompositeState)
    (operation : Operation) (hfamily : ownTraceFamily observer operation = true) :
    (applyOperation state operation).capabilities.nextIdentity =
      state.capabilities.nextIdentity := by
  cases operation with
  | ipc call =>
      simp only [applyOperation]
      cases call with
      | send handleWord word0 word1 => split <;> rfl
      | receive handleWord =>
          simp only [dispatchIPC]
          repeat' split
          all_goals rfl
  | map slot page permissions =>
      simp only [applyOperation]
      split <;> rfl
  | unmap page =>
      simp only [applyOperation]
      split <;> rfl
  | protect page permissions =>
      simp only [applyOperation]
      split <;> rfl
  | syscall call =>
      simp only [applyOperation]
      split
      · rfl
      · split <;> (unfold selectLiveReturnAuthority; split <;> rfl)
  | capabilityRevoke authoritySlot victim victimSlot =>
      simp only [applyOperation]
      split
      · rfl
      · exact revokeRuntimeSafe_nextIdentity _ _ _ _ _
  | restart => rfl
  | _ => simp [ownTraceFamily, ownStepConsistent, ownOutputConsistent] at hfamily

theorem copy_self_counter {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (source destinationSlot : Nat)
    (rights : Capability.Rights) :
    (applyOperation left (.capabilityCopy source observer destinationSlot
        rights)).capabilities.nextIdentity =
      (applyOperation right (.capabilityCopy source observer destinationSlot
        rights)).capabilities.nextIdentity := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  have hresult := copy_self_congr left.capabilities right.capabilities observer source
    destinationSlot rights h.lookup h.low.live h.low.capacity
    (fun slot hslot => (h.low.slot slot (h.low.capacity ▸ hslot)).1)
  have hL := copy_nextIdentity left.capabilities observer source observer destinationSlot rights
  have hR := copy_nextIdentity right.capabilities observer source observer destinationSlot
    rights
  simp only [applyOperation, hLs, hRs]
  rw [hresult] at hL ⊢
  cases hres : (Capability.copy right.capabilities observer source observer destinationSlot
      rights).result with
  | rejected reason => exact h.counter
  | accepted =>
      simp only [hres] at hL hR
      simp only [installCopiedCapabilities, hL, hR, h.counter]

/-- The operations of `ownTraceFamilyCounter` keep the scheduled subject and
the fail-stop mode. -/
theorem ownTraceFamilyCounter_preserves (observer : SubjectId) (state : CompositeState)
    (operation : Operation) (hfamily : ownTraceFamilyCounter observer operation = true)
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    (authoritativeGate state (.ordinary operation)).state.lifecycle.current =
        state.lifecycle.current ∧
      (authoritativeGate state (.ordinary operation)).state.execution.mode =
        state.execution.mode := by
  by_cases hold : ownTraceFamily observer operation = true
  · exact ownTraceFamily_preserves observer state operation hold
  rw [authoritativeGate_ordinary_state]
  rcases gate_state_cases state operation with hsame | happly
  · rw [hsame]
    exact ⟨rfl, rfl⟩
  rw [happly]
  simp only [ownTraceFamilyCounter, Bool.and_eq_true] at hfamily
  cases operation with
  | capabilityCopy source destination destinationSlot rights =>
      simp only [applyOperation]
      split <;> simp [installCopiedCapabilities]
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      rw [applyOperation_transferOffer]
      split <;> simp [installTransfers]
  | createSubject subject =>
      simp only [ownOutputConsistentCounter, beq_iff_eq] at hfamily
      rw [hfamily.2, apply_create_self hstate hcurrent]
      exact ⟨rfl, rfl⟩
  | scheduleNext =>
      rw [apply_scheduleNext]
      exact ⟨rfl, rfl⟩
  | _ => simp_all [ownTraceFamily, ownStepConsistentCounter, ownOutputConsistentCounter,
      ownStepConsistent, ownOutputConsistent]

/-- The operations of `ownTraceFamilyCounter` keep the two counters equal. -/
theorem ownTraceFamilyCounter_counter {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (operation : Operation)
    (hfamily : ownTraceFamilyCounter observer operation = true) :
    (authoritativeGate left (.ordinary operation)).state.capabilities.nextIdentity =
      (authoritativeGate right (.ordinary operation)).state.capabilities.nextIdentity := by
  rw [authoritativeGate_ordinary_state, authoritativeGate_ordinary_state]
  rcases gate_state_pair left right operation h.mode with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
    exact h.counter
  rw [hl, hr]
  by_cases hold : ownTraceFamily observer operation = true
  · rw [apply_nextIdentity_of_ownTraceFamily observer left operation hold,
      apply_nextIdentity_of_ownTraceFamily observer right operation hold]
    exact h.counter
  simp only [ownTraceFamilyCounter, Bool.and_eq_true] at hfamily
  cases operation with
  | capabilityCopy source destination destinationSlot rights =>
      simp only [ownOutputConsistentCounter, ownOutputConsistent, beq_iff_eq] at hfamily
      rw [hfamily.2]
      exact copy_self_counter h source destinationSlot rights
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact nextIdentity_transferOffer h endpointWord sourceWord sourceKind payload rights
  | createSubject subject =>
      simp only [ownOutputConsistentCounter, beq_iff_eq] at hfamily
      rw [hfamily.2, apply_create_self h.leftWF h.current,
        apply_create_self h.rightWF h.rightCurrent]
      exact h.counter
  | scheduleNext =>
      rw [apply_scheduleNext, apply_scheduleNext]
      exact h.counter
  | _ => simp_all [ownTraceFamily, ownStepConsistentCounter, ownOutputConsistentCounter,
      ownStepConsistent, ownOutputConsistent]

/-- One gate step of `ownTraceFamilyCounter` keeps the `OwnStepCounter`
premises. -/
theorem OwnStepCounter.next {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (operation : Operation)
    (hfamily : ownTraceFamilyCounter observer operation = true) :
    OwnStepCounter observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  have hstep : ownStepConsistentCounter observer operation = true := by
    simp only [ownTraceFamilyCounter, Bool.and_eq_true] at hfamily
    exact hfamily.1
  have hleft := ownTraceFamilyCounter_preserves observer left operation hfamily h.leftWF
    h.current
  have hright := ownTraceFamilyCounter_preserves observer right operation hfamily h.rightWF
    h.rightCurrent
  exact
    { low := own_step_consistent_counter h operation hstep
      leftWF := authoritativeGate_preserves_runtimeWellFormed left _ h.leftWF trivial
      rightWF := authoritativeGate_preserves_runtimeWellFormed right _ h.rightWF trivial
      current := hleft.1.trans h.current
      mode := hleft.2.trans (h.mode.trans hright.2.symm)
      counter := ownTraceFamilyCounter_counter h operation hfamily }

/-- **Noninterference for the observer's own runs, identity counter public.**
From two runtime-well-formed states low-equivalent for the scheduled observer,
with the same fail-stop mode and identity counter, the same finite run of the
observer's operations in `ownTraceFamilyCounter` (which adds its own
delegations, transfer offers, creation of itself, and `scheduleNext` to
`ownTraceFamily`) returns the same gate result at every step and ends in
low-equivalent states. -/
theorem own_run_noninterference_counter {observer : SubjectId} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (operations : List Operation)
    (hfamily : ∀ operation, operation ∈ operations →
      ownTraceFamilyCounter observer operation = true) :
    (ownRun left operations).2 = (ownRun right operations).2 ∧
      LowEquiv observer (ownRun left operations).1 (ownRun right operations).1 := by
  induction operations generalizing left right with
  | nil => exact ⟨rfl, h.low⟩
  | cons operation rest ih =>
      have hhead := hfamily operation (by simp)
      have htail := ih (h.next operation hhead) fun candidate hmem =>
        hfamily candidate (by simp [hmem])
      simp only [ownTraceFamilyCounter, Bool.and_eq_true] at hhead
      refine ⟨?_, htail.2⟩
      simp only [ownRun, List.cons.injEq]
      exact ⟨own_output_consistent_counter h operation hhead.2, htail.1⟩

end LeanOS.CompositeOwnSteps
