import LeanOS.CompositeFullView

/-!
# The observer's own steps on the full view

Delegation into its own row, the transfer offer, transfer receipt, subtree
revocation of its own capability, and its own termination change what the
full view (`LeanOS.CompositeFullView`) adds beyond `observe`.  This module
proves that they change it the same way in both runs.
-/
namespace LeanOS.CompositeFullSteps

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeFullView
set_option linter.unusedSimpArgs false

/-! ## Lineage facts -/

/-- A recorded parent edge extends the lineage by one identity. -/
theorem lineage_of_parent (capabilities : Capability.State)
    (hprecede : ParentsPrecede capabilities) (identity parent : Nat) object kind rights
    (hderivation : capabilities.derivations identity = some (some parent, object, kind, rights)) :
    lineage capabilities identity = identity :: lineage capabilities parent := by
  have hlt := hprecede identity parent object kind rights hderivation
  obtain ⟨fuel, rfl⟩ : ∃ fuel, identity = fuel + 1 := ⟨identity - 1, by omega⟩
  simp only [lineage, chain, hderivation]
  rw [chain_stable capabilities hprecede parent fuel (by omega)]

theorem mem_row_of_lookup {state : CompositeState} {observer slot : Nat}
    {cap : Capability.Capability}
    (hfound : Capability.lookup state.capabilities observer slot = .found cap) :
    some cap ∈ row state observer := by
  obtain ⟨hin, hslot⟩ := lookup_found_inRange _ _ _ _ hfound
  rw [List.mem_iff_getElem?]
  exact ⟨slot, by rw [row_getElem? state observer slot hin, hslot]⟩

/-! ## Delegation into the observer's own row -/

/-- The store after an accepted delegation of `cap` into `destinationSlot`. -/
def copied (a : Capability.State) (subject destinationSlot : Nat) (cap : Capability.Capability)
    (rights : Capability.Rights) : Capability.State :=
  Capability.install
    { a with
      nextIdentity := a.nextIdentity + 1
      derivations := fun identity =>
        if identity = a.nextIdentity then
          some (some cap.identity, cap.object, cap.kind, rights)
        else a.derivations identity }
    subject destinationSlot
    { identity := a.nextIdentity, parent := some cap.identity,
      object := cap.object, kind := cap.kind, rights := rights }

theorem copied_extends (a : Capability.State) subject destinationSlot cap rights :
    ∀ index, index < a.nextIdentity →
      (copied a subject destinationSlot cap rights).derivations index = a.derivations index := by
  intro index hindex
  have hne : index ≠ a.nextIdentity := Nat.ne_of_lt hindex
  simp [copied, Capability.install, hne]

theorem copied_lineage (a : Capability.State) (hprecede : ParentsPrecede a) subject
    destinationSlot cap rights (identity : Nat) (hissued : identity < a.nextIdentity) :
    lineage (copied a subject destinationSlot cap rights) identity = lineage a identity :=
  lineage_of_extends _ _ hprecede (copied_extends a subject destinationSlot cap rights)
    identity hissued

theorem copied_fresh_lineage (a : Capability.State) subject destinationSlot cap rights
    (hprecede : ParentsPrecede (copied a subject destinationSlot cap rights))
    (hprecedeA : ParentsPrecede a) (hissued : cap.identity < a.nextIdentity) :
    lineage (copied a subject destinationSlot cap rights) a.nextIdentity =
      a.nextIdentity :: lineage a cap.identity := by
  rw [lineage_of_parent _ hprecede a.nextIdentity cap.identity cap.object cap.kind rights
    (by simp [copied, Capability.install]),
    copied_lineage a hprecedeA subject destinationSlot cap rights _ hissued]

theorem mem_row_copied {state : CompositeState} {observer destinationSlot : Nat}
    {source : Capability.Capability} {rights : Capability.Rights}
    {cap : Capability.Capability}
    (hmem : some cap ∈ Capability.capabilitySpace
      (copied state.capabilities observer destinationSlot source rights) observer) :
    cap = (⟨source.object, source.kind, rights, state.capabilities.nextIdentity,
      some source.identity⟩ : Capability.Capability) ∨
      some cap ∈ row state observer := by
  simp only [Capability.capabilitySpace, copied, Capability.install, List.mem_map,
    List.mem_range] at hmem
  obtain ⟨slot, hrange, hslot⟩ := hmem
  by_cases hdest : slot = destinationSlot
  · simp only [hdest, and_self, ↓reduceIte, Option.some.injEq] at hslot
    exact Or.inl hslot.symm
  · simp only [hdest, and_false, ↓reduceIte] at hslot
    right
    simp only [CompositeObservation.row, Capability.capabilitySpace, List.mem_map,
      List.mem_range]
    exact ⟨slot, hrange, hslot⟩

/-- **The observer's delegation into its own row keeps the authority in
agreement.**  The new capability's lineage is the source's, extended by the
public identity counter. -/
theorem agree_copy_self {observer : Nat} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (hagree : ExtraAgree observer left right)
    (hissuedL : Issued left) (hissuedR : Issued right)
    (source destinationSlot : Nat) (rights : Capability.Rights)
    (hprecedeL : ParentsPrecede (applyOperation left
      (.capabilityCopy source observer destinationSlot rights)).capabilities)
    (hprecedeR : ParentsPrecede (applyOperation right
      (.capabilityCopy source observer destinationSlot rights)).capabilities) :
    ExtraAgree observer
      (applyOperation left (.capabilityCopy source observer destinationSlot rights))
      (applyOperation right (.capabilityCopy source observer destinationSlot rights)) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  have hresult := copy_self_congr left.capabilities right.capabilities observer source
    destinationSlot rights h.lookup h.low.live h.low.capacity
    (fun slot hslot => (h.low.slot slot (h.low.capacity ▸ hslot)).1)
  simp only [applyOperation, hLs, hRs] at hprecedeL hprecedeR ⊢
  rw [hresult] at hprecedeL ⊢
  cases hres : (Capability.copy right.capabilities observer source observer destinationSlot
      rights).result with
  | rejected reason =>
      simp only [hres]
      exact hagree
  | accepted =>
      simp only [hres] at hprecedeL hprecedeR ⊢
      obtain ⟨capL, hfoundL, hstateL⟩ := copy_accepted_state _ _ _ _ _ _ (hresult.trans hres)
      obtain ⟨capR, hfoundR, hstateR⟩ := copy_accepted_state _ _ _ _ _ _ hres
      have hcap : capL = capR := by
        rw [h.lookup source, hfoundR] at hfoundL
        cases hfoundL
        rfl
      subst hcap
      obtain ⟨_, _, hobjL, hkindL⟩ := copy_frame_self left.capabilities observer source
        observer destinationSlot rights
      obtain ⟨_, _, hobjR, hkindR⟩ := copy_frame_self right.capabilities observer source
        observer destinationSlot rights
      rw [show (Capability.copy left.capabilities observer source observer destinationSlot
          rights).state = copied left.capabilities observer destinationSlot capL rights
          from hstateL] at hprecedeL hobjL hkindL ⊢
      rw [show (Capability.copy right.capabilities observer source observer destinationSlot
          rights).state = copied right.capabilities observer destinationSlot capL rights
          from hstateR] at hprecedeR hobjR hkindR ⊢
      have hsourceMem : some capL ∈ row left observer := mem_row_of_lookup hfoundL
      have hsourceIssuedL := hissuedL.row hsourceMem
      have hsourceIssuedR := hissuedR.row (h.low.rowEq ▸ hsourceMem)
      have hviewL : ∀ object, objectView (installCopiedCapabilities left
          (copied left.capabilities observer destinationSlot capL rights)) object =
          objectView left object := by
        intro object
        rw [objectView_installCopiedCapabilities, hobjL, hkindL]; rfl
      have hviewR : ∀ object, objectView (installCopiedCapabilities right
          (copied right.capabilities observer destinationSlot capL rights)) object =
          objectView right object := by
        intro object
        rw [objectView_installCopiedCapabilities, hobjR, hkindR]; rfl
      constructor
      · intro cap hmem
        rcases mem_row_copied hmem with rfl | hold
        · show lineage (copied left.capabilities observer destinationSlot capL rights)
              left.capabilities.nextIdentity =
            lineage (copied right.capabilities observer destinationSlot capL rights)
              left.capabilities.nextIdentity
          rw [copied_fresh_lineage _ _ _ _ _ hprecedeL hissuedL.precede hsourceIssuedL,
            h.counter,
            copied_fresh_lineage _ _ _ _ _ hprecedeR hissuedR.precede hsourceIssuedR,
            hagree.rows capL hsourceMem]
        · show lineage (copied left.capabilities observer destinationSlot capL rights)
              cap.identity =
            lineage (copied right.capabilities observer destinationSlot capL rights) cap.identity
          rw [copied_lineage _ hissuedL.precede _ _ _ _ _ (hissuedL.row hold),
            copied_lineage _ hissuedR.precede _ _ _ _ _ (hissuedR.row (h.low.rowEq ▸ hold)),
            hagree.rows cap hold]
      · intro cap transfer hmem hpending
        have hnamed : Names left observer cap.object = true := by
          rcases mem_row_copied hmem with rfl | hold
          · show Names left observer capL.object = true
            exact names_of_mem hsourceMem
          · exact names_of_mem hold
        change left.transfers.pending cap.object = some transfer at hpending
        obtain ⟨hlineage, hview, hnested⟩ := hagree.named hnamed hpending
        have hpendingR : right.transfers.pending cap.object = some transfer := by
          rw [← pending_of_view (h.low.namedView cap.object hnamed)]
          exact hpending
        have htL := hissuedL.pending _ _ hpending
        have htR := hissuedR.pending _ _ hpendingR
        refine ⟨?_, ?_, ?_⟩
        · show lineage (copied left.capabilities observer destinationSlot capL rights)
              transfer.identity =
            lineage (copied right.capabilities observer destinationSlot capL rights)
              transfer.identity
          rw [copied_lineage _ hissuedL.precede _ _ _ _ _ htL,
            copied_lineage _ hissuedR.precede _ _ _ _ _ htR, hlineage]
        · rw [hviewL, hviewR]; exact hview
        · intro nested hnestedL
          change left.transfers.pending transfer.object = some nested at hnestedL
          have hnestedR : right.transfers.pending transfer.object = some nested := by
            have := congrArg ObjectView.sealed hview
            simp only [objectView] at this
            rw [← this]; exact hnestedL
          show lineage (copied left.capabilities observer destinationSlot capL rights)
              nested.identity =
            lineage (copied right.capabilities observer destinationSlot capL rights)
              nested.identity
          rw [copied_lineage _ hissuedL.precede _ _ _ _ _ (hissuedL.pending _ _ hnestedL),
            copied_lineage _ hissuedR.precede _ _ _ _ _ (hissuedR.pending _ _ hnestedR),
            hnested nested hnestedL]

/-! ## The transfer offer -/

theorem offerCheck_found (a : CapabilityTransfer.State) caller endpointSlot sourceSlot
    (rights : Capability.Rights) endpointCap source
    (hcheck : offerCheck a caller endpointSlot sourceSlot rights = .ok (endpointCap, source)) :
    Capability.lookup a.capabilities caller endpointSlot = .found endpointCap ∧
      Capability.lookup a.capabilities caller sourceSlot = .found source := by
  unfold offerCheck at hcheck
  split at hcheck
  · cases hcheck
  · cases hcheck
  · rename_i found hfound
    repeat' split at hcheck
    all_goals first | (cases hcheck; done) | skip
    rename_i src hsrc _ _ _
    simp only [Except.ok.injEq, Prod.mk.injEq] at hcheck
    obtain ⟨rfl, rfl⟩ := hcheck
    exact ⟨hfound, hsrc⟩

theorem offerWordsCheck_found (a : CapabilityTransfer.State) caller endpointWord sourceWord
    sourceKind (rights : Capability.Rights) endpointCap source
    (hcheck : offerWordsCheck a caller endpointWord sourceWord sourceKind rights =
      .ok (endpointCap, source)) :
    ∃ endpointSlot sourceSlot,
      Capability.lookup a.capabilities caller endpointSlot = .found endpointCap ∧
        Capability.lookup a.capabilities caller sourceSlot = .found source := by
  unfold offerWordsCheck at hcheck
  split at hcheck
  · cases hcheck
  · cases hcheck
  · cases hcheck
  · split at hcheck
    · cases hcheck
    · cases hcheck
    · split at hcheck
      · cases hcheck
      · exact ⟨_, _, offerCheck_found _ _ _ _ _ _ _ hcheck⟩

/-- The sealed transfer an accepted offer records. -/
def offered (identity : Nat) (caller : Nat) (source : Capability.Capability)
    (rights : Capability.Rights) : CapabilityTransfer.Sealed :=
  ⟨identity, source.identity, caller, source.object, source.kind, rights⟩

theorem offerAccepted_pending (state : CapabilityTransfer.State) caller endpointCap source
    payload (rights : Capability.Rights) (object : Nat) :
    (offerAccepted state caller endpointCap source payload rights).pending object =
      if object = endpointCap.object then
        some (offered state.capabilities.nextIdentity caller source rights)
      else state.pending object := by
  simp only [offerAccepted, CapabilityTransfer.record, CapabilityTransfer.setPending, offered]

theorem offerAccepted_mailbox_other (state : CapabilityTransfer.State) caller endpointCap source
    payload (rights : Capability.Rights) (object : Nat) (hne : object ≠ endpointCap.object) :
    (offerAccepted state caller endpointCap source payload rights).mailbox object =
      state.mailbox object := by
  simp [offerAccepted, CapabilityTransfer.record, EndpointIPC.setOption, hne]

theorem offerAccepted_extends (state : CapabilityTransfer.State) caller endpointCap source
    payload (rights : Capability.Rights) :
    ∀ index, index < state.capabilities.nextIdentity →
      (offerAccepted state caller endpointCap source payload rights).capabilities.derivations
        index = state.capabilities.derivations index := by
  intro index hindex
  have hne : index ≠ state.capabilities.nextIdentity := Nat.ne_of_lt hindex
  simp [offerAccepted, CapabilityTransfer.record, hne]

theorem offerAccepted_fresh (state : CapabilityTransfer.State) caller endpointCap source
    payload (rights : Capability.Rights) :
    (offerAccepted state caller endpointCap source payload rights).capabilities.derivations
        state.capabilities.nextIdentity =
      some (some source.identity, source.object, source.kind, rights) := by
  simp [offerAccepted, CapabilityTransfer.record]

/-- Lineages of identities issued before a step that only extends the
derivation history agree afterwards when they agreed before. -/
theorem lineage_after {left right left' right' : CompositeState}
    (hissuedL : Issued left) (hissuedR : Issued right)
    (hextL : ∀ index, index < left.capabilities.nextIdentity →
      left'.capabilities.derivations index = left.capabilities.derivations index)
    (hextR : ∀ index, index < right.capabilities.nextIdentity →
      right'.capabilities.derivations index = right.capabilities.derivations index)
    (identity : Nat) (hltL : identity < left.capabilities.nextIdentity)
    (hltR : identity < right.capabilities.nextIdentity)
    (hagree : lineage left.capabilities identity = lineage right.capabilities identity) :
    lineage left'.capabilities identity = lineage right'.capabilities identity := by
  rw [lineage_of_extends _ _ hissuedL.precede hextL identity hltL,
    lineage_of_extends _ _ hissuedR.precede hextR identity hltR, hagree]

/-- **The observer's transfer offer keeps the authority in agreement.**  The
offered transfer's lineage is the source's, extended by the public counter. -/
theorem agree_offer {observer : Nat} {left right : CompositeState}
    (h : OwnStepCounter observer left right) (hagree : ExtraAgree observer left right)
    (hissuedL : Issued left) (hissuedR : Issued right)
    (endpointWord sourceWord : UInt64) (sourceKind : Capability.ObjectKind)
    (payload : EndpointIPC.Payload) (rights : Capability.Rights)
    (hprecedeL : ParentsPrecede (applyOperation left
      (.transferOffer endpointWord sourceWord sourceKind payload rights)).capabilities)
    (hprecedeR : ParentsPrecede (applyOperation right
      (.transferOffer endpointWord sourceWord sourceKind payload rights)).capabilities)
    (hlow' : LowEquiv observer
      (applyOperation left (.transferOffer endpointWord sourceWord sourceKind payload rights))
      (applyOperation right (.transferOffer endpointWord sourceWord sourceKind payload rights))) :
    ExtraAgree observer
      (applyOperation left (.transferOffer endpointWord sourceWord sourceKind payload rights))
      (applyOperation right (.transferOffer endpointWord sourceWord sourceKind payload rights)) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  have hcongr := offerWordsCheck_congr _ _ observer (ownStep_callerInputs h.toOwnStep)
    h.transferCounter endpointWord sourceWord sourceKind rights
  simp only [applyOperation_transferOffer, hLs, hRs, hcongr]
    at hprecedeL hprecedeR hlow' ⊢
  cases hcheck : offerWordsCheck right.transfers observer endpointWord sourceWord sourceKind
      rights with
  | error reason =>
      simp only [hcheck]
      exact hagree
  | ok caps =>
      obtain ⟨endpointCap, source⟩ := caps
      simp only [hcheck] at hprecedeL hprecedeR hlow' ⊢
      obtain ⟨endpointSlot, sourceSlot, hendpointR, hsourceR⟩ :=
        offerWordsCheck_found _ _ _ _ _ _ _ _ hcheck
      have hcapsL := (transfers_published h.leftWF.1).1
      have hcapsR := (transfers_published h.rightWF.1).1
      have hmailboxL := (transfers_published h.leftWF.1).2
      have hmailboxR := (transfers_published h.rightWF.1).2
      rw [hcapsR] at hendpointR hsourceR
      have hendpointL : Capability.lookup left.capabilities observer endpointSlot =
          .found endpointCap := (h.lookup endpointSlot).trans hendpointR
      have hsourceL : Capability.lookup left.capabilities observer sourceSlot =
          .found source := (h.lookup sourceSlot).trans hsourceR
      have hsourceMem : some source ∈ row left observer := mem_row_of_lookup hsourceL
      have hendpointNamed : Names left observer endpointCap.object = true :=
        names_of_mem (mem_row_of_lookup hendpointL)
      have hsourceNamed : Names left observer source.object = true := names_of_mem hsourceMem
      -- The published stores.
      generalize hnL : offerAccepted left.transfers observer endpointCap source payload rights = nextL at hprecedeL hlow' ⊢
      generalize hnR : offerAccepted right.transfers observer endpointCap source payload rights = nextR at hprecedeR hlow' ⊢
      have hcounter : left.transfers.capabilities.nextIdentity =
          right.transfers.capabilities.nextIdentity := h.transferCounter
      have hextL : ∀ index, index < left.capabilities.nextIdentity →
          (installTransfers left nextL).capabilities.derivations index =
            left.capabilities.derivations index := by
        intro index hindex
        show nextL.capabilities.derivations index = _
        rw [← hnL]
        rw [offerAccepted_extends _ _ _ _ _ _ index (by rw [hcapsL]; exact hindex), hcapsL]
      have hextR : ∀ index, index < right.capabilities.nextIdentity →
          (installTransfers right nextR).capabilities.derivations index =
            right.capabilities.derivations index := by
        intro index hindex
        show nextR.capabilities.derivations index = _
        rw [← hnR]
        rw [offerAccepted_extends _ _ _ _ _ _ index (by rw [hcapsR]; exact hindex), hcapsR]
      have hsealedL : (installTransfers left nextL).transfers.pending =
          fun object => if object = endpointCap.object then
            some (offered left.capabilities.nextIdentity observer source rights)
          else left.transfers.pending object := by
        funext object
        show nextL.pending object = _
        rw [← hnL]
        rw [offerAccepted_pending, hcapsL]
      have hsealedR : (installTransfers right nextR).transfers.pending =
          fun object => if object = endpointCap.object then
            some (offered left.capabilities.nextIdentity observer source rights)
          else right.transfers.pending object := by
        funext object
        show nextR.pending object = _
        rw [← hnR]
        rw [offerAccepted_pending, hcapsR, ← h.counter]
      have hrowL : row (installTransfers left nextL) observer = row left observer := by
        rw [← hnL]
        simp only [CompositeObservation.row, Capability.capabilitySpace, installTransfers,
          offerAccepted, CapabilityTransfer.record, hcapsL]
      have hviewL : ∀ object, object ≠ endpointCap.object →
          objectView (installTransfers left nextL) object = objectView left object := by
        intro object hne
        have hmail := offerAccepted_mailbox_other left.transfers observer endpointCap source
          payload rights object hne
        rw [hmailboxL, hnL] at hmail
        have hpend : nextL.pending object = left.transfers.pending object := by
          rw [← hnL, offerAccepted_pending]; simp [hne]
        have hobj : nextL.capabilities.objects = left.capabilities.objects := by
          rw [← hnL]; simp [offerAccepted, CapabilityTransfer.record, hcapsL]
        have hkind : nextL.capabilities.kinds = left.capabilities.kinds := by
          rw [← hnL]; simp [offerAccepted, CapabilityTransfer.record, hcapsL]
        simp only [objectView, backing, installTransfers, hmail, hpend, hobj, hkind]
        rfl
      have hviewR : ∀ object, object ≠ endpointCap.object →
          objectView (installTransfers right nextR) object = objectView right object := by
        intro object hne
        have hmail := offerAccepted_mailbox_other right.transfers observer endpointCap source
          payload rights object hne
        rw [hmailboxR, hnR] at hmail
        have hpend : nextR.pending object = right.transfers.pending object := by
          rw [← hnR, offerAccepted_pending]; simp [hne]
        have hobj : nextR.capabilities.objects = right.capabilities.objects := by
          rw [← hnR]; simp [offerAccepted, CapabilityTransfer.record, hcapsR]
        have hkind : nextR.capabilities.kinds = right.capabilities.kinds := by
          rw [← hnR]; simp [offerAccepted, CapabilityTransfer.record, hcapsR]
        simp only [objectView, backing, installTransfers, hmail, hpend, hobj, hkind]
        rfl
      have hsourceIssuedL := hissuedL.row hsourceMem
      have hsourceIssuedR := hissuedR.row (h.low.rowEq ▸ hsourceMem)
      -- The offered transfer's lineage.
      have hoffered : lineage (installTransfers left nextL).capabilities
            left.capabilities.nextIdentity =
          lineage (installTransfers right nextR).capabilities left.capabilities.nextIdentity := by
        have hfreshL : (installTransfers left nextL).capabilities.derivations
            left.capabilities.nextIdentity =
            some (some source.identity, source.object, source.kind, rights) := by
          show nextL.capabilities.derivations _ = _
          rw [← hnL]
          rw [← hcapsL]; exact offerAccepted_fresh _ _ _ _ _ _
        have hfreshR : (installTransfers right nextR).capabilities.derivations
            left.capabilities.nextIdentity =
            some (some source.identity, source.object, source.kind, rights) := by
          show nextR.capabilities.derivations _ = _
          rw [← hnR]
          rw [h.counter, ← hcapsR]; exact offerAccepted_fresh _ _ _ _ _ _
        rw [lineage_of_parent _ hprecedeL _ _ _ _ _ hfreshL,
          lineage_of_parent _ hprecedeR _ _ _ _ _ hfreshR,
          lineage_after hissuedL hissuedR hextL hextR source.identity hsourceIssuedL
            hsourceIssuedR (hagree.rows source hsourceMem)]
      -- Every transfer pending afterwards on a named or carried object is
      -- either the offered one or was pending before.
      have hpendingFact : ∀ object, Names left observer object = true →
          ∀ transfer, (installTransfers left nextL).transfers.pending object = some transfer →
            lineage (installTransfers left nextL).capabilities transfer.identity =
              lineage (installTransfers right nextR).capabilities transfer.identity := by
        intro object hnamed transfer hpending
        rw [hsealedL] at hpending
        by_cases hobject : object = endpointCap.object
        · simp only [hobject, ↓reduceIte, Option.some.injEq] at hpending
          subst hpending
          exact hoffered
        · simp only [hobject, ↓reduceIte] at hpending
          obtain ⟨hlineage, _, _⟩ := hagree.named hnamed hpending
          have hpendingR : right.transfers.pending object = some transfer := by
            rw [← pending_of_view (h.low.namedView object hnamed)]; exact hpending
          exact lineage_after hissuedL hissuedR hextL hextR _
            (hissuedL.pending _ _ hpending) (hissuedR.pending _ _ hpendingR) hlineage
      constructor
      · intro cap hmem
        rw [hrowL] at hmem
        exact lineage_after hissuedL hissuedR hextL hextR _ (hissuedL.row hmem)
          (hissuedR.row (h.low.rowEq ▸ hmem)) (hagree.rows cap hmem)
      · intro cap transfer hmem hpending
        rw [hrowL] at hmem
        have hnamed := names_of_mem hmem
        refine ⟨hpendingFact cap.object hnamed transfer hpending, ?_, ?_⟩
        · -- The carried object's view.
          rw [hsealedL] at hpending
          by_cases hcarried : transfer.object = endpointCap.object
          · rw [hcarried]
            apply hlow'.namedView
            rw [names_eq_of_capabilities (show (installTransfers left nextL).capabilities =
              _ from rfl)]
            simp only [Names, CompositeObservation.row, installTransfers, ← hnL, offerAccepted,
              CapabilityTransfer.record, hcapsL] at hendpointNamed ⊢
            exact hendpointNamed
          · rw [hviewL _ hcarried, hviewR _ hcarried]
            by_cases hobject : cap.object = endpointCap.object
            · simp only [hobject, ↓reduceIte, Option.some.injEq] at hpending
              subst hpending
              exact h.low.namedView _ hsourceNamed
            · simp only [hobject, ↓reduceIte] at hpending
              exact (hagree.carried cap transfer hmem hpending).2.1
        · intro nested hnested
          rw [hsealedL] at hpending hnested
          by_cases hcarried : transfer.object = endpointCap.object
          · simp only [hcarried, ↓reduceIte, Option.some.injEq] at hnested
            subst hnested
            exact hoffered
          · simp only [hcarried, ↓reduceIte] at hnested
            have hlineage : lineage left.capabilities nested.identity =
                lineage right.capabilities nested.identity := by
              by_cases hobject : cap.object = endpointCap.object
              · simp only [hobject, ↓reduceIte, Option.some.injEq] at hpending
                subst hpending
                exact (hagree.named hsourceNamed hnested).1
              · simp only [hobject, ↓reduceIte] at hpending
                exact (hagree.carried cap transfer hmem hpending).2.2 nested hnested
            have hview : objectView left transfer.object = objectView right transfer.object := by
              by_cases hobject : cap.object = endpointCap.object
              · simp only [hobject, ↓reduceIte, Option.some.injEq] at hpending
                subst hpending
                exact h.low.namedView _ hsourceNamed
              · simp only [hobject, ↓reduceIte] at hpending
                exact (hagree.carried cap transfer hmem hpending).2.1
            have hnestedR : right.transfers.pending transfer.object = some nested := by
              rw [← pending_of_view hview]; exact hnested
            exact lineage_after hissuedL hissuedR hextL hextR _
              (hissuedL.pending _ _ hnested) (hissuedR.pending _ _ hnestedR) hlineage

/-! ## Transfer receipt -/

/-- The subject gate lets receipt through only when the carried object is
the endpoint itself or has no transfer of its own pending. -/
def NestedFree (state : CompositeState) (endpointWord : UInt64) : Prop :=
  ∀ resolution, CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject } endpointWord .endpoint =
      .ok resolution →
    ∀ transfer, state.transfers.pending resolution.capability.object = some transfer →
      transfer.object ≠ resolution.capability.object →
      state.transfers.pending transfer.object = none

theorem nestedFree_of_not_refused {state : CompositeState} {endpointWord : UInt64}
    {destinationSlot : Nat} (hmode : state.execution.mode = .running)
    (hnested : state.refusesNestedTransfer
      (.ordinary (.transferAccept endpointWord destinationSlot)) = false) :
    NestedFree state endpointWord := by
  intro resolution hresolve transfer hpending hne
  simp only [CompositeState.refusesNestedTransfer, hmode, hresolve, hpending,
    Bool.and_eq_false_iff, bne_eq_false_iff_eq, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hnested
  rcases hnested with heq | hnone
  · exact absurd heq hne
  · exact hnone

/-- **The observer's transfer receipt keeps the authority in agreement.**  The
installed capability's lineage and the carried object's view were part of the
offer the observer saw; the carried object has no transfer of its own pending
(`NestedFree`), so nothing beyond the offer becomes reachable. -/
theorem agree_accept {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hagree : ExtraAgree observer left right)
    (endpointWord : UInt64) (destinationSlot : Nat)
    (hfree : NestedFree left endpointWord)
    (hlow' : LowEquiv observer
      (applyOperation left (.transferAccept endpointWord destinationSlot))
      (applyOperation right (.transferAccept endpointWord destinationSlot)))
    (hissuedL : Issued left) (hissuedR : Issued right) :
    ExtraAgree observer
      (applyOperation left (.transferAccept endpointWord destinationSlot))
      (applyOperation right (.transferAccept endpointWord destinationSlot)) := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  obtain ⟨hLvalid, hRvalid⟩ := ownStep_pendingValid h
  have hcongr := acceptWordCheck_congr _ _ observer (ownStep_callerInputs h) hLvalid hRvalid
    endpointWord destinationSlot
  unfold NestedFree at hfree
  rw [hLs] at hfree
  simp only [applyOperation_transferAccept, hLs, hRs, hcongr] at hlow' ⊢
  have hcapsL := (transfers_published h.leftWF.1).1
  have hcapsR := (transfers_published h.rightWF.1).1
  have hmailboxL := (transfers_published h.leftWF.1).2
  have hmailboxR := (transfers_published h.rightWF.1).2
  cases hcheck : acceptWordCheck right.transfers observer endpointWord destinationSlot with
  | error reason =>
      simp only [hcheck]
      exact hagree
  | ok result =>
      obtain ⟨endpointCap, envelope, sealed⟩ := result
      simp only [hcheck] at hlow' ⊢
      obtain ⟨slot, hfoundL, hpendingL, _⟩ :=
        acceptWordCheck_ok _ _ _ _ _ _ _ (hcongr.trans hcheck)
      obtain ⟨resolution, hresolve, hobjectEq⟩ :=
        CompositeLocalRespect.acceptWordCheck_endpoint _ _ _ _ _ _ _ (hcongr.trans hcheck)
      rw [hcapsL] at hfoundL
      have hendpointMem : some endpointCap ∈ row left observer := mem_row_of_lookup hfoundL
      have hendpointNamed : Names left observer endpointCap.object = true :=
        names_of_mem hendpointMem
      have hpendingR : right.transfers.pending endpointCap.object = sealed := by
        rw [← pending_of_view (h.low.namedView _ hendpointNamed)]; exact hpendingL
      cases sealed with
      | none =>
          -- Data receipt: only the endpoint's mailbox changes.
          dsimp only [acceptOutcome] at hlow' ⊢
          have hframe : ∀ (state : CompositeState), state.Coherent →
              Names state observer endpointCap.object = true →
              Frame observer state (installTransfers state
                (CapabilityTransfer.deliverData state.transfers observer endpointCap
                  envelope).state) ∧
              row (installTransfers state (CapabilityTransfer.deliverData state.transfers
                observer endpointCap envelope).state) observer = row state observer := by
            intro state hcoherent hnamed
            have hcaps := (transfers_published hcoherent).1
            have hmailbox := (transfers_published hcoherent).2
            have hcapsAfter : (installTransfers state (CapabilityTransfer.deliverData
                state.transfers observer endpointCap envelope).state).capabilities =
                state.capabilities := by
              simp [installTransfers, CapabilityTransfer.deliverData, CapabilityTransfer.record,
                hcaps]
            refine ⟨frame_of_target hcapsAfter
              (by simp [installTransfers, CapabilityTransfer.deliverData,
                CapabilityTransfer.record])
              (some endpointCap.object) (fun object h => by cases h; exact hnamed) ?_, ?_⟩
            · intro object hne
              have hne' : object ≠ endpointCap.object := fun h => hne (by rw [h])
              simp only [objectView, backing, installTransfers, CapabilityTransfer.deliverData,
                CapabilityTransfer.record, EndpointIPC.setOption, hne', ↓reduceIte, hcaps,
                hmailbox]
            · simp only [CompositeObservation.row, hcapsAfter]
          obtain ⟨hframeL, hrowL⟩ := hframe left h.leftWF.1 hendpointNamed
          obtain ⟨hframeR, _⟩ := hframe right h.rightWF.1 (h.low.namesEq _ ▸ hendpointNamed)
          exact agree_of_extra hlow' (extra_of_frame h.low (extra_of_agree h.low hagree)
            hissuedL hissuedR hframeL hframeR (row_sub_of_eq hrowL) hlow')
      | some transfer =>
          dsimp only [acceptOutcome] at hlow' ⊢
          -- A carried object other than the endpoint has no transfer of its
          -- own pending.
          have hcarriedFree : transfer.object ≠ endpointCap.object →
              left.transfers.pending transfer.object = none := by
            intro hne
            apply hfree resolution hresolve
            · rw [hobjectEq]; exact hpendingL
            · rw [hobjectEq]; exact hne
          obtain ⟨hlineageT, hviewT, _⟩ := hagree.named hendpointNamed hpendingL
          -- The published stores.
          have hcapsAfter : ∀ (state : CompositeState),
              (installTransfers state (CapabilityTransfer.deliver state.transfers observer
                destinationSlot endpointCap envelope transfer).state).capabilities =
              Capability.install state.transfers.capabilities observer destinationSlot
                ⟨transfer.object, transfer.kind, transfer.rights, transfer.identity,
                  some transfer.parent⟩ := by
            intro state
            simp [installTransfers, CapabilityTransfer.deliver, CapabilityTransfer.record]
          have hpendingAfter : ∀ (state : CompositeState) object,
              (installTransfers state (CapabilityTransfer.deliver state.transfers observer
                destinationSlot endpointCap envelope transfer).state).transfers.pending object =
              if object = endpointCap.object then none else state.transfers.pending object := by
            intro state object
            simp [installTransfers, CapabilityTransfer.deliver, CapabilityTransfer.record,
              CapabilityTransfer.setPending]
          have hviewAfter : ∀ (state : CompositeState), state.Coherent → ∀ object,
              object ≠ endpointCap.object →
              objectView (installTransfers state (CapabilityTransfer.deliver state.transfers
                observer destinationSlot endpointCap envelope transfer).state) object =
              objectView state object := by
            intro state hcoherent object hne
            have hcaps := (transfers_published hcoherent).1
            have hmailbox := (transfers_published hcoherent).2
            simp only [objectView, backing, installTransfers, CapabilityTransfer.deliver,
              CapabilityTransfer.record, EndpointIPC.setOption, CapabilityTransfer.setPending,
              hne, ↓reduceIte, Capability.install, hcaps, hmailbox]
          have hlineageAfter : ∀ (state : CompositeState), state.Coherent → ∀ identity,
              lineage (installTransfers state (CapabilityTransfer.deliver state.transfers
                observer destinationSlot endpointCap envelope transfer).state).capabilities
                  identity = lineage state.capabilities identity := by
            intro state hcoherent identity
            rw [hcapsAfter, (transfers_published hcoherent).1]
            apply lineage_eq_of_derivations; rfl
          have hrowAfter : ∀ (state : CompositeState), state.Coherent → ∀ cap,
              some cap ∈ row (installTransfers state (CapabilityTransfer.deliver state.transfers
                observer destinationSlot endpointCap envelope transfer).state) observer →
              cap = ⟨transfer.object, transfer.kind, transfer.rights, transfer.identity,
                some transfer.parent⟩ ∨ some cap ∈ row state observer := by
            intro state hcoherent cap hmem
            simp only [CompositeObservation.row, hcapsAfter, (transfers_published hcoherent).1,
              Capability.capabilitySpace, Capability.install, List.mem_map,
              List.mem_range] at hmem
            obtain ⟨candidate, hrange, hslot⟩ := hmem
            by_cases hdest : candidate = destinationSlot
            · simp only [hdest, and_self, ↓reduceIte, Option.some.injEq] at hslot
              exact Or.inl hslot.symm
            · simp only [hdest, and_false, ↓reduceIte] at hslot
              right
              simp only [CompositeObservation.row, Capability.capabilitySpace, List.mem_map,
                List.mem_range]
              exact ⟨candidate, hrange, hslot⟩
          have hcohL := h.leftWF.1
          have hcohR := h.rightWF.1
          constructor
          · intro cap hmem
            rw [hlineageAfter left hcohL, hlineageAfter right hcohR]
            rcases hrowAfter left hcohL cap hmem with rfl | hold
            · exact hlineageT
            · exact hagree.rows cap hold
          · intro cap carried hmem hpending
            rw [hpendingAfter] at hpending
            by_cases hobject : cap.object = endpointCap.object
            · simp only [hobject, ↓reduceIte] at hpending
              cases hpending
            simp only [hobject, ↓reduceIte] at hpending
            rcases hrowAfter left hcohL cap hmem with rfl | hold
            · -- The installed capability: its object has nothing pending.
              rw [hcarriedFree hobject] at hpending
              cases hpending
            obtain ⟨hlineage, hview, hnested⟩ := hagree.carried cap carried hold hpending
            rw [hlineageAfter left hcohL, hlineageAfter right hcohR]
            refine ⟨hlineage, ?_, ?_⟩
            · by_cases hcarriedObject : carried.object = endpointCap.object
              · rw [hcarriedObject]
                apply hlow'.namedView
                simp only [Names, CompositeObservation.row, hcapsAfter left, Capability.capabilitySpace,
                  Capability.install, List.any_eq_true, List.mem_map, List.mem_range]
                obtain ⟨endpointSlotIndex, hin, hslotE⟩ :=
                  (mem_row_slot_range hendpointMem)
                refine ⟨some endpointCap, ⟨endpointSlotIndex, ?_, ?_⟩, by simp⟩
                · rw [hcapsL]; exact hin
                · rw [hcapsL]
                  by_cases hsame : endpointSlotIndex = destinationSlot
                  · exfalso
                    obtain ⟨_, _, _, hdestFree⟩ :=
                      acceptWordCheck_ok _ _ _ _ _ _ _ (hcongr.trans hcheck)
                    have := (hdestFree transfer rfl).2
                    rw [hcapsL, ← hsame, hslotE] at this
                    cases this
                  · simp [hsame, hslotE]
              · rw [hviewAfter left hcohL _ hcarriedObject,
                  hviewAfter right hcohR _ hcarriedObject]
                exact hview
            · intro nested hnestedL
              rw [hpendingAfter] at hnestedL
              by_cases hcarriedObject : carried.object = endpointCap.object
              · simp only [hcarriedObject, ↓reduceIte] at hnestedL
                cases hnestedL
              · simp only [hcarriedObject, ↓reduceIte] at hnestedL
                rw [hlineageAfter left hcohL, hlineageAfter right hcohR]
                exact hnested nested hnestedL

/-! ## Subtree revocation of the observer's own capability -/

/-- What survives the revocation of `root`, decided by lineage. -/
def cut (state : CompositeState) (root : Nat) (cap : Capability.Capability) :
    Option Capability.Capability :=
  if root ∈ lineage state.capabilities cap.identity then none else some cap

/-- The transfer pending on `object` after the revocation of `root`. -/
def cancelPending (state : CompositeState) (root object : Nat) :
    Option CapabilityTransfer.Sealed :=
  match state.transfers.pending object with
  | some transfer =>
      if root ∈ lineage state.capabilities transfer.identity then none else some transfer
  | none => none

/-- The mailbox of `object` after the revocation of `root`. -/
def cancelMailbox (state : CompositeState) (root object : Nat) :
    Option EndpointIPC.Envelope :=
  match state.transfers.pending object with
  | some transfer =>
      if root ∈ lineage state.capabilities transfer.identity then none
      else state.ipc.endpoints.mailbox object
  | none => state.ipc.endpoints.mailbox object

/-- The composite state after the accepted revocation of `root`. -/
def revoked (state : CompositeState) (root : Nat) : CompositeState :=
  installRevokedSubtree state root (Capability.clearSubtree state.capabilities root)

theorem descendsFrom_issued {state : CompositeState} (hissued : Issued state)
    (identity root : Nat) (hlt : identity < state.capabilities.nextIdentity) :
    Capability.descendsFrom state.capabilities identity root state.capabilities.nextIdentity =
      decide (root ∈ lineage state.capabilities identity) :=
  descendsFrom_eq_lineage _ hissued.precede identity root hlt

theorem revoked_capabilities (state : CompositeState) (root : Nat) :
    (revoked state root).capabilities = Capability.clearSubtree state.capabilities root := rfl

theorem revoked_slots {state : CompositeState} (hissued : Issued state) (root subject slot : Nat) :
    (revoked state root).capabilities.slots subject slot =
      (state.capabilities.slots subject slot).bind (cut state root) := by
  rw [revoked_capabilities]
  simp only [Capability.clearSubtree]
  cases hslot : state.capabilities.slots subject slot with
  | none => rfl
  | some cap =>
      simp only [Option.bind_some, cut]
      rw [descendsFrom_issued hissued _ _ (hissued.slots subject slot cap hslot)]
      by_cases hmem : root ∈ lineage state.capabilities cap.identity <;> simp [hmem]

theorem revoked_pending {state : CompositeState} (hcoherent : state.Coherent)
    (hissued : Issued state) (root object : Nat) :
    (revoked state root).transfers.pending object = cancelPending state root object := by
  have hcaps := (transfers_published hcoherent).1
  show (CapabilityTransfer.publishSubtreeRevocation state.transfers root _).pending object = _
  rw [CapabilityTransfer.publishSubtreeRevocation_pending]
  simp only [cancelPending, CapabilityTransfer.descendsFromRoot, hcaps]
  cases hpending : state.transfers.pending object with
  | none => rfl
  | some transfer =>
      simp only
      rw [descendsFrom_issued hissued _ _ (hissued.pending _ _ hpending)]
      by_cases hmem : root ∈ lineage state.capabilities transfer.identity <;> simp [hmem]

theorem revoked_mailbox {state : CompositeState} (hcoherent : state.Coherent)
    (hissued : Issued state) (root object : Nat) :
    (revoked state root).ipc.endpoints.mailbox object = cancelMailbox state root object := by
  have hcaps := (transfers_published hcoherent).1
  have hmailbox := (transfers_published hcoherent).2
  show (CapabilityTransfer.publishSubtreeRevocation state.transfers root _).mailbox object = _
  rw [CapabilityTransfer.publishSubtreeRevocation_mailbox]
  simp only [cancelMailbox, CapabilityTransfer.descendsFromRoot, hcaps, hmailbox]
  cases hpending : state.transfers.pending object with
  | none => rfl
  | some transfer =>
      simp only
      rw [descendsFrom_issued hissued _ _ (hissued.pending _ _ hpending)]
      by_cases hmem : root ∈ lineage state.capabilities transfer.identity <;> simp [hmem]

theorem revoked_objectView {state : CompositeState} (hcoherent : state.Coherent)
    (hissued : Issued state) (root object : Nat) :
    objectView (revoked state root) object =
      { objectView state object with
        mailbox := cancelMailbox state root object
        sealed := cancelPending state root object } := by
  rw [show objectView (revoked state root) object =
    { objectView state object with
      mailbox := (revoked state root).ipc.endpoints.mailbox object
      sealed := (revoked state root).transfers.pending object } from rfl,
    revoked_mailbox hcoherent hissued, revoked_pending hcoherent hissued]

theorem revoked_lineage (state : CompositeState) (root identity : Nat) :
    lineage (revoked state root).capabilities identity = lineage state.capabilities identity := by
  apply lineage_eq_of_derivations; rfl

theorem revoked_current (state : CompositeState) (root : Nat) :
    (revoked state root).lifecycle.current = state.lifecycle.current := rfl

theorem revoked_subjects (state : CompositeState) (root : Nat) :
    (revoked state root).capabilities.subjects = state.capabilities.subjects := rfl

theorem revoked_slotCapacity (state : CompositeState) (root : Nat) :
    (revoked state root).capabilities.slotCapacity = state.capabilities.slotCapacity := rfl

theorem revoked_virtualMemory_owner (state : CompositeState) (root : Nat) :
    (revoked state root).virtualMemory.owner = state.virtualMemory.owner := rfl

theorem revoked_virtualMemory_mappings (state : CompositeState) (root : Nat) :
    (revoked state root).virtualMemory.mappings = state.virtualMemory.mappings := rfl

theorem revoked_waiterEndpoint (state : CompositeState) (root : Nat) :
    (revoked state root).blockingIPC.waiterEndpoint = state.blockingIPC.waiterEndpoint := rfl

theorem revoked_completion (state : CompositeState) (root : Nat) :
    (revoked state root).blockingIPC.completion = state.blockingIPC.completion := rfl

theorem revoked_row {state : CompositeState} (hissued : Issued state) (observer root : Nat) :
    row (revoked state root) observer = (row state observer).map (·.bind (cut state root)) := by
  simp only [CompositeObservation.row, Capability.capabilitySpace, List.map_map]
  rw [show (revoked state root).capabilities.slotCapacity observer =
    state.capabilities.slotCapacity observer from rfl]
  apply List.map_congr_left
  intro slot _
  exact revoked_slots hissued root observer slot

theorem mem_revoked_row {state : CompositeState} (hissued : Issued state) {observer root : Nat}
    {cap : Capability.Capability} (hmem : some cap ∈ row (revoked state root) observer) :
    some cap ∈ row state observer ∧ root ∉ lineage state.capabilities cap.identity := by
  rw [revoked_row hissued] at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨slot, hslot, hcut⟩ := hmem
  cases slot with
  | none => cases hcut
  | some found =>
      simp only [Option.bind_some, cut] at hcut
      by_cases hroot : root ∈ lineage state.capabilities found.identity
      · simp [hroot] at hcut
      · simp only [hroot, ↓reduceIte, Option.some.injEq] at hcut
        subst hcut
        exact ⟨hslot, hroot⟩

/-- Cancellation agrees on an object whose view and pending lineage agree. -/
theorem cancel_congr {left right : CompositeState} {root object : Nat}
    (hview : objectView left object = objectView right object)
    (hlineage : ∀ transfer, left.transfers.pending object = some transfer →
      lineage left.capabilities transfer.identity = lineage right.capabilities transfer.identity) :
    cancelPending left root object = cancelPending right root object ∧
      cancelMailbox left root object = cancelMailbox right root object := by
  have hpending := pending_of_view hview
  have hmailbox := mailbox_of_view hview
  simp only [cancelPending, cancelMailbox, ← hpending, ← hmailbox]
  cases hcase : left.transfers.pending object with
  | none => exact ⟨rfl, rfl⟩
  | some transfer =>
      simp only
      rw [hlineage transfer hcase]
      exact ⟨rfl, rfl⟩

theorem revoked_objectView_congr {left right : CompositeState} (hcohL : left.Coherent)
    (hcohR : right.Coherent) (hissuedL : Issued left) (hissuedR : Issued right) {root object : Nat}
    (hview : objectView left object = objectView right object)
    (hlineage : ∀ transfer, left.transfers.pending object = some transfer →
      lineage left.capabilities transfer.identity = lineage right.capabilities transfer.identity) :
    objectView (revoked left root) object = objectView (revoked right root) object := by
  obtain ⟨hpending, hmailbox⟩ := cancel_congr (root := root) hview hlineage
  rw [revoked_objectView hcohL hissuedL, revoked_objectView hcohR hissuedR, hview, hpending,
    hmailbox]

/-- **Subtree revocation of the observer's own capability is step consistent on
the full view**: what it removes from the observer's row and cancels on the
endpoints it names or is offered is decided by lineages in the full view. -/
theorem full_revoked {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hagree : ExtraAgree observer left right)
    (hissuedL : Issued left) (hissuedR : Issued right) (root : Nat) :
    LowEquiv observer (revoked left root) (revoked right root) ∧
      ExtraAgree observer (revoked left root) (revoked right root) := by
  have hcohL := h.leftWF.1
  have hcohR := h.rightWF.1
  have hcutRow : (row left observer).map (·.bind (cut left root)) =
      (row right observer).map (·.bind (cut right root)) := by
    rw [← h.low.rowEq]
    apply List.map_congr_left
    intro slot hmem
    cases slot with
    | none => rfl
    | some cap =>
        simp only [Option.bind_some, cut]
        rw [hagree.rows cap hmem]
  have hrowAfter : row (revoked left root) observer = row (revoked right root) observer := by
    rw [revoked_row hissuedL, revoked_row hissuedR, hcutRow]
  -- Every object the observer names afterwards it named before.
  have hnamedView : ∀ cap, some cap ∈ row (revoked left root) observer →
      objectView (revoked left root) cap.object = objectView (revoked right root) cap.object := by
    intro cap hmem
    obtain ⟨hold, _⟩ := mem_revoked_row hissuedL hmem
    have hnamed := names_of_mem hold
    apply revoked_objectView_congr hcohL hcohR hissuedL hissuedR
      (h.low.namedView cap.object hnamed)
    intro transfer hpending
    exact (hagree.named hnamed hpending).1
  have hlow' : LowEquiv observer (revoked left root) (revoked right root) := by
    unfold LowEquiv
    have hbase := h.low
    unfold LowEquiv at hbase
    have hscheduled := congrArg View.scheduled hbase
    have hlive := congrArg View.live hbase
    have hcapacity := congrArg View.capacity hbase
    have howns := congrArg View.owns hbase
    have hmappings := congrArg View.mappings hbase
    have hwaiting := congrArg View.waitingOn hbase
    have hcompletion := congrArg View.completion hbase
    simp only [observe] at hscheduled hlive hcapacity howns hmappings hwaiting hcompletion
    have hnamedList : (row (revoked left root) observer).map
          (Option.map fun cap => objectView (revoked left root) cap.object) =
        (row (revoked right root) observer).map
          (Option.map fun cap => objectView (revoked right root) cap.object) := by
      rw [← hrowAfter]
      apply List.map_congr_left
      intro slot hmem
      cases slot with
      | none => rfl
      | some cap => simp [hnamedView cap hmem]
    simp only [observe, revoked_current, revoked_subjects, revoked_slotCapacity,
      revoked_virtualMemory_owner, revoked_virtualMemory_mappings, revoked_waiterEndpoint,
      revoked_completion]
    rw [hnamedList, hrowAfter, hscheduled, hlive, hcapacity]
    congr 1
  refine ⟨hlow', ?_, ?_⟩
  · intro cap hmem
    obtain ⟨hold, _⟩ := mem_revoked_row hissuedL hmem
    rw [revoked_lineage, revoked_lineage]
    exact hagree.rows cap hold
  · intro cap transfer hmem hpending
    obtain ⟨hold, _⟩ := mem_revoked_row hissuedL hmem
    rw [revoked_pending hcohL hissuedL] at hpending
    have hbefore : left.transfers.pending cap.object = some transfer := by
      simp only [cancelPending] at hpending
      split at hpending
      · split at hpending
        · cases hpending
        · rename_i found hfound _
          rw [hfound]; exact hpending
      · cases hpending
    obtain ⟨hlineage, hview, hnested⟩ := hagree.carried cap transfer hold hbefore
    rw [revoked_lineage, revoked_lineage]
    refine ⟨hlineage, ?_, ?_⟩
    · exact revoked_objectView_congr hcohL hcohR hissuedL hissuedR hview hnested
    · intro nested hnestedL
      rw [revoked_pending hcohL hissuedL] at hnestedL
      rw [revoked_lineage, revoked_lineage]
      apply hnested
      simp only [cancelPending] at hnestedL
      split at hnestedL
      · split at hnestedL
        · cases hnestedL
        · rename_i found hfound _
          rw [hfound]; exact hnestedL
      · cases hnestedL

/-- The observer's subtree revocation of its own slot either changes nothing
on both sides or revokes the same root on both sides. -/
theorem apply_revokeSubtree_self {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (authoritySlot victimSlot : Nat) :
    (applyOperation left (.capabilityRevokeSubtree authoritySlot observer victimSlot) = left ∧
        applyOperation right (.capabilityRevokeSubtree authoritySlot observer victimSlot) =
          right) ∨
      ∃ root,
        applyOperation left (.capabilityRevokeSubtree authoritySlot observer victimSlot) =
            revoked left root ∧
          applyOperation right (.capabilityRevokeSubtree authoritySlot observer victimSlot) =
            revoked right root := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  have hresult := revokeSubtreeRuntimeSafe_self_congr left.capabilities right.capabilities
    h.leftWF.2.2.2.1 h.rightWF.2.2.2.1 observer authoritySlot victimSlot h.lookup
  simp only [applyOperation, hLs, hRs]
  generalize hoL : Capability.revokeSubtreeRuntimeSafe left.capabilities observer authoritySlot
    observer victimSlot = outL at hresult ⊢
  generalize hoR : Capability.revokeSubtreeRuntimeSafe right.capabilities observer authoritySlot
    observer victimSlot = outR at hresult ⊢
  rcases outL with ⟨capsL, resultL⟩
  rcases outR with ⟨capsR, resultR⟩
  simp only at hresult
  subst hresult
  cases resultL with
  | rejected reason => exact Or.inl ⟨rfl, rfl⟩
  | accepted =>
      obtain ⟨targetL, hfoundL, hcapsL⟩ :=
        Capability.revokeSubtreeRuntimeSafe_accepted_target _ _ _ _ _ _ hoL
      obtain ⟨targetR, hfoundR, hcapsR⟩ :=
        Capability.revokeSubtreeRuntimeSafe_accepted_target _ _ _ _ _ _ hoR
      have htarget : targetL = targetR := by
        rw [h.lookup victimSlot, hfoundR] at hfoundL
        cases hfoundL
        rfl
      subst htarget
      subst hcapsL hcapsR
      right
      refine ⟨targetL.identity, ?_, ?_⟩
      · simp only [hfoundL]; rfl
      · simp only [hfoundR]; rfl

end LeanOS.CompositeFullSteps
