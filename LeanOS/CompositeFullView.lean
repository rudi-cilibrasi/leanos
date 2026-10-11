import LeanOS.CompositeOwnBlocking
import LeanOS.CompositeSubjectGate

/-!
# The observer's full authority view

`CompositeObservation.observe` is what a subject sees through the capabilities
it holds.  Two more things are within its authority, and the remaining
channels of issue #479 come from leaving them out:

* **Lineage.**  Subtree revocation of the observer's own capability removes
  every capability and every sealed transfer derived from it, in any row.  The
  observer's row can hold a capability derived from its own through another
  subject's delegation, and an endpoint it names can carry a sealed transfer
  derived the same way (`CompositeSwitchedChannels.revokeSubtree_own_step_inconsistent`).
  Which ones go is the observer's revocation authority.
* **What is offered to it.**  A sealed transfer pending on an endpoint the
  observer names is an offer to it: accepting installs the carried capability
  and with it the carried object's view (`CompositeOwnSteps.CarriedAgree`).

`extra` adds, for every capability in the observer's row:

* its lineage, the chain of identities it derives from (`lineage`);
* for the sealed transfer pending on the object it names, if any: that
  transfer's lineage, the carried object's view, and the lineage of the
  sealed transfer pending on the carried object (`CarriedView`).

The second level stops there: the subject gate refuses receipt of a transfer
whose carried object has a transfer of its own pending
(`FailStop.CompositeState.refusesNestedTransfer`), so receipt never makes an
object reachable that no offer to the observer carried.

`FullLowEquiv` is equality of `observe` and `extra`.

Lineages are chains of identities: the derivation history is append-only and
orders every parent before its child (`Capability.DerivationsWellFormed`), so
the chain of an issued identity never changes (`chain_congr`), and it decides
the bounded ancestry walk of revocation (`descendsFrom_eq_lineage`).
-/
namespace LeanOS.CompositeFullView

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
set_option linter.unusedSimpArgs false

/-! ## Lineage -/

/-- The identities `identity` derives from, itself first, following at most
`fuel` recorded parent edges: exactly the walk of `Capability.descendsFrom`. -/
def chain (capabilities : Capability.State) : Nat → Nat → List Nat
  | identity, 0 => [identity]
  | identity, fuel + 1 => identity ::
      match capabilities.derivations identity with
      | some (some parent, _, _, _) => chain capabilities parent fuel
      | _ => []

/-- The complete lineage of an identity: every parent precedes its child, so
`identity` edges suffice. -/
def lineage (capabilities : Capability.State) (identity : Nat) : List Nat :=
  chain capabilities identity identity

/-- Parents precede their children. -/
def ParentsPrecede (capabilities : Capability.State) : Prop :=
  ∀ identity parent object kind rights,
    capabilities.derivations identity = some (some parent, object, kind, rights) →
      parent < identity

theorem parentsPrecede_of_wellFormed {capabilities : Capability.State}
    (hwf : Capability.DerivationsWellFormed capabilities) : ParentsPrecede capabilities := by
  intro identity parent object kind rights hderivation
  exact (hwf identity (some parent) object kind rights hderivation).2.1

theorem descendsFrom_eq_chain (capabilities : Capability.State) (candidate ancestor fuel : Nat) :
    Capability.descendsFrom capabilities candidate ancestor fuel =
      decide (ancestor ∈ chain capabilities candidate fuel) := by
  induction fuel generalizing candidate with
  | zero =>
      simp only [Capability.descendsFrom, chain, List.mem_singleton]
      by_cases h : candidate = ancestor
      · subst h; simp
      · simp [h, Ne.symm h]
  | succ fuel ih =>
      simp only [Capability.descendsFrom, chain, List.mem_cons]
      by_cases h : candidate = ancestor
      · subst h; simp
      · have hne : ¬ ancestor = candidate := Ne.symm h
        simp only [beq_iff_eq, h, ↓reduceIte, hne, false_or]
        split
        · rename_i parent _ _ _ hderivation
          rw [ih parent, hderivation]
        · rename_i hnot
          split
          · rename_i parent _ _ _ hderivation
            exact absurd hderivation (hnot parent _ _ _)
          · simp

/-- Only the derivations at or below an identity decide its chain. -/
theorem chain_congr (a b : Capability.State) (hprecede : ParentsPrecede a) :
    ∀ fuel identity, (∀ index, index ≤ identity → b.derivations index = a.derivations index) →
      chain b identity fuel = chain a identity fuel := by
  intro fuel
  induction fuel with
  | zero => intro identity _; rfl
  | succ fuel ih =>
      intro identity hsame
      simp only [chain, hsame identity (Nat.le_refl _)]
      split
      · rename_i parent _ _ _ hderivation
        have hlt := hprecede identity parent _ _ _ hderivation
        rw [ih parent fun index hindex => hsame index (Nat.le_trans hindex (Nat.le_of_lt hlt))]
      · rfl

theorem chain_eq_of_derivations (a b : Capability.State) (h : a.derivations = b.derivations) :
    ∀ fuel identity, chain a identity fuel = chain b identity fuel := by
  intro fuel
  induction fuel with
  | zero => intro identity; rfl
  | succ fuel ih =>
      intro identity
      simp only [chain, h]
      split
      · rename_i parent _ _ _ _
        rw [ih parent]
      · rfl

theorem lineage_eq_of_derivations (a b : Capability.State) (h : a.derivations = b.derivations)
    (identity : Nat) : lineage a identity = lineage b identity :=
  chain_eq_of_derivations a b h identity identity

/-- Enough fuel walks the whole chain. -/
theorem chain_stable (a : Capability.State) (hprecede : ParentsPrecede a) :
    ∀ identity fuel, identity ≤ fuel → chain a identity fuel = chain a identity identity := by
  intro identity
  induction identity using Nat.strongRecOn with
  | _ identity ih =>
      have key : ∀ fuel, identity ≤ fuel → ∀ other, identity ≤ other →
          chain a identity fuel = chain a identity other := by
        intro fuel hfuel other hother
        cases fuel with
        | zero =>
            cases other with
            | zero => rfl
            | succ other =>
                have hzero : identity = 0 := Nat.le_zero.mp hfuel
                subst hzero
                simp only [chain]
                split
                · rename_i parent _ _ _ hderivation
                  exact absurd (hprecede 0 parent _ _ _ hderivation) (Nat.not_lt_zero _)
                · rfl
        | succ fuel =>
            cases other with
            | zero =>
                have hzero : identity = 0 := Nat.le_zero.mp hother
                subst hzero
                simp only [chain]
                split
                · rename_i parent _ _ _ hderivation
                  exact absurd (hprecede 0 parent _ _ _ hderivation) (Nat.not_lt_zero _)
                · rfl
            | succ other =>
                simp only [chain]
                split
                · rename_i parent _ _ _ hderivation
                  have hlt := hprecede identity parent _ _ _ hderivation
                  rw [ih parent hlt fuel (by omega), ih parent hlt other (by omega)]
                · rfl
      intro fuel hfuel
      exact key fuel hfuel identity (Nat.le_refl _)

/-- Revocation's bounded walk is membership in the lineage. -/
theorem descendsFrom_eq_lineage (a : Capability.State) (hprecede : ParentsPrecede a)
    (candidate ancestor : Nat) (hissued : candidate < a.nextIdentity) :
    Capability.descendsFrom a candidate ancestor a.nextIdentity =
      decide (ancestor ∈ lineage a candidate) := by
  rw [descendsFrom_eq_chain, lineage, chain_stable a hprecede candidate _ (Nat.le_of_lt hissued)]

/-- An extension of the derivation history keeps every issued lineage. -/
theorem lineage_of_extends (a b : Capability.State) (hprecede : ParentsPrecede a)
    (hextends : ∀ index, index < a.nextIdentity → b.derivations index = a.derivations index)
    (identity : Nat) (hissued : identity < a.nextIdentity) :
    lineage b identity = lineage a identity :=
  chain_congr a b hprecede identity identity fun index hindex =>
    hextends index (Nat.lt_of_le_of_lt hindex hissued)

/-! ## The full view -/

/-- What the observer sees of a sealed transfer offered to it. -/
structure CarriedView where
  lineage : List Nat
  view : ObjectView
  nested : Option (List Nat)
  deriving DecidableEq

/-- What the observer's authority adds to one capability of its row. -/
structure SlotExtra where
  lineage : List Nat
  carried : Option CarriedView
  deriving DecidableEq

def carriedView (state : CompositeState) (transfer : CapabilityTransfer.Sealed) :
    CarriedView :=
  { lineage := lineage state.capabilities transfer.identity
    view := objectView state transfer.object
    nested := (state.transfers.pending transfer.object).map fun nested =>
      lineage state.capabilities nested.identity }

def slotExtra (state : CompositeState) (cap : Capability.Capability) : SlotExtra :=
  { lineage := lineage state.capabilities cap.identity
    carried := (state.transfers.pending cap.object).map (carriedView state) }

def extra (observer : Nat) (state : CompositeState) : List (Option SlotExtra) :=
  (row state observer).map (Option.map (slotExtra state))

structure FullView where
  base : View
  extra : List (Option SlotExtra)

def observeFull (observer : Nat) (state : CompositeState) : FullView :=
  { base := observe observer state, extra := extra observer state }

/-- Full low equivalence: the view and the authority it implies. -/
def FullLowEquiv (observer : Nat) (left right : CompositeState) : Prop :=
  observeFull observer left = observeFull observer right

theorem FullLowEquiv.low {observer left right} (h : FullLowEquiv observer left right) :
    LowEquiv observer left right :=
  congrArg FullView.base h

theorem FullLowEquiv.extra {observer left right} (h : FullLowEquiv observer left right) :
    extra observer left = extra observer right :=
  congrArg FullView.extra h

theorem fullLowEquiv_of {observer left right} (hlow : LowEquiv observer left right)
    (hextra : extra observer left = extra observer right) : FullLowEquiv observer left right := by
  unfold FullLowEquiv observeFull
  rw [show observe observer left = observe observer right from hlow, hextra]

/-- Extra agreement, slot by slot. -/
theorem extra_pointwise {observer left right} (hlow : LowEquiv observer left right)
    (hextra : extra observer left = extra observer right) (cap : Capability.Capability)
    (hmem : some cap ∈ row left observer) : slotExtra left cap = slotExtra right cap := by
  unfold extra at hextra
  rw [← hlow.rowEq] at hextra
  have h := List.map_inj_left.mp hextra (some cap) hmem
  simpa using h

theorem extra_of_pointwise {observer left right}
    (hrow : row left observer = row right observer)
    (hslots : ∀ cap, some cap ∈ row left observer → slotExtra left cap = slotExtra right cap) :
    extra observer left = extra observer right := by
  unfold extra
  rw [← hrow]
  apply List.map_congr_left
  intro slot hmem
  cases slot with
  | none => rfl
  | some cap => simp [hslots cap hmem]

theorem names_of_mem {state : CompositeState} {observer : Nat} {cap : Capability.Capability}
    (hmem : some cap ∈ row state observer) : Names state observer cap.object = true := by
  simp only [Names, List.any_eq_true]
  exact ⟨some cap, hmem, by simp⟩

/-- Whether a sealed transfer offered to the observer carries `object`. -/
def Carried (state : CompositeState) (observer : Nat) (object : Nat) : Bool :=
  (row state observer).any fun slot =>
    slot.any fun cap => (state.transfers.pending cap.object).any (·.object == object)

theorem carried_of_mem {state : CompositeState} {observer : Nat} {cap : Capability.Capability}
    {transfer : CapabilityTransfer.Sealed} (hmem : some cap ∈ row state observer)
    (hpending : state.transfers.pending cap.object = some transfer) :
    Carried state observer transfer.object = true := by
  simp only [Carried, List.any_eq_true]
  exact ⟨some cap, hmem, by simp [hpending]⟩

theorem pending_of_view {left right : CompositeState} {object : Nat}
    (h : objectView left object = objectView right object) :
    left.transfers.pending object = right.transfers.pending object :=
  congrArg ObjectView.sealed h

theorem mailbox_of_view {left right : CompositeState} {object : Nat}
    (h : objectView left object = objectView right object) :
    left.ipc.endpoints.mailbox object = right.ipc.endpoints.mailbox object :=
  congrArg ObjectView.mailbox h

/-! ## Agreement on the authority, fact by fact -/

/-- `extra` agreement as facts about lineages and carried objects. -/
structure ExtraAgree (observer : Nat) (left right : CompositeState) : Prop where
  rows : ∀ cap, some cap ∈ row left observer →
    CompositeFullView.lineage left.capabilities cap.identity =
      CompositeFullView.lineage right.capabilities cap.identity
  carried : ∀ cap transfer, some cap ∈ row left observer →
    left.transfers.pending cap.object = some transfer →
      CompositeFullView.lineage left.capabilities transfer.identity =
          CompositeFullView.lineage right.capabilities transfer.identity ∧
        objectView left transfer.object = objectView right transfer.object ∧
        ∀ nested, left.transfers.pending transfer.object = some nested →
          CompositeFullView.lineage left.capabilities nested.identity =
            CompositeFullView.lineage right.capabilities nested.identity

theorem extra_of_agree {observer left right} (hlow : LowEquiv observer left right)
    (h : ExtraAgree observer left right) : extra observer left = extra observer right := by
  apply extra_of_pointwise hlow.rowEq
  intro cap hmem
  have hpendingEq : left.transfers.pending cap.object = right.transfers.pending cap.object :=
    congrArg ObjectView.sealed (hlow.namedView cap.object (names_of_mem hmem))
  simp only [slotExtra, SlotExtra.mk.injEq]
  refine ⟨h.rows cap hmem, ?_⟩
  rw [← hpendingEq]
  cases hpending : left.transfers.pending cap.object with
  | none => rfl
  | some transfer =>
      obtain ⟨hlineage, hview, hnested⟩ := h.carried cap transfer hmem hpending
      have hnestedEq : left.transfers.pending transfer.object =
          right.transfers.pending transfer.object := congrArg ObjectView.sealed hview
      simp only [Option.map_some, carriedView, Option.some.injEq, CarriedView.mk.injEq]
      refine ⟨hlineage, hview, ?_⟩
      rw [← hnestedEq]
      cases hnestedL : left.transfers.pending transfer.object with
      | none => rfl
      | some nested => simp [hnested nested hnestedL]

theorem agree_of_extra {observer left right} (hlow : LowEquiv observer left right)
    (hextra : extra observer left = extra observer right) : ExtraAgree observer left right := by
  constructor
  · intro cap hmem
    exact congrArg SlotExtra.lineage (extra_pointwise hlow hextra cap hmem)
  · intro cap transfer hmem hpending
    have hslot := extra_pointwise hlow hextra cap hmem
    have hpendingEq : left.transfers.pending cap.object = right.transfers.pending cap.object :=
      congrArg ObjectView.sealed (hlow.namedView cap.object (names_of_mem hmem))
    have hpendingR : right.transfers.pending cap.object = some transfer := hpendingEq ▸ hpending
    simp only [slotExtra, SlotExtra.mk.injEq, hpending, hpendingR, Option.map_some,
      Option.some.injEq, carriedView, CarriedView.mk.injEq] at hslot
    obtain ⟨_, hlineage, hview, hnested⟩ := hslot
    refine ⟨hlineage, hview, ?_⟩
    intro nested hnestedL
    have hnestedR : right.transfers.pending transfer.object = some nested := by
      have := congrArg ObjectView.sealed hview
      simp only [objectView] at this
      rw [← this]; exact hnestedL
    simp only [hnestedL, hnestedR, Option.map_some, Option.some.injEq] at hnested
    exact hnested

theorem fullLowEquiv_of_agree {observer left right} (hlow : LowEquiv observer left right)
    (h : ExtraAgree observer left right) : FullLowEquiv observer left right :=
  fullLowEquiv_of hlow (extra_of_agree hlow h)

theorem FullLowEquiv.agree {observer left right} (h : FullLowEquiv observer left right) :
    ExtraAgree observer left right :=
  agree_of_extra h.low h.extra

/-- Agreement on the authority, for an object the observer names. -/
theorem ExtraAgree.named {observer left right} (hagree : ExtraAgree observer left right)
    {object : Nat} (hnames : Names left observer object = true)
    {transfer : CapabilityTransfer.Sealed}
    (hpending : left.transfers.pending object = some transfer) :
    lineage left.capabilities transfer.identity = lineage right.capabilities transfer.identity ∧
      objectView left transfer.object = objectView right transfer.object ∧
      ∀ nested, left.transfers.pending transfer.object = some nested →
        lineage left.capabilities nested.identity = lineage right.capabilities nested.identity := by
  simp only [Names, List.any_eq_true] at hnames
  obtain ⟨slot, hmem, hslot⟩ := hnames
  cases slot with
  | none => simp at hslot
  | some cap =>
      simp only [Option.any_some, beq_iff_eq] at hslot
      subst hslot
      exact hagree.carried cap transfer hmem hpending

/-! ## Issued identities -/

/-- The well-formedness the full view uses: parents precede children, and
every capability in a row and every pending sealed transfer has an issued
identity. -/
structure Issued (state : CompositeState) : Prop where
  precede : ParentsPrecede state.capabilities
  slots : ∀ subject slot cap, state.capabilities.slots subject slot = some cap →
    cap.identity < state.capabilities.nextIdentity
  pending : ∀ endpoint transfer, state.transfers.pending endpoint = some transfer →
    transfer.identity < state.capabilities.nextIdentity

theorem issued_of_runtime {state : CompositeState} (hstate : RuntimeWellFormed state) :
    Issued state := by
  have hcaps : Capability.WellFormed state.capabilities := hstate.2.2.2.1
  have htransfers : CapabilityTransfer.WellFormed state.transfers := hstate.2.2.2.2.2.2.2.2.2.1
  have hpublished := (transfers_published hstate.1).1
  refine ⟨parentsPrecede_of_wellFormed hcaps.2.1, ?_, ?_⟩
  · intro subject slot cap hslot
    exact (hcaps.1 subject slot cap hslot).2.2.2.2.1
  · intro endpoint transfer hpending
    have h := (htransfers.2 endpoint transfer hpending).2.2.2.2.2.2.2.1
    rw [hpublished] at h
    exact h

theorem mem_row_slot {state : CompositeState} {observer : Nat} {cap : Capability.Capability}
    (hmem : some cap ∈ row state observer) :
    ∃ slot, state.capabilities.slots observer slot = some cap := by
  simp only [row, Capability.capabilitySpace, List.mem_map, List.mem_range] at hmem
  obtain ⟨slot, _, hslot⟩ := hmem
  exact ⟨slot, hslot⟩

theorem mem_row_slot_range {state : CompositeState} {observer : Nat}
    {cap : Capability.Capability} (hmem : some cap ∈ row state observer) :
    ∃ slot, slot < state.capabilities.slotCapacity observer ∧
      state.capabilities.slots observer slot = some cap := by
  simp only [row, Capability.capabilitySpace, List.mem_map, List.mem_range] at hmem
  obtain ⟨slot, hin, hslot⟩ := hmem
  exact ⟨slot, hin, hslot⟩

theorem Issued.row {state : CompositeState} (hissued : Issued state) {observer : Nat}
    {cap : Capability.Capability} (hmem : some cap ∈ row state observer) :
    cap.identity < state.capabilities.nextIdentity := by
  obtain ⟨slot, hslot⟩ := mem_row_slot hmem
  exact hissued.slots observer slot cap hslot

/-! ## The frame of a step -/

/-- A step that extends the derivation history, keeps every pending sealed
transfer, and changes the view of no object the observer does not name
afterwards. -/
structure Frame (observer : Nat) (before after : CompositeState) : Prop where
  extends_ : ∀ index, index < before.capabilities.nextIdentity →
    after.capabilities.derivations index = before.capabilities.derivations index
  pending : after.transfers.pending = before.transfers.pending
  objects : ∀ object, Names after observer object = false →
    objectView after object = objectView before object

theorem Frame.lineage {observer before after} (hframe : Frame observer before after)
    (hissued : Issued before) (identity : Nat)
    (hlt : identity < before.capabilities.nextIdentity) :
    CompositeFullView.lineage after.capabilities identity =
      CompositeFullView.lineage before.capabilities identity :=
  lineage_of_extends _ _ hissued.precede hframe.extends_ identity hlt

theorem carriedView_frame {observer before after} (hframe : Frame observer before after)
    (hissued : Issued before) (endpoint : Nat) (transfer : CapabilityTransfer.Sealed)
    (hpending : before.transfers.pending endpoint = some transfer) :
    carriedView after transfer =
      { carriedView before transfer with view := objectView after transfer.object } := by
  simp only [carriedView, hframe.pending]
  rw [hframe.lineage hissued _ (hissued.pending endpoint transfer hpending)]
  congr 1
  cases hnested : before.transfers.pending transfer.object with
  | none => rfl
  | some nested =>
      simp only [Option.map_some]
      rw [hframe.lineage hissued _ (hissued.pending _ nested hnested)]

/-- **The frame rule for the full view.**  When a step of each run is a
`Frame`, the observer's row afterwards holds only capabilities it held before,
and the views agree afterwards, the authority agrees afterwards. -/
theorem extra_of_frame {observer : Nat} {left right left' right' : CompositeState}
    (hlow : LowEquiv observer left right) (hextra : extra observer left = extra observer right)
    (hissuedL : Issued left) (hissuedR : Issued right)
    (hframeL : Frame observer left left') (hframeR : Frame observer right right')
    (hrow : ∀ cap, some cap ∈ row left' observer → some cap ∈ row left observer)
    (hlow' : LowEquiv observer left' right') :
    extra observer left' = extra observer right' := by
  apply extra_of_pointwise hlow'.rowEq
  intro cap hmem'
  have hmem := hrow cap hmem'
  have hmemR : some cap ∈ row right observer := hlow.rowEq ▸ hmem
  have hbefore := extra_pointwise hlow hextra cap hmem
  have hpendingEq : left.transfers.pending cap.object = right.transfers.pending cap.object :=
    congrArg ObjectView.sealed (hlow.namedView cap.object (names_of_mem hmem))
  simp only [slotExtra, SlotExtra.mk.injEq] at hbefore ⊢
  obtain ⟨hlineage, hcarried⟩ := hbefore
  refine ⟨?_, ?_⟩
  · rw [hframeL.lineage hissuedL _ (hissuedL.row hmem),
      hframeR.lineage hissuedR _ (hissuedR.row hmemR)]
    exact hlineage
  · rw [hframeL.pending, hframeR.pending, ← hpendingEq]
    rw [← hpendingEq] at hcarried
    cases hpending : left.transfers.pending cap.object with
    | none => rfl
    | some transfer =>
        have hpendingR : right.transfers.pending cap.object = some transfer :=
          hpendingEq ▸ hpending
        simp only [hpending, Option.map_some, Option.some.injEq] at hcarried ⊢
        rw [carriedView_frame hframeL hissuedL _ transfer hpending,
          carriedView_frame hframeR hissuedR _ transfer hpendingR, hcarried]
        simp only [CarriedView.mk.injEq, true_and, and_true]
        cases hnamed : Names left' observer transfer.object with
        | true => exact hlow'.namedView transfer.object hnamed
        | false =>
            have hnamedR : Names right' observer transfer.object = false :=
              (hlow'.namesEq transfer.object) ▸ hnamed
            rw [hframeL.objects _ hnamed, hframeR.objects _ hnamedR]
            exact congrArg CarriedView.view hcarried

/-- A step that keeps the whole capability store and every pending transfer,
and changes no object view the observer does not name afterwards, is a frame
step. -/
theorem frame_of_unchanged {observer : Nat} {before after : CompositeState}
    (hcaps : after.capabilities = before.capabilities)
    (hpending : after.transfers.pending = before.transfers.pending)
    (hobjects : ∀ object, Names after observer object = false →
      objectView after object = objectView before object) :
    Frame observer before after :=
  { extends_ := fun index _ => by rw [hcaps]
    pending := hpending
    objects := hobjects }

theorem frame_refl (observer : Nat) (state : CompositeState) : Frame observer state state :=
  frame_of_unchanged rfl rfl fun _ _ => rfl

theorem row_sub_of_eq {observer : Nat} {before after : CompositeState}
    (hrow : row after observer = row before observer) :
    ∀ cap, some cap ∈ row after observer → some cap ∈ row before observer := by
  intro cap hmem
  rw [hrow] at hmem
  exact hmem

/-! ## Steps that change no object -/

/-- A step that keeps the capability store, every pending transfer and every
object view. -/
structure Unchanged (before after : CompositeState) : Prop where
  capabilities : after.capabilities = before.capabilities
  pending : after.transfers.pending = before.transfers.pending
  objects : ∀ object, objectView after object = objectView before object

theorem Unchanged.frame {before after : CompositeState} (h : Unchanged before after)
    (observer : Nat) : Frame observer before after :=
  frame_of_unchanged h.capabilities h.pending fun object _ => h.objects object

theorem Unchanged.row {before after : CompositeState} (h : Unchanged before after)
    (observer : Nat) : row after observer = row before observer := by
  simp only [CompositeObservation.row, h.capabilities]

theorem unchanged_refl (state : CompositeState) : Unchanged state state :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem unchanged_of_fields {before after : CompositeState}
    (hcaps : after.capabilities = before.capabilities)
    (hmailbox : after.ipc.endpoints.mailbox = before.ipc.endpoints.mailbox)
    (hpending : after.transfers.pending = before.transfers.pending)
    (hblockingMailbox : after.blockingIPC.mailbox = before.blockingIPC.mailbox)
    (hwaiters : after.blockingIPC.waiters = before.blockingIPC.waiters)
    (hmemory : after.virtualMemory.memory = before.virtualMemory.memory) :
    Unchanged before after :=
  ⟨hcaps, hpending, fun object => by
    simp only [objectView, backing, hcaps, hmailbox, hpending, hblockingMailbox, hwaiters,
      hmemory]⟩

/-- The projections an object view reads. -/
def objectProjections : List CompositeFootprint.Projection :=
  [.capabilities, .virtualMemory, .ipc, .transfers, .blockingIPC]

theorem unchanged_of_projections {before after : CompositeState}
    (same : ∀ projection, projection ∈ objectProjections →
      after.project projection = before.project projection) :
    Unchanged before after := by
  have hcaps : after.capabilities = before.capabilities := same .capabilities (by decide)
  have hvirtual : after.virtualMemory = before.virtualMemory := same .virtualMemory (by decide)
  have hipc : after.ipc = before.ipc := same .ipc (by decide)
  have htransfers : after.transfers = before.transfers := same .transfers (by decide)
  have hblocking : after.blockingIPC = before.blockingIPC := same .blockingIPC (by decide)
  exact unchanged_of_fields hcaps (by rw [hipc]) (by rw [htransfers]) (by rw [hblocking])
    (by rw [hblocking]) (by rw [hvirtual])

theorem unchanged_apply_of_untouched (state : CompositeState) (operation : Operation)
    (untouched : ∀ projection, projection ∈ objectProjections →
      CompositeFootprint.Untouched operation.footprint projection) :
    Unchanged state (applyOperation state operation) :=
  unchanged_of_projections fun projection hmem =>
    applyOperation_project_untouched state operation projection (untouched projection hmem)

theorem unchanged_selectLiveReturnAuthority (state : CompositeState)
    (purpose : Interrupt.ReturnPurpose) :
    Unchanged state (selectLiveReturnAuthority state purpose) :=
  unchanged_of_projections fun projection hmem =>
    selectLiveReturnAuthority_frames state purpose projection (by
      simp only [objectProjections, List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with h | h | h | h | h <;> subst h <;> untouched_decide)

theorem unchanged_trans {a b c : CompositeState} (hab : Unchanged a b) (hbc : Unchanged b c) :
    Unchanged a c :=
  ⟨hbc.capabilities.trans hab.capabilities, hbc.pending.trans hab.pending,
    fun object => (hbc.objects object).trans (hab.objects object)⟩

/-- Republishing a resumable bank whose lifecycle differs only in the scheduled
subject, and whose translation is the published one, changes no object. -/
theorem unchanged_installResumable (state : CompositeState)
    (resumable : ResumablePreemption.State)
    (hcaps : resumable.scheduler.lifecycle.capabilities = state.capabilities)
    (hvirtual : resumable.translations.virtual = state.virtualMemory) :
    Unchanged state (installResumable state resumable) := by
  apply unchanged_of_fields <;> simp only [installResumable, hcaps, hvirtual]

theorem unchanged_execution (state : CompositeState) (execution : FailStop.State) :
    Unchanged state { state with execution } :=
  unchanged_of_fields rfl rfl rfl rfl rfl rfl

theorem map_memory (virtualMemory : VirtualMapping.State) actor slot space page permissions :
    (VirtualMapping.map virtualMemory actor slot space page permissions).state.memory =
      virtualMemory.memory := by
  simp only [VirtualMapping.map]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]

theorem unmap_memory (virtualMemory : VirtualMapping.State) actor space page :
    (VirtualMapping.unmap virtualMemory actor space page).state.memory =
      virtualMemory.memory := by
  simp only [VirtualMapping.unmap]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]

theorem protect_memory (translations : TLB.State) actor space page permissions :
    (TLB.protect translations actor space page permissions).state.virtual.memory =
      translations.virtual.memory := by
  simp only [TLB.protect]
  repeat' split
  all_goals simp_all [TLB.invalidatePage, VirtualMapping.setMapping]

theorem syscall_memory (virtualMemory : VirtualMapping.State)
    (context : Syscall.TrustedContext) (call : Syscall.UntrustedCall) :
    (Syscall.dispatch virtualMemory context call).state.memory = virtualMemory.memory := by
  simp only [Syscall.dispatch]
  split
  · rfl
  · rename_i decoded _
    cases decoded with
    | map handleWord page permissions =>
        simp only [Syscall.dispatchDecoded]
        split
        · rfl
        · exact map_memory _ _ _ _ _ _
    | unmap page => exact unmap_memory _ _ _ _
    | access page access =>
        simp only [Syscall.dispatchDecoded]
        split <;> rfl

theorem unchanged_installVirtualMemory (state : CompositeState)
    (virtualMemory : VirtualMapping.State) (translations : TLB.State)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory) :
    Unchanged state (installVirtualMemory state virtualMemory translations) := by
  apply unchanged_of_fields <;> simp only [installVirtualMemory, hmemory]

/-- Operations that change no object, whoever performs them. -/
def unchangedFamily : Operation → Bool
  | .nmi _ _ | .selectUserReturn _ | .userReturn _ | .restart => true
  | .syscall _ | .map _ _ _ | .unmap _ | .protect _ _ => true
  | .resumePreempt _ _ => true
  | .scheduleAdd _ | .scheduleRemove _ | .scheduleNext | .scheduleYield | .scheduleTick => true
  | _ => false

theorem unchanged_apply (state : CompositeState) (hcoherent : state.Coherent)
    (operation : Operation) (hfamily : unchangedFamily operation = true) :
    Unchanged state (applyOperation state operation) := by
  cases operation with
  | nmi raw context =>
      exact unchanged_apply_of_untouched state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | selectUserReturn purpose =>
      exact unchanged_apply_of_untouched state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | userReturn request =>
      exact unchanged_apply_of_untouched state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | restart =>
      exact unchanged_apply_of_untouched state _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide)
  | syscall call =>
      simp only [applyOperation]
      split
      · exact unchanged_refl state
      · split
        · exact unchanged_selectLiveReturnAuthority state _
        · exact unchanged_trans (unchanged_installVirtualMemory state _ _
            (syscall_memory _ _ _)) (unchanged_selectLiveReturnAuthority _ _)
        · exact unchanged_trans (unchanged_installVirtualMemory state _ _
            (syscall_memory _ _ _)) (unchanged_selectLiveReturnAuthority _ _)
  | map slot page permissions =>
      simp only [applyOperation]
      split
      · exact unchanged_refl state
      · exact unchanged_installVirtualMemory state _ _ (map_memory _ _ _ _ _ _)
  | unmap page =>
      simp only [applyOperation]
      split
      · exact unchanged_refl state
      · exact unchanged_installVirtualMemory state _ _ (unmap_memory _ _ _ _)
  | protect page permissions =>
      simp only [applyOperation]
      split
      · exact unchanged_refl state
      · exact unchanged_installVirtualMemory state _ _ (by
          rw [protect_memory, translations_eq hcoherent])
  | resumePreempt frame registers =>
      simp only [applyOperation]
      generalize houtcome : ResumablePreemption.switch state.resumable state.execution.core frame
        registers = outcome
      rcases outcome with ⟨resumable, restored, error⟩
      cases error with
      | none =>
          simp only
          cases restored with
          | none =>
              have := CompositeOwnSwitch.switch_restored_of_error state.resumable
                state.execution.core frame registers (by rw [houtcome])
              rw [houtcome] at this
              simp at this
          | some context =>
              obtain ⟨hlifecycle, hvirtual⟩ := CompositeOwnSwitch.switch_success_state
                state.resumable state.execution.core frame registers context (by rw [houtcome])
              rw [houtcome] at hlifecycle hvirtual
              simp only at hlifecycle hvirtual
              apply unchanged_installResumable state _
              · rw [hlifecycle, resumable_lifecycle hcoherent, capabilities_eq_lifecycle hcoherent]
              · rw [hvirtual, translations_eq hcoherent]
      | some error =>
          obtain ⟨hscheduler, htranslations⟩ := CompositeLocalRespect.switch_error_frame
            state.resumable state.execution.core frame registers (by rw [houtcome]; rfl)
          rw [houtcome] at hscheduler htranslations
          simp only at hscheduler htranslations
          simp only
          split
          · split
            · exact unchanged_trans (unchanged_execution state _)
                (unchanged_installResumable _ resumable
                  (by rw [hscheduler, resumable_lifecycle hcoherent,
                    capabilities_eq_lifecycle hcoherent])
                  (by rw [htranslations, translations_eq hcoherent]))
            · exact unchanged_refl state
          · exact unchanged_refl state
          · rename_i hnone
            cases hnone
  | scheduleAdd subject =>
      simp only [applyOperation]
      split
      · exact unchanged_refl state
      · exact unchanged_of_fields rfl rfl rfl rfl rfl rfl
  | scheduleRemove subject =>
      simp only [applyOperation]
      split
      · exact unchanged_refl state
      · exact unchanged_of_fields rfl rfl rfl rfl rfl rfl
  | scheduleNext => rw [apply_scheduleNext]; exact unchanged_refl state
  | scheduleYield => rw [apply_scheduleYield]; exact unchanged_refl state
  | scheduleTick => rw [apply_scheduleTick]; exact unchanged_refl state
  | _ => simp [unchangedFamily] at hfamily

/-- An interrupt that contains no scheduled subject changes no object. -/
theorem unchanged_apply_interrupt (state : CompositeState) (hcoherent : state.Coherent)
    (frame : Interrupt.HardwareFrame)
    (hsilent : CompositeLocalRespect.interruptSilent state frame = true) :
    Unchanged state (applyOperation state (.interrupt frame)) := by
  unfold CompositeLocalRespect.interruptSilent at hsilent
  simp only [applyOperation]
  split
  · rename_i subject haction
    simp only [haction, bne_iff_ne, ne_eq] at hsilent
    simp only [hsilent, ↓reduceIte]
    exact unchanged_refl state
  · exact unchanged_trans (unchanged_execution state _)
      (unchanged_installResumable _ _
        (by simp only [resumable_lifecycle hcoherent, capabilities_eq_lifecycle hcoherent])
        (by simp only [translations_eq hcoherent]))
  · exact unchanged_execution state _
  · exact unchanged_execution state _
  · exact unchanged_execution state _
  · exact unchanged_refl state

/-! ## Steps that change only objects the actor names -/

theorem names_eq_of_capabilities {before after : CompositeState}
    (hcaps : after.capabilities = before.capabilities) (observer object : Nat) :
    Names after observer object = Names before observer object := by
  simp only [Names, CompositeObservation.row, hcaps]

/-- A step that keeps the capability store and every pending transfer and
changes the view of at most one object, which the observer names, is a frame
step for it. -/
theorem frame_of_target {observer : Nat} {before after : CompositeState}
    (hcaps : after.capabilities = before.capabilities)
    (hpending : after.transfers.pending = before.transfers.pending)
    (target : Option Nat)
    (htarget : ∀ object, target = some object → Names before observer object = true)
    (hobjects : ∀ object, target ≠ some object →
      objectView after object = objectView before object) :
    Frame observer before after := by
  apply frame_of_unchanged hcaps hpending
  intro object hnames
  apply hobjects
  intro htargetEq
  rw [names_eq_of_capabilities hcaps, htarget object htargetEq] at hnames
  cases hnames

theorem ipcTarget_named {state : CompositeState} (hcoherent : state.Coherent)
    (call : IPCSyscall.Call) (object : Nat) (htarget : ipcTarget state call = some object) :
    Names state (actor state) object = true := by
  have hcaps := (ipcCapabilitiesPublished_of_coherent hcoherent).1
  have key : ∀ word, (match CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
      { caller := actor state } word .endpoint with
      | .ok resolution => some resolution.capability.object
      | .error _ => none) = some object → Names state (actor state) object = true := by
    intro word hword
    split at hword
    · rename_i resolution hresolve
      simp only [Option.some.injEq] at hword
      subst hword
      have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
      rw [hcaps] at hlookup
      exact names_of_lookup state _ _ _ hlookup
    · cases hword
  cases call <;> exact key _ htarget

theorem objectView_installIPC (state : CompositeState) (ipc : IPCSyscall.State)
    (object : Nat) :
    objectView (installIPC state ipc) object =
      { objectView state object with mailbox := ipc.endpoints.mailbox object } := rfl

/-- Data IPC of the scheduled subject is a frame step for it. -/
theorem frame_apply_ipc (state : CompositeState) (hcoherent : state.Coherent)
    (call : IPCSyscall.Call) :
    Frame (actor state) state (applyOperation state (.ipc call)) ∧
      (applyOperation state (.ipc call)).capabilities = state.capabilities := by
  have hinstall : ∀ ipc : IPCSyscall.State,
      (∀ object, ipcTarget state call ≠ some object →
        ipc.endpoints.mailbox object = state.ipc.endpoints.mailbox object) →
      Frame (actor state) state (installIPC state ipc) ∧
        (installIPC state ipc).capabilities = state.capabilities := by
    intro ipc hmailbox
    refine ⟨frame_of_target rfl rfl (ipcTarget state call)
      (ipcTarget_named hcoherent call) ?_, rfl⟩
    intro object hne
    rw [objectView_installIPC, hmailbox object hne]
    rfl
  have hdispatch := hinstall _ fun object hne => ipcDispatch_mailbox_other state call object hne
  cases call with
  | send handleWord word0 word1 =>
      simp only [applyOperation, dispatchIPC]
      split
      all_goals first | exact ⟨frame_refl _ _, rfl⟩ | exact hdispatch
  | receive handleWord =>
      simp only [applyOperation]
      split
      all_goals first | exact ⟨frame_refl _ _, rfl⟩ | skip
      all_goals
        rename_i heq
        simp only [dispatchIPC] at heq ⊢
        repeat' split
        all_goals first | exact ⟨frame_refl _ _, rfl⟩ | exact hdispatch | skip
        all_goals simp_all

/-! ## Direct revocation -/

theorem objectView_installCopiedCapabilities (state : CompositeState)
    (capabilities : Capability.State) (object : Nat) :
    objectView (installCopiedCapabilities state capabilities) object =
      { objectView state object with
        live := capabilities.objects object
        kind := capabilities.kinds object } := rfl

theorem revokeRuntimeSafe_store (a : Capability.State) actor authoritySlot victim victimSlot :
    let next := (Capability.revokeRuntimeSafe a actor authoritySlot victim victimSlot).state
    next.derivations = a.derivations ∧ next.nextIdentity = a.nextIdentity ∧
      next.objects = a.objects ∧ next.kinds = a.kinds ∧
      ∀ subject slot cap, next.slots subject slot = some cap → a.slots subject slot = some cap := by
  simp only [Capability.revokeRuntimeSafe, Capability.revoke]
  repeat' split
  all_goals simp_all [Capability.reject, Capability.clear]
  all_goals
    intro subject slot cap
    split
    · simp
    · exact id

theorem revokeRuntimeSafe_store_capacity (a : Capability.State) actor authoritySlot victim
    victimSlot :
    (Capability.revokeRuntimeSafe a actor authoritySlot victim victimSlot).state.slotCapacity =
      a.slotCapacity := by
  simp only [Capability.revokeRuntimeSafe, Capability.revoke]
  repeat' split
  all_goals simp_all [Capability.reject, Capability.clear]

/-- Direct revocation is a frame step that only removes capabilities. -/
theorem frame_apply_revoke (observer : Nat) (state : CompositeState)
    (authoritySlot victim victimSlot : Nat) :
    let after := applyOperation state (.capabilityRevoke authoritySlot victim victimSlot)
    Frame observer state after ∧
      (∀ cap, some cap ∈ row after observer → some cap ∈ row state observer) := by
  intro after
  simp only [after, applyOperation]
  split
  · exact ⟨frame_refl _ _, fun _ h => h⟩
  · obtain ⟨hderivations, _, hobjects, hkinds, hslots⟩ := revokeRuntimeSafe_store
      state.capabilities state.execution.core.context.currentSubject authoritySlot victim
      victimSlot
    refine ⟨⟨fun index _ => by simp only [installCopiedCapabilities, hderivations], rfl,
      fun object _ => by rw [objectView_installCopiedCapabilities, hobjects, hkinds]; rfl⟩, ?_⟩
    intro cap hmem
    obtain ⟨slot, hslot⟩ := mem_row_slot hmem
    have hbefore := hslots observer slot cap hslot
    simp only [CompositeObservation.row, Capability.capabilitySpace, List.mem_map,
      List.mem_range] at hmem ⊢
    obtain ⟨index, hindex, hcap⟩ := hmem
    refine ⟨index, ?_, hslots observer index cap hcap⟩
    have hcapacity := (revokeRuntimeSafe_store_capacity state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot)
    simpa [installCopiedCapabilities, hcapacity] using hindex

/-! ## Blocking IPC -/

theorem send_objects (blocking : BlockingIPC.State) caller slot payload
    (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap) (object : Nat) (hne : object ≠ cap.object) :
    (BlockingIPC.send blocking caller slot payload).state.mailbox object =
        blocking.mailbox object ∧
      (BlockingIPC.send blocking caller slot payload).state.waiters object =
        blocking.waiters object := by
  simp only [BlockingIPC.send, hlookup]
  repeat' split
  all_goals simp_all [BlockingIPC.reject, BlockingIPC.setMailbox, BlockingIPC.wakeState,
    BlockingIPC.setWaiters]

theorem receiveOrBlock_objects (blocking : BlockingIPC.State) caller slot
    (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap) (object : Nat) (hne : object ≠ cap.object) :
    (BlockingIPC.receiveOrBlock blocking caller slot).state.mailbox object =
        blocking.mailbox object ∧
      (BlockingIPC.receiveOrBlock blocking caller slot).state.waiters object =
        blocking.waiters object := by
  simp only [BlockingIPC.receiveOrBlock, hlookup]
  repeat' split
  all_goals simp_all [BlockingIPC.rejectReceive, BlockingIPC.setMailbox, BlockingIPC.blockState,
    BlockingIPC.setWaiters, BlockingIPC.setCompletion]

theorem objectView_publishBlocking (state : CompositeState) (blocking : BlockingIPCContext.State)
    (object : Nat) :
    objectView (publishBlockingIPCContext state blocking) object =
      { objectView state object with
        blockingMailbox := blocking.ipc.mailbox object
        waiters := blocking.ipc.waiters object } := rfl

/-- Publishing a blocking store that agrees off one object the actor names is
a frame step. -/
theorem frame_publishBlocking {observer : Nat} (state : CompositeState)
    (blocking : BlockingIPCContext.State) (endpoint : Nat)
    (hnames : Names state observer endpoint = true)
    (hobjects : ∀ object, object ≠ endpoint →
      blocking.ipc.mailbox object = state.blockingIPC.mailbox object ∧
        blocking.ipc.waiters object = state.blockingIPC.waiters object)
    (after : CompositeState)
    (hafter : ∀ object, objectView after object =
      objectView (publishBlockingIPCContext state blocking) object)
    (hcaps : after.capabilities = state.capabilities)
    (hpending : after.transfers.pending = state.transfers.pending) :
    Frame observer state after := by
  apply frame_of_target hcaps hpending (some endpoint)
    (fun object h => by cases h; exact hnames)
  intro object hne
  have hne' : object ≠ endpoint := fun h => hne (by rw [h])
  obtain ⟨hmailbox, hwaiters⟩ := hobjects object hne'
  rw [hafter, objectView_publishBlocking, hmailbox, hwaiters]
  rfl

/-- The scheduled subject's blocking send is a frame step for it. -/
theorem frame_dispatchBlockingSend (state : CompositeState)
    (hstate : AuthoritativeRuntimeWellFormed state) (handleWord word0 word1 : UInt64) :
    let after := (dispatchBlockingSend state handleWord word0 word1).state
    Frame (actor state) state after ∧ after.capabilities = state.capabilities := by
  intro after
  simp only [after, dispatchBlockingSend]
  split
  · exact ⟨frame_refl _ _, rfl⟩
  · rename_i resolution hresolve
    have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
    have hnames : Names state (actor state) resolution.capability.object = true := by
      have := hlookup
      rw [CompositeOwnBlocking.blockingCaps_eq hstate] at this
      exact names_of_lookup state _ _ _ this
    generalize houtcome : BlockingIPCContext.send state.blockingIPCContext
      state.execution.core.context.currentSubject resolution.handle.slot
      { word0, word1 } = outcome
    rcases outcome with ⟨next, result, released⟩
    have hobjects : result = .accepted → ∀ object, object ≠ resolution.capability.object →
        next.ipc.mailbox object = state.blockingIPC.mailbox object ∧
          next.ipc.waiters object = state.blockingIPC.waiters object := by
      intro haccepted object hne
      have hexact := (BlockingIPCContext.send_accepted_ipc_exact state.blockingIPCContext
        state.execution.core.context.currentSubject resolution.handle.slot { word0, word1 }
        (by rw [houtcome]; exact haccepted)).1
      rw [houtcome] at hexact
      simp only at hexact
      rw [hexact]
      exact send_objects state.blockingIPC _ _ _ _ hlookup object hne
    cases result with
    | ipcRejected reason => exact ⟨frame_refl _ _, rfl⟩
    | contextRejected reason => exact ⟨frame_refl _ _, rfl⟩
    | accepted =>
        cases released with
        | none =>
            exact ⟨frame_publishBlocking state next _ hnames (hobjects rfl) _
              (fun _ => rfl) rfl rfl, rfl⟩
        | some saved =>
            simp only
            split
            · exact ⟨frame_refl _ _, rfl⟩
            · rename_i published hpublished
              unfold publishReleasedBlockingContext at hpublished
              repeat' split at hpublished
              all_goals try contradiction
              simp only [Except.ok.injEq] at hpublished
              subst hpublished
              exact ⟨frame_publishBlocking state next _ hnames (hobjects rfl) _
                (fun _ => rfl) rfl rfl, rfl⟩

/-- The scheduled subject's blocking receive is a frame step for it. -/
theorem frame_dispatchBlockingReceive (state : CompositeState)
    (hstate : AuthoritativeRuntimeWellFormed state) (handleWord : UInt64)
    (frame : Interrupt.HardwareFrame) (registers : ResumableContext.Registers) :
    let after := (dispatchBlockingReceive state handleWord frame registers).state
    Frame (actor state) state after ∧ after.capabilities = state.capabilities := by
  intro after
  simp only [after, dispatchBlockingReceive]
  split
  · exact ⟨frame_refl _ _, rfl⟩
  · rename_i resolution hresolve
    have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
    have hnames : Names state (actor state) resolution.capability.object = true := by
      have := hlookup
      rw [CompositeOwnBlocking.blockingCaps_eq hstate] at this
      exact names_of_lookup state _ _ _ this
    generalize houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
      state.execution.core.context.currentSubject resolution.handle.slot
      (state.blockingSavedContext frame registers) = outcome
    rcases outcome with ⟨next, result⟩
    have hraw := receiveOrBlock_objects state.blockingIPC _ _ _ hlookup
    cases result with
    | contextRejected reason => exact ⟨frame_refl _ _, rfl⟩
    | completed result =>
        cases result with
        | rejected reason => exact ⟨frame_refl _ _, rfl⟩
        | delivered envelope =>
            have hexact := (BlockingIPCContext.receive_delivered_ipc_exact
              state.blockingIPCContext _ _ _ envelope (by rw [houtcome])).1
            rw [houtcome] at hexact
            simp only at hexact
            refine ⟨frame_publishBlocking state next _ hnames ?_ _ (fun _ => rfl) rfl rfl, rfl⟩
            intro object hne
            rw [hexact]
            exact hraw object hne
        | blocked =>
            have hexact := (BlockingIPCContext.receive_blocked_ipc_exact
              state.blockingIPCContext _ _ _ (by rw [houtcome])).1
            rw [houtcome] at hexact
            simp only at hexact
            have hobjects : ∀ object, object ≠ resolution.capability.object →
                next.ipc.mailbox object = state.blockingIPC.mailbox object ∧
                  next.ipc.waiters object = state.blockingIPC.waiters object := by
              intro object hne
              rw [hexact]
              exact hraw object hne
            simp only
            split
            · split
              · exact ⟨frame_refl _ _, rfl⟩
              · rename_i published hpublished
                unfold restoreBlockingPeer at hpublished
                repeat' split at hpublished
                all_goals try contradiction
                simp only [Except.ok.injEq] at hpublished
                subst hpublished
                exact ⟨frame_publishBlocking state next _ hnames hobjects _
                  (fun _ => rfl) rfl rfl, rfl⟩
            · exact ⟨frame_publishBlocking state next _ hnames hobjects _
                (fun _ => rfl) rfl rfl, rfl⟩

end LeanOS.CompositeFullView
