import LeanOS.CompositeFullSteps

/-!
# Observer isolation over the subject gate, every operation

The premise is `FullStep`: the observer is the scheduled subject of two
runtime-well-formed states that agree on its full view
(`CompositeFullView.FullLowEquiv`), on the fail-stop mode, and on the
declared public inputs: the identity counter and the scheduler's bookkeeping
(`CompositeOwnSwitch.KernelPublic`).

* **Step consistency** (`full_step`): every request the observer can make
  through `FailStop.subjectGate` leaves the two states fully low-equivalent.
* **Output consistency** (`full_output`): every request returns the same
  result in both, except a user return, whose result can differ only by
  whether the machine halts (the termination channel, excluded).

Nothing else is excluded: the remaining exclusions are timing, caches, device
reads and refinement to generated C or hardware, none of which the composite
state models.
-/
namespace LeanOS.CompositeFullIsolation

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeOwnSwitch
open LeanOS.CompositeOwnTermination
open LeanOS.CompositeSubjectGate
open LeanOS.CompositeFullView
open LeanOS.CompositeFullSteps
set_option linter.unusedSimpArgs false

/-- The premise of the full theorems. -/
structure FullStep (observer : Nat) (left right : CompositeState) : Prop where
  own : OwnStepCounter observer left right
  kernel : KernelPublic left right
  extra : extra observer left = extra observer right
  leftRuntime : AuthoritativeRuntimeWellFormed left
  rightRuntime : AuthoritativeRuntimeWellFormed right

theorem FullStep.ownStep {observer left right} (h : FullStep observer left right) :
    OwnStep observer left right := h.own.toOwnStep

theorem FullStep.full {observer left right} (h : FullStep observer left right) :
    FullLowEquiv observer left right :=
  fullLowEquiv_of h.own.low h.extra

theorem FullStep.agree {observer left right} (h : FullStep observer left right) :
    ExtraAgree observer left right :=
  agree_of_extra h.own.low h.extra

theorem FullStep.issuedLeft {observer left right} (h : FullStep observer left right) :
    Issued left := issued_of_runtime h.leftRuntime.left

theorem FullStep.issuedRight {observer left right} (h : FullStep observer left right) :
    Issued right := issued_of_runtime h.rightRuntime.left

theorem FullStep.carried {observer left right} (h : FullStep observer left right) :
    CarriedAgree observer left right := by
  intro object transfer hnames hpending
  exact (h.agree.named hnames hpending).2.1

/-! ## Generic shapes -/

/-- The view of a terminated observer adds nothing. -/
theorem extra_of_dead {observer : Nat} {state : CompositeState} {capacity : Nat}
    {completion : Option BlockingIPC.Completion}
    (hdead : observe observer state = deadView capacity completion) :
    extra observer state = List.replicate capacity none := by
  have hrow : row state observer = List.replicate capacity none := congrArg View.row hdead
  simp only [extra, hrow, List.map_replicate, Option.map_none]

/-- Step consistency on the full view from frame steps on each side. -/
theorem full_of_frames {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : Operation)
    (hframe : ∀ state : CompositeState, AuthoritativeRuntimeWellFormed state →
      state.lifecycle.current = some observer →
      Frame observer state (applyOperation state operation) ∧
        ∀ cap, some cap ∈ row (applyOperation state operation) observer →
          some cap ∈ row state observer)
    (hlow : LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state) :
    FullLowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  apply fullLowEquiv_of hlow
  have hside : ∀ state : CompositeState, AuthoritativeRuntimeWellFormed state →
      state.lifecycle.current = some observer →
      Frame observer state (authoritativeGate state (.ordinary operation)).state ∧
        ∀ cap, some cap ∈ row (authoritativeGate state (.ordinary operation)).state observer →
          some cap ∈ row state observer := by
    intro state hstate hcurrent
    rw [authoritativeGate_ordinary_state]
    rcases gate_state_cases state operation with hsame | happly
    · rw [hsame]; exact ⟨frame_refl _ _, fun _ hmem => hmem⟩
    · rw [happly]; exact hframe state hstate hcurrent
  obtain ⟨hframeL, hrowL⟩ := hside left h.leftRuntime h.own.current
  obtain ⟨hframeR, _⟩ := hside right h.rightRuntime h.ownStep.rightCurrent
  exact extra_of_frame h.own.low h.extra h.issuedLeft h.issuedRight hframeL hframeR hrowL hlow

theorem frame_of_unchangedApply {observer : Nat} (operation : Operation)
    (hunchanged : ∀ state : CompositeState, state.Coherent →
      Unchanged state (applyOperation state operation)) :
    ∀ state : CompositeState, AuthoritativeRuntimeWellFormed state →
      state.lifecycle.current = some observer →
      Frame observer state (applyOperation state operation) ∧
        ∀ cap, some cap ∈ row (applyOperation state operation) observer →
          some cap ∈ row state observer := by
  intro state hstate _
  have hU := hunchanged state (coherent_of hstate)
  exact ⟨hU.frame observer, row_sub_of_eq (hU.row observer)⟩

/-- In the running latch the ordinary gate applies the operation. -/
theorem gate_running {state : CompositeState} (hmode : state.execution.mode = .running)
    (operation : Operation) :
    (authoritativeGate state (.ordinary operation)).state = applyOperation state operation := by
  rw [authoritativeGate_ordinary_state]
  cases operation <;> simp [gate, hmode]

theorem issued_apply {state : CompositeState} (hstate : AuthoritativeRuntimeWellFormed state)
    (hmode : state.execution.mode = .running) (operation : Operation) :
    Issued (applyOperation state operation) := by
  have := issued_of_runtime
    (authoritativeGate_preserves_authoritativeRuntimeWellFormed state (.ordinary operation)
      hstate).left
  rwa [gate_running hmode] at this

/-- Step consistency from an `ExtraAgree` proof for `applyOperation`. -/
theorem full_of_agree {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : Operation)
    (hlow : LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state)
    (hagree : left.execution.mode = .running →
      ExtraAgree observer (applyOperation left operation) (applyOperation right operation)) :
    FullLowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  cases hmode : left.execution.mode with
  | running =>
      have hmodeR : right.execution.mode = .running := h.own.mode ▸ hmode
      have hlow' := hlow
      rw [gate_running hmode, gate_running hmodeR] at hlow' ⊢
      exact fullLowEquiv_of_agree hlow' (hagree hmode)
  | handling entry =>
      have hmodeR : right.execution.mode = .handling entry := h.own.mode ▸ hmode
      apply fullLowEquiv_of hlow
      have hlow'' := hlow
      rw [authoritativeGate_ordinary_state, authoritativeGate_ordinary_state] at hlow'' ⊢
      cases operation
      case nmi raw context =>
        -- Only an NMI is applied while handling, and it changes no object.
        have hl : (gate left (.nmi raw context)).state = applyOperation left (.nmi raw context) := by
          simp [gate, hmode]
        have hr : (gate right (.nmi raw context)).state =
            applyOperation right (.nmi raw context) := by
          simp [gate, hmodeR]
        rw [hl, hr] at hlow'' ⊢
        have hUL := unchanged_apply left (coherent_of h.leftRuntime) (.nmi raw context) rfl
        have hUR := unchanged_apply right (coherent_of h.rightRuntime) (.nmi raw context) rfl
        exact extra_of_frame h.own.low h.extra h.issuedLeft h.issuedRight
          (hUL.frame observer) (hUR.frame observer) (row_sub_of_eq (hUL.row observer)) hlow''
      all_goals (simp only [gate, hmode, hmodeR]; exact h.extra)
  | halted record =>
      apply fullLowEquiv_of hlow
      rw [authoritativeGate_ordinary_state, authoritativeGate_ordinary_state]
      have hmodeR : right.execution.mode = .halted record := h.own.mode ▸ hmode
      have hl : (gate left operation).state = left := by cases operation <;> simp [gate, hmode]
      have hr : (gate right operation).state = right := by cases operation <;> simp [gate, hmodeR]
      rw [hl, hr]; exact h.extra

/-- Step consistency from equal `extra` after `applyOperation`. -/
theorem full_of_extra {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : Operation)
    (hlow : LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state)
    (hextra : left.execution.mode = .running →
      extra observer (applyOperation left operation) =
        extra observer (applyOperation right operation)) :
    FullLowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  apply full_of_agree h operation hlow
  intro hmode
  have hmodeR : right.execution.mode = .running := h.own.mode ▸ hmode
  have hlow' := hlow
  rw [gate_running hmode, gate_running hmodeR] at hlow'
  exact agree_of_extra hlow' (hextra hmode)

/-- **Step consistency of every ordinary request of the observer on the full
view.**  Requests that name another subject are refused by the subject gate
(`CompositeSubjectGate.own_step_cross`); receipt also needs the subject gate's
nested-transfer refusal (`NestedFree`). -/
theorem full_ordinary {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : Operation)
    (hcross : crossTarget observer (.ordinary operation) = false)
    (hfree : ∀ endpointWord destinationSlot,
      operation = .transferAccept endpointWord destinationSlot →
      left.execution.mode = .running → NestedFree left endpointWord) :
    FullLowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  have hO := h.ownStep
  have hcohL := coherent_of h.leftRuntime
  have hcohR := coherent_of h.rightRuntime
  have hunchanged : ∀ (operation : Operation), unchangedFamily operation = true →
      LowEquiv observer (authoritativeGate left (.ordinary operation)).state
        (authoritativeGate right (.ordinary operation)).state →
      FullLowEquiv observer (authoritativeGate left (.ordinary operation)).state
        (authoritativeGate right (.ordinary operation)).state := by
    intro operation hfamily hlow
    exact full_of_frames h operation (frame_of_unchangedApply operation fun state hcoherent =>
      unchanged_apply state hcoherent operation hfamily) hlow
  have hcounter : ∀ (operation : Operation), ownStepConsistentCounter observer operation = true →
      LowEquiv observer (authoritativeGate left (.ordinary operation)).state
        (authoritativeGate right (.ordinary operation)).state :=
    fun operation hfamily => own_step_consistent_counter h.own operation hfamily
  cases operation with
  | nmi raw context => exact hunchanged _ rfl (hcounter _ rfl)
  | selectUserReturn purpose => exact hunchanged _ rfl (hcounter _ rfl)
  | userReturn request => exact hunchanged _ rfl (hcounter _ rfl)
  | restart => exact hunchanged _ rfl (hcounter _ rfl)
  | syscall call => exact hunchanged _ rfl (hcounter _ rfl)
  | map slot page permissions => exact hunchanged _ rfl (hcounter _ rfl)
  | unmap page => exact hunchanged _ rfl (hcounter _ rfl)
  | protect page permissions => exact hunchanged _ rfl (hcounter _ rfl)
  | scheduleAdd subject => exact hunchanged _ rfl (hcounter _ rfl)
  | scheduleRemove subject => exact hunchanged _ rfl (hcounter _ rfl)
  | scheduleNext => exact hunchanged _ rfl (hcounter _ rfl)
  | scheduleYield => exact hunchanged _ rfl (hcounter _ rfl)
  | scheduleTick => exact hunchanged _ rfl (hcounter _ rfl)
  | resumePreempt frame registers =>
      exact hunchanged _ rfl (own_step_resumePreempt hO h.kernel frame registers)
  | ipc call =>
      apply full_of_frames h _ _ (hcounter _ rfl)
      intro state hstate hcurrent
      have hactor : actor state = observer := (actor_of_current (coherent_of hstate) hcurrent).1
      obtain ⟨hframe, hcaps⟩ := frame_apply_ipc state (coherent_of hstate) call
      rw [hactor] at hframe
      exact ⟨hframe, row_sub_of_eq (by simp only [CompositeObservation.row, hcaps])⟩
  | capabilityRevoke authoritySlot victim victimSlot =>
      apply full_of_frames h _ _ (hcounter _ rfl)
      intro state _ _
      exact frame_apply_revoke observer state authoritySlot victim victimSlot
  | capabilityCopy source destination destinationSlot rights =>
      have hdest : destination = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hdest
      apply full_of_agree h _ (hcounter _ (by simp [ownStepConsistentCounter]))
      intro hmode
      have hmodeR : right.execution.mode = .running := h.own.mode ▸ hmode
      exact agree_copy_self h.own h.agree h.issuedLeft h.issuedRight source destinationSlot
        rights (issued_apply h.leftRuntime hmode _).precede
        (issued_apply h.rightRuntime hmodeR _).precede
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      have hlow := hcounter (.transferOffer endpointWord sourceWord sourceKind payload rights) rfl
      apply full_of_agree h _ hlow
      intro hmode
      have hmodeR : right.execution.mode = .running := h.own.mode ▸ hmode
      have hlow' := hlow
      rw [gate_running hmode, gate_running hmodeR] at hlow'
      exact agree_offer h.own h.agree h.issuedLeft h.issuedRight endpointWord sourceWord
        sourceKind payload rights (issued_apply h.leftRuntime hmode _).precede
        (issued_apply h.rightRuntime hmodeR _).precede hlow'
  | transferAccept endpointWord destinationSlot =>
      have hlow := own_step_accept_gate hO h.carried endpointWord destinationSlot
      apply full_of_agree h _ hlow
      intro hmode
      have hmodeR : right.execution.mode = .running := h.own.mode ▸ hmode
      have hlow' := hlow
      rw [gate_running hmode, gate_running hmodeR] at hlow'
      exact agree_accept hO h.agree endpointWord destinationSlot
        (hfree endpointWord destinationSlot rfl hmode) hlow' h.issuedLeft h.issuedRight
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      have hvictim : victim = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hvictim
      have happly : FullLowEquiv victim
          (applyOperation left (.capabilityRevokeSubtree authoritySlot victim victimSlot))
          (applyOperation right (.capabilityRevokeSubtree authoritySlot victim victimSlot)) := by
        rcases apply_revokeSubtree_self hO authoritySlot victimSlot with ⟨hl, hr⟩ | ⟨root, hl, hr⟩
        · rw [hl, hr]; exact h.full
        · rw [hl, hr]
          obtain ⟨hlow, hagree⟩ := full_revoked hO h.agree h.issuedLeft h.issuedRight root
          exact fullLowEquiv_of_agree hlow hagree
      apply full_of_agree h _ (lowEquiv_gate_of_apply h.own.low h.own.mode happly.low)
      intro _
      exact happly.agree
  | createSubject subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      apply full_of_extra h _ (hcounter _ (by simp [ownStepConsistentCounter]))
      intro _
      rw [apply_create_self h.leftRuntime.left h.own.current,
        apply_create_self h.rightRuntime.left hO.rightCurrent]
      exact h.extra
  | terminateSubject subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      apply full_of_extra h _ (own_step_terminate_self hO h.leftRuntime h.rightRuntime)
      intro _
      rw [apply_terminate_self h.leftRuntime.left h.own.current,
        apply_terminate_self h.rightRuntime.left hO.rightCurrent,
        extra_of_dead (observe_installTerminatedSubject_self h.leftRuntime h.own.current),
        extra_of_dead (observe_installTerminatedSubject_self h.rightRuntime hO.rightCurrent),
        h.own.low.capacity]
  | terminateCurrent =>
      apply full_of_extra h _ (own_step_terminateCurrent hO h.leftRuntime h.rightRuntime)
      intro _
      rw [apply_terminateCurrent_self h.leftRuntime.left h.own.current,
        apply_terminateCurrent_self h.rightRuntime.left hO.rightCurrent,
        extra_of_dead (observe_installTerminatedSubject_self h.leftRuntime h.own.current),
        extra_of_dead (observe_installTerminatedSubject_self h.rightRuntime hO.rightCurrent),
        h.own.low.capacity]
  | interrupt frame =>
      apply full_of_extra h _ (own_step_interrupt hO h.leftRuntime h.rightRuntime frame)
      intro hmode
      have hmodeR : right.execution.mode = .running := h.own.mode ▸ hmode
      have hlow := own_step_interrupt hO h.leftRuntime h.rightRuntime frame
      rw [gate_running hmode, gate_running hmodeR] at hlow
      have haction := dispatchHardware_action_eq left.execution right.execution frame h.own.mode
        (hO.leftActor.1.trans hO.rightActor.1.symm)
      have hdeadL := observe_apply_interrupt_own h.leftRuntime h.own.current frame
      have hdeadR := observe_apply_interrupt_own h.rightRuntime hO.rightCurrent frame
      rw [← haction] at hdeadR
      have hsilent : ∀ state : CompositeState, state.lifecycle.current = some observer →
          (dispatchHardware state.execution frame).action =
            (dispatchHardware left.execution frame).action →
          (∀ subject, (dispatchHardware left.execution frame).action = .contained subject →
            subject ≠ observer) →
          CompositeLocalRespect.interruptSilent state frame = true := by
        intro state hcurrent hsame hnot
        unfold CompositeLocalRespect.interruptSilent
        rw [hsame]
        split
        · rename_i subject hcontained
          simp only [hcurrent, bne_iff_ne, ne_eq, Option.some.injEq]
          exact fun heq => hnot subject hcontained heq.symm
        · rfl
      by_cases hself : (dispatchHardware left.execution frame).action = .contained observer
      · rw [hself] at hdeadL hdeadR
        simp only [h.own.current, hO.rightCurrent, ↓reduceIte] at hdeadL hdeadR
        rw [extra_of_dead hdeadL, extra_of_dead hdeadR, h.own.low.capacity]
      · have hnot : ∀ subject, (dispatchHardware left.execution frame).action =
            .contained subject → subject ≠ observer := by
          intro subject hcontained heq
          subst heq
          exact hself hcontained
        have hUL := unchanged_apply_interrupt left hcohL frame
          (hsilent left h.own.current rfl hnot)
        have hUR := unchanged_apply_interrupt right hcohR frame
          (hsilent right hO.rightCurrent haction.symm hnot)
        exact extra_of_frame h.own.low h.extra h.issuedLeft h.issuedRight (hUL.frame observer)
          (hUR.frame observer) (row_sub_of_eq (hUL.row observer)) hlow

/-! ## Blocking operations and drains -/

theorem full_blocking_frames {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : CompositeBlockingOperation)
    (hframe : ∀ state : CompositeState, AuthoritativeRuntimeWellFormed state →
      state.lifecycle.current = some observer →
      Frame observer state (applyBlockingOperation state operation) ∧
        (applyBlockingOperation state operation).capabilities = state.capabilities)
    (hlow : LowEquiv observer (authoritativeGate left (.blocking operation)).state
      (authoritativeGate right (.blocking operation)).state) :
    FullLowEquiv observer (authoritativeGate left (.blocking operation)).state
      (authoritativeGate right (.blocking operation)).state := by
  apply fullLowEquiv_of hlow
  have hside : ∀ state : CompositeState, AuthoritativeRuntimeWellFormed state →
      state.lifecycle.current = some observer →
      Frame observer state (authoritativeGate state (.blocking operation)).state ∧
        ∀ cap, some cap ∈ row (authoritativeGate state (.blocking operation)).state observer →
          some cap ∈ row state observer := by
    intro state hstate hcurrent
    rw [authoritativeGate_blocking_state]
    cases hmode : state.execution.mode with
    | running =>
        simp only [blockingGate, hmode]
        obtain ⟨hF, hcaps⟩ := hframe state hstate hcurrent
        exact ⟨hF, row_sub_of_eq (by simp only [CompositeObservation.row, hcaps])⟩
    | handling entry =>
        simp only [blockingGate, hmode]
        exact ⟨frame_refl _ _, fun _ hmem => hmem⟩
    | halted record =>
        simp only [blockingGate, hmode]
        exact ⟨frame_refl _ _, fun _ hmem => hmem⟩
  obtain ⟨hframeL, hrowL⟩ := hside left h.leftRuntime h.own.current
  obtain ⟨hframeR, _⟩ := hside right h.rightRuntime h.ownStep.rightCurrent
  exact extra_of_frame h.own.low h.extra h.issuedLeft h.issuedRight hframeL hframeR hrowL hlow

/-- **Step consistency of the observer's blocking requests on the full
view.** -/
theorem full_blocking {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : CompositeBlockingOperation)
    (hcross : crossTarget observer (.blocking operation) = false) :
    FullLowEquiv observer (authoritativeGate left (.blocking operation)).state
      (authoritativeGate right (.blocking operation)).state := by
  have hO := h.ownStep
  cases operation with
  | send handleWord word0 word1 =>
      apply full_blocking_frames h _ _
        (CompositeOwnBlocking.own_blockingSend hO h.leftRuntime h.rightRuntime h.kernel
          handleWord word0 word1).1
      intro state hstate hcurrent
      have hactor : actor state = observer :=
        (actor_of_current (coherent_of hstate) hcurrent).1
      have := frame_dispatchBlockingSend state hstate handleWord word0 word1
      rw [hactor] at this
      exact this
  | receive handleWord frame registers =>
      apply full_blocking_frames h _ _
        (CompositeOwnBlocking.own_blockingReceive hO h.leftRuntime h.rightRuntime h.kernel
          handleWord frame registers).1
      intro state hstate hcurrent
      have hactor : actor state = observer :=
        (actor_of_current (coherent_of hstate) hcurrent).1
      have := frame_dispatchBlockingReceive state hstate handleWord frame registers
      rw [hactor] at this
      exact this
  | cancel subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      apply full_blocking_frames h _ _
        (CompositeOwnBlocking.own_blockingCancel_self hO h.leftRuntime h.rightRuntime).1
      intro state hstate hcurrent
      simp only [applyBlockingOperation,
        CompositeOwnBlocking.dispatchBlockingCancel_self hstate hcurrent]
      exact ⟨frame_refl _ _, trivial⟩

/-- **The observer's drain of itself changes nothing.** -/
theorem full_drain_self {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) :
    FullLowEquiv observer (authoritativeGate left (.drainDeferred observer)).state
      (authoritativeGate right (.drainDeferred observer)).state := by
  rcases CompositeLocalRespect.authoritativeGate_drain_pair left right observer h.own.mode
    with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]; exact h.full
  · rw [hl, hr, CompositeLocalRespect.drain_self_rejected h.leftRuntime h.own.current,
      CompositeLocalRespect.drain_self_rejected h.rightRuntime h.ownStep.rightCurrent]
    exact h.full

/-! ## The subject gate -/

/-- The nested-transfer refusal reads the observer's handle, the transfer
pending on the endpoint it names, and the transfer pending on the object that
transfer carries: all in the full view. -/
theorem refusesNestedTransfer_congr {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : AuthoritativeOperation) :
    left.refusesNestedTransfer operation = right.refusesNestedTransfer operation := by
  have hO := h.ownStep
  cases operation with
  | ordinary operation =>
      cases operation with
      | transferAccept endpointWord destinationSlot =>
          obtain ⟨hLs, _⟩ := hO.leftActor
          obtain ⟨hRs, _⟩ := hO.rightActor
          have hcapsL := (transfers_published h.leftRuntime.left.1).1
          have hcapsR := (transfers_published h.rightRuntime.left.1).1
          simp only [CompositeState.refusesNestedTransfer, hLs, hRs, hcapsL, hcapsR, ← h.own.mode,
            h.own.low.resolveCurrent]
          split
          · split
            · rename_i resolution hresolve
              have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
              have hnamesR := names_of_lookup right observer _ _ hlookup
              have hnamesL : Names left observer resolution.capability.object = true := by
                rw [h.own.low.namesEq]; exact hnamesR
              have hpending := pending_of_view (h.own.low.namedView _ hnamesL)
              rw [hpending]
              cases hcase : right.transfers.pending resolution.capability.object with
              | none => rfl
              | some transfer =>
                  have hpendingL : left.transfers.pending resolution.capability.object =
                      some transfer := hpending.trans hcase
                  have hview := (h.agree.named hnamesL hpendingL).2.1
                  simp only [pending_of_view hview]
            · rfl
          · rfl
      | _ => rfl
  | blocking operation => rfl
  | drainDeferred subject => rfl

/-- **Step consistency over the subject gate, every request.**  The scheduled
observer's request leaves two fully low-equivalent states, agreeing on the
declared public inputs, fully low-equivalent. -/
theorem full_step {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : AuthoritativeOperation) :
    FullLowEquiv observer (subjectGate left operation).state
      (subjectGate right operation).state := by
  have hO := h.ownStep
  cases hcross : crossTarget observer operation
  · have hcrossL := refuses_own h.own.current operation hcross
    have hcrossR := refuses_own hO.rightCurrent operation hcross
    have hnested := refusesNestedTransfer_congr h operation
    cases hrefusedL : left.refusesNestedTransfer operation
    · have hrefusedR : right.refusesNestedTransfer operation = false := hnested ▸ hrefusedL
      rw [subjectGate_of_not_refused hcrossL hrefusedL,
        subjectGate_of_not_refused hcrossR hrefusedR]
      simp only
      cases operation with
      | ordinary operation =>
          apply full_ordinary h operation hcross
          intro endpointWord destinationSlot hop hmode
          subst hop
          exact nestedFree_of_not_refused hmode hrefusedL
      | blocking operation => exact full_blocking h operation hcross
      | drainDeferred subject =>
          have hsubject : subject = observer := by
            simpa [crossTarget, AuthoritativeOperation.target] using hcross
          subst hsubject
          exact full_drain_self h
    · have hrefusedR : right.refusesNestedTransfer operation = true := hnested ▸ hrefusedL
      have hL : left.refusal operation = some .nestedTransferRefused := by
        simp [CompositeState.refusal, hcrossL, hrefusedL]
      have hR : right.refusal operation = some .nestedTransferRefused := by
        simp [CompositeState.refusal, hcrossR, hrefusedR]
      rw [subjectGate_of_refusal hL, subjectGate_of_refusal hR]
      exact h.full
  · obtain ⟨hl, hr, _⟩ := own_cross_stutter hO operation hcross
    rw [hl, hr]
    exact h.full

/-! ## Output consistency -/

/-- **Output consistency of every ordinary request on the authoritative
gate**, except the user return (`own_output_userReturn`). -/
theorem output_ordinary {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : Operation)
    (hcross : crossTarget observer (.ordinary operation) = false)
    (hreturn : ∀ request, operation ≠ .userReturn request) :
    (authoritativeGate left (.ordinary operation)).result =
      (authoritativeGate right (.ordinary operation)).result := by
  have hO := h.ownStep
  have hcounter : ∀ (operation : Operation),
      ownOutputConsistentCounter observer operation = true →
      (authoritativeGate left (.ordinary operation)).result =
        (authoritativeGate right (.ordinary operation)).result :=
    fun operation hfamily => own_output_consistent_counter h.own operation hfamily
  have hscheduler : ∀ (operation : Operation), schedulerOutputConsistent operation = true →
      (authoritativeGate left (.ordinary operation)).result =
        (authoritativeGate right (.ordinary operation)).result :=
    fun operation hfamily => own_output_consistent_scheduler hO h.kernel.schedulerPublic
      operation hfamily
  cases operation with
  | interrupt frame => exact own_output_interrupt hO frame
  | nmi raw context => exact own_output_nmi hO raw context
  | selectUserReturn purpose => exact own_output_selectUserReturn hO purpose
  | userReturn request => exact absurd rfl (hreturn request)
  | syscall call => exact hcounter _ rfl
  | ipc call => exact hcounter _ rfl
  | map slot page permissions => exact hcounter _ rfl
  | unmap page => exact hcounter _ rfl
  | protect page permissions => exact hcounter _ rfl
  | restart => exact hcounter _ rfl
  | resumePreempt frame registers => exact own_output_resumePreempt hO h.kernel frame registers
  | transferOffer endpointWord sourceWord sourceKind payload rights => exact hcounter _ rfl
  | transferAccept endpointWord destinationSlot => exact hcounter _ rfl
  | capabilityCopy source destination destinationSlot rights =>
      have hdest : destination = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hdest
      exact hcounter _ (by simp [ownOutputConsistentCounter, ownOutputConsistent])
  | capabilityRevoke authoritySlot victim victimSlot =>
      have hvictim : victim = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hvictim
      exact hcounter _ (by simp [ownOutputConsistentCounter, ownOutputConsistent])
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      have hvictim : victim = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hvictim
      exact hcounter _ (by simp [ownOutputConsistentCounter])
  | createSubject subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      exact hcounter _ (by simp [ownOutputConsistentCounter])
  | terminateSubject subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      exact hcounter _ (by simp [ownOutputConsistentCounter])
  | scheduleAdd subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      apply authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.own.mode
      rw [CompositeOwnBlocking.reply_scheduleAdd_self h.leftRuntime h.own.current,
        CompositeOwnBlocking.reply_scheduleAdd_self h.rightRuntime hO.rightCurrent]
  | scheduleRemove subject => exact hscheduler _ rfl
  | scheduleNext => exact hcounter _ rfl
  | scheduleYield => exact hscheduler _ rfl
  | scheduleTick => exact hscheduler _ rfl
  | terminateCurrent => exact hcounter _ rfl

/-- Output consistency of every request on the authoritative gate, except the
user return. -/
theorem output_authoritative {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : AuthoritativeOperation)
    (hcross : crossTarget observer operation = false)
    (hreturn : ∀ request, operation ≠ .ordinary (.userReturn request)) :
    (authoritativeGate left operation).result = (authoritativeGate right operation).result := by
  have hO := h.ownStep
  cases operation with
  | ordinary operation =>
      exact output_ordinary h operation hcross fun request heq => hreturn request (by rw [heq])
  | blocking operation =>
      cases operation with
      | send handleWord word0 word1 =>
          exact (CompositeOwnBlocking.own_blockingSend hO h.leftRuntime h.rightRuntime h.kernel
            handleWord word0 word1).2
      | receive handleWord frame registers =>
          exact (CompositeOwnBlocking.own_blockingReceive hO h.leftRuntime h.rightRuntime
            h.kernel handleWord frame registers).2
      | cancel subject =>
          have hsubject : subject = observer := by
            simpa [crossTarget, AuthoritativeOperation.target] using hcross
          subst hsubject
          exact (CompositeOwnBlocking.own_blockingCancel_self hO h.leftRuntime
            h.rightRuntime).2
  | drainDeferred subject =>
      have hsubject : subject = observer := by
        simpa [crossTarget, AuthoritativeOperation.target] using hcross
      subst hsubject
      exact CompositeLocalRespect.own_output_drain_self hO h.leftRuntime h.rightRuntime

/-- **Output consistency over the subject gate, every request.**  A user
return is included when neither run halts: it is otherwise the termination
channel, which the claim excludes. -/
theorem full_output {observer : Nat} {left right : CompositeState}
    (h : FullStep observer left right) (operation : AuthoritativeOperation)
    (hcontinues : ∀ request, operation = .ordinary (.userReturn request) →
      Continues (subjectGate left operation).state ∧
        Continues (subjectGate right operation).state) :
    (subjectGate left operation).result = (subjectGate right operation).result := by
  have hO := h.ownStep
  cases hcross : crossTarget observer operation
  · have hcrossL := refuses_own h.own.current operation hcross
    have hcrossR := refuses_own hO.rightCurrent operation hcross
    have hnested := refusesNestedTransfer_congr h operation
    cases hrefusedL : left.refusesNestedTransfer operation
    · have hrefusedR : right.refusesNestedTransfer operation = false := hnested ▸ hrefusedL
      have hgateL := subjectGate_of_not_refused hcrossL hrefusedL
      have hgateR := subjectGate_of_not_refused hcrossR hrefusedR
      rw [hgateL, hgateR]
      simp only [SubjectGateResult.gate.injEq]
      by_cases hreturn : ∃ request, operation = .ordinary (.userReturn request)
      · obtain ⟨request, rfl⟩ := hreturn
        obtain ⟨hcontL, hcontR⟩ := hcontinues request rfl
        rw [hgateL] at hcontL
        rw [hgateR] at hcontR
        exact own_output_userReturn hO request hcontL hcontR
      · exact output_authoritative h operation hcross fun request heq =>
          hreturn ⟨request, heq⟩
    · have hrefusedR : right.refusesNestedTransfer operation = true := hnested ▸ hrefusedL
      have hL : left.refusal operation = some .nestedTransferRefused := by
        simp [CompositeState.refusal, hcrossL, hrefusedL]
      have hR : right.refusal operation = some .nestedTransferRefused := by
        simp [CompositeState.refusal, hcrossR, hrefusedR]
      rw [subjectGate_of_refusal hL, subjectGate_of_refusal hR]
  · exact own_output_cross hO operation hcross

end LeanOS.CompositeFullIsolation
