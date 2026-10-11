import LeanOS.CompositeSwitchedChannels

/-!
# Composite unwinding: the saved-register channel, closed

Until this module, three composite replies carried a complete saved context
of another subject, frame and registers included:

* the reply of a resumable switch (`resumePreempt`) carried the context it
  restored, which belongs to the next subject;
* the reply of a blocking send that woke a waiter carried the waiter's saved
  context;
* the reply of a wait cancellation carried the cancelled subject's saved
  context.

`#542` proved each one a channel (`resumePreempt_output_inconsistent`,
`blockingSend_output_inconsistent`, `blockingCancel_output_inconsistent`):
two states the observer cannot tell apart gave it different replies.

**Model artifact, not a binary leak.**  The booted kernel never returns a
saved context to the caller.  The timer path (`isr32` in `boot/boot.S`) and
the blocking send and block paths (`isr80`) save the outgoing subject's
twenty-word frame and copy the incoming subject's own complete twenty-word
frame (or a zeroed fresh one) over the return frame before `iretq`; the only
words written into another subject's return frame are the two payload words
the sender passed and the delivery flag.  The channel was in the model's typed
reply, which recorded the restored context as if it were returned.

**The fix.**  The replies now name a subject and nothing else
(`OperationReply.resume next`, `CompositeBlockingSendReply.woke receiver`,
`CompositeBlockingCancelReply.cancelled subject`).  The restored context is
kept by the kernel in the composite state and in the dispatch outcome's
`restored` field, never in the reply.  The named subject is public:

* after a switch it is the scheduled subject of the post-state
  (`resume_reply_names_scheduled`), which every observer view contains;
* a wake names the receiver it moved to the resumable bank, and a
  cancellation names the subject it was asked to cancel.

**Adversarial record.**  `legacyResume`, `legacySend` and `legacyCancel`
compute the payload the old replies carried, from the same transitions.
`legacy_replies_leaked` proves, on the canonical sample plan, that the old
payloads differ on the `#542` pairs (states that satisfy every
`OwnStepCounter` premise), and `register_channel_closed_on_pairs` that the
new replies on the same pairs are equal.  The negative fixture
`tests/negative/CompositeRegisterChannelReopened.lean` shows that the old
inconsistency cannot be proved of the new replies.
-/
namespace LeanOS.CompositeRegisterChannels

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeChannels
open LeanOS.CompositeSwitchedChannels
set_option linter.unusedSimpArgs false

/-! ## The subject a switch reply names is the scheduled subject -/

/-- An accepted round-robin yield schedules exactly the subject it returns. -/
theorem yield_accepted_current (scheduler : Scheduler.State)
    (selected : Scheduler.TrustedContext)
    (haccepted : (Scheduler.yield scheduler).result = .accepted (some selected)) :
    (Scheduler.yield scheduler).state.lifecycle.current = some selected.currentSubject := by
  revert haccepted
  unfold Scheduler.yield Scheduler.selectNext
  repeat' split
  all_goals simp_all [Scheduler.reject]
  intro h
  subst h
  rfl

/-- A switch restores exactly the subject its scheduler step selects. -/
theorem switch_restored_current (resumable : ResumablePreemption.State)
    (interruptState : Interrupt.State) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers) (restored : ResumablePreemption.Context)
    (hrestored : (ResumablePreemption.switch resumable interruptState frame
      registers).restored = some restored) :
    (ResumablePreemption.switch resumable interruptState frame
      registers).state.scheduler.lifecycle.current = some restored.owner := by
  revert hrestored
  unfold ResumablePreemption.switch
  generalize htick : Scheduler.tick resumable.scheduler = scheduled
  rcases scheduled with ⟨next, (_ | selected) | reason⟩
  all_goals
    repeat' split
  all_goals simp [ResumablePreemption.reject, ResumablePreemption.halt]
  cases hctx : ResumablePreemption.contextFor resumable.contexts selected.currentSubject with
  | none => simp
  | some destination =>
      simp only
      split
      · simp
      · rename_i hcheck
        intro h
        simp only [Option.some.injEq] at h
        subst h
        simp only [not_or, Decidable.not_not] at hcheck
        have hcurrent := yield_accepted_current resumable.scheduler selected
          (by rw [show Scheduler.yield resumable.scheduler = Scheduler.tick resumable.scheduler
            from rfl, htick])
        rw [show Scheduler.yield resumable.scheduler = Scheduler.tick resumable.scheduler
          from rfl, htick] at hcurrent
        simp only at hcurrent ⊢
        rw [hcurrent, hcheck.1.1.1.1.1.2]

/-- **A switch reply names only the scheduled subject.**  When the gate
reports a completed switch to subject `next`, `next` is the scheduled subject
of the post-state, which is part of every observer's view: the reply carries
the public scheduler choice and none of `next`'s saved frame or registers. -/
theorem resume_reply_names_scheduled (state : CompositeState)
    (frame : Interrupt.HardwareFrame) (registers : ResumablePreemption.Registers)
    (next : Nat)
    (hreply : (authoritativeGate state (.ordinary (.resumePreempt frame registers))).result =
      .completed (.ordinary (.resume (some next) none))) :
    (authoritativeGate state (.ordinary (.resumePreempt frame registers))).state.lifecycle.current =
      some next := by
  rw [authoritativeGate_ordinary_state]
  cases hmode : state.execution.mode with
  | handling entry => simp [authoritativeGate, hmode] at hreply
  | halted record => simp [authoritativeGate, hmode] at hreply
  | running =>
      simp only [authoritativeGate, hmode, authoritativeOperationReply, operationReply,
        AuthoritativeGateResult.completed.injEq, AuthoritativeOperationReply.ordinary.injEq,
        OperationReply.resume.injEq] at hreply
      obtain ⟨hrestored, herror⟩ := hreply
      generalize houtcome : ResumablePreemption.switch state.resumable state.execution.core
        frame registers = outcome at hrestored herror
      rcases outcome with ⟨resumable, restored, error⟩
      simp only at hrestored herror
      subst herror
      obtain ⟨context, hcontext, howner⟩ := Option.map_eq_some_iff.1 hrestored
      have hcurrent := switch_restored_current state.resumable state.execution.core frame
        registers context (by rw [houtcome]; exact hcontext)
      rw [houtcome] at hcurrent
      simp only [gate, hmode, applyOperation, houtcome, installResumable]
      rw [hcurrent, howner]

/-! ## The adversarial record: what the old replies carried -/

/-- The context the old reply of a resumable switch carried: the restored
context of the next subject. -/
def legacyResume (state : CompositeState) : Operation → Option ResumablePreemption.Context
  | .resumePreempt frame registers =>
      (ResumablePreemption.switch state.resumable state.execution.core frame registers).restored
  | _ => none

/-- The context the old reply of a waking blocking send carried. -/
def legacySend (state : CompositeState) (handleWord word0 word1 : UInt64) :
    Option ResumableContext.Context :=
  (dispatchBlockingSend state handleWord word0 word1).restored

/-- The context the old reply of a wait cancellation carried. -/
def legacyCancel (state : CompositeState) (subject : Nat) : Option ResumableContext.Context :=
  (dispatchBlockingCancel state subject).restored

/-- The old payload was the new reply's subject together with that subject's
saved frame and registers. -/
theorem legacyResume_owner (state : CompositeState) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers) :
    operationReply state (.resumePreempt frame registers) =
      .resume ((legacyResume state (.resumePreempt frame registers)).map (·.owner))
        (ResumablePreemption.switch state.resumable state.execution.core frame
          registers).error := rfl

/-- Every fact below, evaluated on one plan. -/
def facts (plan : BootPageTablePlan.Plan) : Bool :=
  let preemptLeft := runFrom plan preemptLeftTrace
  let preemptRight := runFrom plan preemptRightTrace
  let blockedLeft := runFrom plan blockedLeftTrace
  let blockedRight := runFrom plan blockedRightTrace
  pairFacts preemptLeft preemptRight &&
    pairFacts blockedLeft blockedRight &&
    -- The old replies leaked the other subject's saved registers.
    legacyResume preemptLeft preempt != legacyResume preemptRight preempt &&
    legacySend blockedLeft endpointWord 5 6 != legacySend blockedRight endpointWord 5 6 &&
    legacyCancel blockedLeft 1 != legacyCancel blockedRight 1 &&
    -- The new replies on the same pairs agree.
    reply preemptLeft preempt == reply preemptRight preempt &&
    (authoritativeGate blockedLeft blockingSend).result ==
      (authoritativeGate blockedRight blockingSend).result &&
    (authoritativeGate blockedLeft blockingCancel).result ==
      (authoritativeGate blockedRight blockingCancel).result

set_option maxRecDepth 100000 in
/-- **Kernel evaluation on the canonical sample plan.** -/
theorem facts_sample :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => facts plan
      | .error _ => false) = true := by
  decide +kernel

theorem facts_of_compile {plan : BootPageTablePlan.Plan}
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    facts plan = true := by
  have h := facts_sample
  rw [hplan] at h
  exact h

/-- Every fact of `facts`, named. -/
structure Facts (plan : BootPageTablePlan.Plan) : Prop where
  preemptPair : pairFacts (runFrom plan preemptLeftTrace) (runFrom plan preemptRightTrace) = true
  blockedPair : pairFacts (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) = true
  legacyPreempt : legacyResume (runFrom plan preemptLeftTrace) preempt ≠
    legacyResume (runFrom plan preemptRightTrace) preempt
  legacyWake : legacySend (runFrom plan blockedLeftTrace) endpointWord 5 6 ≠
    legacySend (runFrom plan blockedRightTrace) endpointWord 5 6
  legacyCancelled : legacyCancel (runFrom plan blockedLeftTrace) 1 ≠
    legacyCancel (runFrom plan blockedRightTrace) 1
  preemptReply : reply (runFrom plan preemptLeftTrace) preempt =
    reply (runFrom plan preemptRightTrace) preempt
  sendReply : (authoritativeGate (runFrom plan blockedLeftTrace) blockingSend).result =
    (authoritativeGate (runFrom plan blockedRightTrace) blockingSend).result
  cancelReply : (authoritativeGate (runFrom plan blockedLeftTrace) blockingCancel).result =
    (authoritativeGate (runFrom plan blockedRightTrace) blockingCancel).result

theorem facts_parts {plan : BootPageTablePlan.Plan}
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    Facts plan := by
  have hfacts := facts_of_compile hplan
  simp only [facts, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hfacts
  obtain ⟨⟨⟨⟨⟨⟨⟨hpreemptPair, hblockedPair⟩, hlegacyPreempt⟩, hlegacyWake⟩,
    hlegacyCancel⟩, hpreempt⟩, hsend⟩, hcancel⟩ := hfacts
  exact ⟨hpreemptPair, hblockedPair, hlegacyPreempt, hlegacyWake, hlegacyCancel, hpreempt,
    hsend, hcancel⟩

theorem preempt_pair (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan preemptLeftTrace) (runFrom plan preemptRightTrace) :=
  ownStepCounter_of_pairFacts plan _ _ preemptLeftTrace_keeps preemptRightTrace_keeps
    (facts_parts hplan).preemptPair

theorem blocked_pair (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) :=
  ownStepCounter_of_pairFacts plan _ _ (blockedTrace_keeps _) (blockedTrace_keeps _)
    (facts_parts hplan).blockedPair

/-- **The old replies leaked another subject's registers** (adversarial
record of `#542`'s three channels).  On pairs that satisfy every
`OwnStepCounter` premise, the contexts the old replies of the observer's timer
switch, its waking blocking send, and its wait cancellation carried differ:
they hold another subject's saved registers. -/
theorem legacy_replies_leaked (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan preemptLeftTrace) (runFrom plan preemptRightTrace) ∧
      legacyResume (runFrom plan preemptLeftTrace) preempt ≠
        legacyResume (runFrom plan preemptRightTrace) preempt ∧
      OwnStepCounter 2 (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) ∧
      legacySend (runFrom plan blockedLeftTrace) endpointWord 5 6 ≠
        legacySend (runFrom plan blockedRightTrace) endpointWord 5 6 ∧
      legacyCancel (runFrom plan blockedLeftTrace) 1 ≠
        legacyCancel (runFrom plan blockedRightTrace) 1 :=
  ⟨preempt_pair plan hplan, (facts_parts hplan).legacyPreempt, blocked_pair plan hplan,
    (facts_parts hplan).legacyWake, (facts_parts hplan).legacyCancelled⟩

/-- **The channel is closed on the same pairs**: the observer's timer switch,
blocking send and wait cancellation now return equal replies. -/
theorem register_channel_closed_on_pairs (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    reply (runFrom plan preemptLeftTrace) preempt =
        reply (runFrom plan preemptRightTrace) preempt ∧
      (authoritativeGate (runFrom plan blockedLeftTrace) blockingSend).result =
        (authoritativeGate (runFrom plan blockedRightTrace) blockingSend).result ∧
      (authoritativeGate (runFrom plan blockedLeftTrace) blockingCancel).result =
        (authoritativeGate (runFrom plan blockedRightTrace) blockingCancel).result :=
  ⟨(facts_parts hplan).preemptReply, (facts_parts hplan).sendReply,
    (facts_parts hplan).cancelReply⟩

end LeanOS.CompositeRegisterChannels
