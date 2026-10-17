import LeanOS.FailStop.SubjectGate
import LeanOS.TimingChannels

/-!
# Timing channels: the closures of ADR 0028 (issue #576)

ADR 0028 closes two timing channels by construction.  This module states what
each closure decides; the timing-channels QEMU image exercises both and
reports the cycle counts of the paths the ADR names.

**Cross-subject refusals at a fixed budget.**  The subject gate refuses a
scheduled subject's request that names another subject (ADR 0025).

* The boot witness `TimingChannels.crossSubjectRefusal` answers exactly
  `CompositeState.refusesCrossSubject` on the encoded latch mode, scheduled
  subject and target (`crossSubjectRefusal_agrees`).  It has no other input,
  so the decision reads nothing of the target.
* The reply leaves the kernel at `departure start work budget`: the kernel
  spins until `budget` cycles after entry, or leaves when its work is done if
  that is later.  Two refusals whose work fits the budget leave at the same
  cycle (`departure_fixed`), and no refusal leaves before the budget
  (`departure_not_early`).
* Together (`refusal_fixed_budget`): two states that agree on the latch mode
  and the scheduled subject refuse the same cross-subject request with the
  same fixed result, change nothing, and reply at the same cycle when the
  work fits the budget, whatever the target's state.

**No cycle counter at CPL3.**  The validated user return (`validate_user_return`
in `boot/kernel.c`, the only path to `iretq`) requires CR4.TSD and forbids
CR4.PCE (`userReturnClockControls`).  `userCounterFaults` states the
architectural reading of RDTSC, RDTSCP and RDPMC at CPL 3 (Intel SDM Vol. 2B);
`clock_controls_deny_user_counters` proves the gate's controls imply it.  The
processor's behaviour is an assumption, which the image exercises: its
observer executes `rdtsc` at CPL3 and takes #GP(0).

What this does not prove: anything about real cycles.  `work` is whatever the
hardware takes; the model says only how the departure is computed from it.
Caches, TLBs, branch predictors and other microarchitectural state are out of
scope (ADR 0028), as is refinement of the C path to this model.
-/
namespace LeanOS.TimingBudget

open LeanOS LeanOS.FailStop LeanOS.TimingChannels

/-! ## The refusal witness agrees with the subject gate -/

/-- The latch mode word the witness reads. -/
def modeWord : Mode → UInt64
  | .running => 1
  | .handling _ => 2
  | .halted _ => 3

/-- A subject word: `0` for none, the identity plus one otherwise. -/
def subjectWord : Option Nat → UInt64
  | none => 0
  | some subject => UInt64.ofNat (subject + 1)

/-- The subject identities a word carries exactly. -/
def Encodable : Option Nat → Prop
  | none => True
  | some subject => subject + 1 < 2 ^ 64

private theorem subjectWord_some_toNat {subject : Nat} (h : subject + 1 < 2 ^ 64) :
    (subjectWord (some subject)).toNat = subject + 1 := by
  simp only [subjectWord, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

private theorem subjectWord_some_ne_zero {subject : Nat} (h : subject + 1 < 2 ^ 64) :
    subjectWord (some subject) ≠ 0 := by
  intro hzero
  have := subjectWord_some_toNat h
  rw [hzero] at this
  simp at this

private theorem subjectWord_some_inj {left right : Nat} (hl : left + 1 < 2 ^ 64)
    (hr : right + 1 < 2 ^ 64) :
    subjectWord (some left) = subjectWord (some right) ↔ left = right := by
  constructor
  · intro h
    have hl' := subjectWord_some_toNat hl
    have hr' := subjectWord_some_toNat hr
    rw [h] at hl'
    omega
  · intro h
    rw [h]

/-- **The witness is the gate's refusal.**  On the encoded latch mode,
scheduled subject and target, `crossSubjectRefusal` answers the refusal word
exactly when the subject gate refuses the request as cross-subject. -/
theorem crossSubjectRefusal_agrees (state : CompositeState) (operation : AuthoritativeOperation)
    (hcurrent : Encodable state.lifecycle.current) (htarget : Encodable operation.target) :
    crossSubjectRefusal (modeWord state.execution.mode) (subjectWord state.lifecycle.current)
        (subjectWord operation.target) =
      if state.refusesCrossSubject operation then refusedWord else passWord := by
  unfold CompositeState.refusesCrossSubject
  cases hmode : state.execution.mode with
  | handling entry => simp [crossSubjectRefusal, modeWord]
  | halted record => simp [crossSubjectRefusal, modeWord]
  | running =>
      cases hc : state.lifecycle.current with
      | none => simp [crossSubjectRefusal, modeWord, subjectWord]
      | some caller =>
          rw [hc] at hcurrent
          cases ht : operation.target with
          | none => simp [crossSubjectRefusal, modeWord, subjectWord]
          | some target =>
              rw [ht] at htarget
              simp only [Encodable] at hcurrent htarget
              have hcaller := subjectWord_some_ne_zero hcurrent
              have htargetNe := subjectWord_some_ne_zero htarget
              have hinj := subjectWord_some_inj htarget hcurrent
              by_cases hsame : target = caller
              · subst hsame
                simp [crossSubjectRefusal, modeWord]
              · have hdiff : subjectWord (some target) ≠ subjectWord (some caller) :=
                  fun h => hsame (hinj.mp h)
                simp [crossSubjectRefusal, modeWord, hcaller, htargetNe, hdiff, hsame]

/-! ## The reply departs at a fixed budget -/

/-- The cycle at which a reply padded to `budget` leaves the kernel, for a
path that entered at `start` and needed `work` cycles: the kernel spins until
`start + budget`, or leaves when its work is done if that is later (an
overrun, which the timing-channels image counts and reports). -/
def departure (start work budget : Nat) : Nat := start + max work budget

/-- No padded reply leaves before its budget. -/
theorem departure_not_early (start work budget : Nat) :
    start + budget ≤ departure start work budget := by
  unfold departure; omega

/-- Two padded replies whose work fits the budget leave at the same cycle. -/
theorem departure_fixed {start left right budget : Nat} (hleft : left ≤ budget)
    (hright : right ≤ budget) :
    departure start left budget = departure start right budget := by
  unfold departure; omega

/-- A path that fits its budget leaves exactly at the budget. -/
theorem departure_within {start work budget : Nat} (h : work ≤ budget) :
    departure start work budget = start + budget := by
  unfold departure; omega

/-- An overrun leaves when its work is done. -/
theorem departure_overrun {start work budget : Nat} (h : budget < work) :
    departure start work budget = start + work := by
  unfold departure; omega

/-- **Refusal at a fixed budget.**  Two states that agree on the latch mode
and the scheduled subject, which every observer sees, and a request the gate
refuses as cross-subject in one of them: the gate refuses it in both with the
one fixed result and changes neither, and two refusals whose work fits the
budget reply at the same cycle.  Nothing of the target enters. -/
theorem refusal_fixed_budget {left right : CompositeState} {operation : AuthoritativeOperation}
    (hmode : left.execution.mode = right.execution.mode)
    (hcurrent : left.lifecycle.current = right.lifecycle.current)
    (hrefused : left.refusesCrossSubject operation = true)
    {start budget leftWork rightWork : Nat} (hleft : leftWork ≤ budget)
    (hright : rightWork ≤ budget) :
    subjectGate left operation = { state := left, result := .crossSubjectRefused } ∧
      subjectGate right operation = { state := right, result := .crossSubjectRefused } ∧
      departure start leftWork budget = departure start rightWork budget := by
  have hright' : right.refusesCrossSubject operation = true := by
    rw [← refusesCrossSubject_congr hmode hcurrent operation]; exact hrefused
  exact ⟨subjectGate_refused hrefused, subjectGate_refused hright',
    departure_fixed hleft hright⟩

/-- The witness's answer is a function of the three public words: the two
states of `refusal_fixed_budget` give it the same words. -/
theorem refusal_words_public {left right : CompositeState} (operation : AuthoritativeOperation)
    (hmode : left.execution.mode = right.execution.mode)
    (hcurrent : left.lifecycle.current = right.lifecycle.current) :
    crossSubjectRefusal (modeWord left.execution.mode) (subjectWord left.lifecycle.current)
        (subjectWord operation.target) =
      crossSubjectRefusal (modeWord right.execution.mode) (subjectWord right.lifecycle.current)
        (subjectWord operation.target) := by
  rw [hmode, hcurrent]

/-! ## No cycle counter at CPL3 -/

/-- CR4.TSD (bit 2): RDTSC and RDTSCP are privileged. -/
def tsdBit : UInt64 := 0x4

/-- CR4.PCE (bit 8): RDPMC is allowed at any privilege level. -/
def pceBit : UInt64 := 0x100

/-- The clock controls `validate_user_return` requires of the live CR4 before
every return to CPL3: TSD set, PCE clear. -/
def userReturnClockControls (cr4 : UInt64) : Bool :=
  (cr4 &&& tsdBit == tsdBit) && (cr4 &&& pceBit == 0)

/-- The architectural reading this closure assumes (Intel SDM Vol. 2B,
RDTSC, RDTSCP and RDPMC): at a CPL other than 0, RDTSC and RDTSCP raise
#GP(0) when CR4.TSD is set, and RDPMC raises #GP(0) when CR4.PCE is clear.
It is a statement about the processor, not a proof of it. -/
def userCounterFaults (cr4 : UInt64) (cpl : Nat) : Bool :=
  cpl != 0 && (cr4 &&& tsdBit != 0) && (cr4 &&& pceBit == 0)

/-- Every CR4 the outbound gate accepts makes the time-stamp counter and the
performance counters fault at CPL3. -/
theorem clock_controls_deny_user_counters (cr4 : UInt64)
    (h : userReturnClockControls cr4 = true) : userCounterFaults cr4 3 = true := by
  simp only [userReturnClockControls, Bool.and_eq_true, beq_iff_eq] at h
  unfold userCounterFaults
  rw [h.1, h.2]
  decide

/-- A CR4 without TSD, such as firmware leaves it, is refused by the gate. -/
theorem clock_controls_require_tsd (cr4 : UInt64) (h : cr4 &&& tsdBit = 0) :
    userReturnClockControls cr4 = false := by
  unfold userReturnClockControls
  rw [h]
  have hzero : ((0 : UInt64) == tsdBit) = false := by decide
  simp [hzero]

end LeanOS.TimingBudget
