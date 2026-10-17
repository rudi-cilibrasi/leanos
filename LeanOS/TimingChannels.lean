/-!
# Timing channels: the cross-subject refusal witness (issue #576)

ADR 0028 decides which timing differences LeanOS declares, which it closes and
which are out of scope.  One closure is the subject gate's refusal of a
cross-subject request (ADR 0025): the gate decides the refusal from three
words every observer already sees (the latch mode, the scheduled subject and
the subject the request names) and answers one fixed word, so the refusal
path reads nothing of the target, and the kernel pads its reply to a fixed
cycle budget (`TimingBudget.departure`).

This module is the allocation-free witness the timing-channels image calls on
that path, `leanos_cross_subject_refusal`.  It has three inputs and no others:
whatever the target's state is, the witness cannot read it.
`TimingBudget.crossSubjectRefusal_agrees` proves that it answers exactly
`FailStop.CompositeState.refusesCrossSubject` on the encoded words.

The words:

* `mode`: `1` when the fail-stop latch is running; any other word is not
  running (`2` handling an entry, `3` halted).
* `scheduled`: `0` when no subject is scheduled, otherwise its identity plus
  one.
* `target`: `0` when the request names no subject, otherwise that subject's
  identity plus one.

The answer is `refusedWord` for a refusal and `passWord` otherwise, when the
request goes on to the authoritative gate.
-/
namespace LeanOS.TimingChannels

/-- The fixed reply of a refused cross-subject request. -/
def refusedWord : UInt64 := 0xc5

/-- The answer for a request the gate does not refuse. -/
def passWord : UInt64 := 0

/-- Allocation-free witness of the subject gate's cross-subject refusal.  It
refuses exactly when the latch is running, a subject is scheduled, and the
request names a different subject. -/
@[export leanos_cross_subject_refusal]
def crossSubjectRefusal (mode scheduled target : UInt64) : UInt64 :=
  if mode == 1 && scheduled != 0 && target != 0 && target != scheduled then refusedWord
  else passWord

/-- The witness answers one of two words. -/
theorem crossSubjectRefusal_cases (mode scheduled target : UInt64) :
    crossSubjectRefusal mode scheduled target = refusedWord ∨
      crossSubjectRefusal mode scheduled target = passWord := by
  unfold crossSubjectRefusal
  split
  · exact .inl rfl
  · exact .inr rfl

/-- The refusal word is never the pass word. -/
theorem refusedWord_ne_passWord : refusedWord ≠ passWord := by decide

/-- A refusal names a subject other than the scheduled one, while the latch
runs. -/
theorem crossSubjectRefusal_refused {mode scheduled target : UInt64}
    (h : crossSubjectRefusal mode scheduled target = refusedWord) :
    mode = 1 ∧ scheduled ≠ 0 ∧ target ≠ 0 ∧ target ≠ scheduled := by
  unfold crossSubjectRefusal at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcond
    exact ⟨hcond.1.1.1, hcond.1.1.2, hcond.1.2, hcond.2⟩
  · exact absurd h.symm refusedWord_ne_passWord

/-- A request that names its own caller, or no subject, is never refused. -/
theorem crossSubjectRefusal_own (mode scheduled : UInt64) :
    crossSubjectRefusal mode scheduled scheduled = passWord ∧
      crossSubjectRefusal mode scheduled 0 = passWord := by
  constructor <;> simp [crossSubjectRefusal]

end LeanOS.TimingChannels
