import LeanOS.UserCopy

/-!
# Atomic SMAP user-copy window

This module composes whole-range `UserCopy.validate` with an explicit model of
the EFLAGS.AC override.  The public operations are atomic: validation happens
while AC is clear, the modeled byte transfer is the only action in the window,
and every return path clears AC.  The sequential model assumes that mappings
cannot change between validation and transfer.
-/
namespace LeanOS.UserCopyWindow

open LeanOS.UserCopy
open LeanOS.VirtualMapping

structure State where
  memory : UserCopy.State
  ac : Bool := false

inductive Error where
  | acAlreadySet
  | validation (reason : CopyError)
  deriving BEq, DecidableEq, Repr

inductive Result where
  | accepted
  | rejected (reason : Error)
  deriving BEq, DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

private def reject (state : State) (reason : Error) : Outcome :=
  { state := { state with ac := false }, result := .rejected reason }

/-- Validate with AC clear, perform exactly one bounded copy-from operation,
then close the override before returning. -/
def copyFrom (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) : Outcome :=
  if state.ac then reject state .acAlreadySet
  else match validate state.memory context start length .read with
    | .error reason => reject state (.validation reason)
    | .ok _ =>
      let copied := copyFromUser state.memory context start length buffer
      { state := { memory := copied.state, ac := false }, result := .accepted }

/-- Validate with AC clear, perform exactly one bounded copy-to operation,
then close the override before returning. -/
def copyTo (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) : Outcome :=
  if state.ac then reject state .acAlreadySet
  else match validate state.memory context start length .write with
    | .error reason => reject state (.validation reason)
    | .ok _ =>
      let copied := copyToUser state.memory context start length buffer
      { state := { memory := copied.state, ac := false }, result := .accepted }

theorem copyFrom_clears_ac state context start length buffer :
    (copyFrom state context start length buffer).state.ac = false := by
  unfold copyFrom
  split
  · rfl
  · split <;> rfl

theorem copyTo_clears_ac state context start length buffer :
    (copyTo state context start length buffer).state.ac = false := by
  unfold copyTo
  split
  · rfl
  · split <;> rfl

/-- An accepted copy window can only arise from successful whole-range
prevalidation with the requested read permission. -/
theorem copyFrom_accepted_validated state context start length buffer
    (h : (copyFrom state context start length buffer).result = .accepted) :
    ∃ locations, validate state.memory context start length .read = .ok locations := by
  simp only [copyFrom] at h
  split at h <;> try contradiction
  next =>
    split at h <;> try contradiction
    next locations hvalidate => exact ⟨locations, hvalidate⟩

/-- An accepted copy-to window can only arise from successful whole-range
prevalidation with the requested write permission. -/
theorem copyTo_accepted_validated state context start length buffer
    (h : (copyTo state context start length buffer).result = .accepted) :
    ∃ locations, validate state.memory context start length .write = .ok locations := by
  simp only [copyTo] at h
  split at h <;> try contradiction
  next =>
    split at h <;> try contradiction
    next locations hvalidate => exact ⟨locations, hvalidate⟩

/-- Rejection before opening the window cannot modify either memory domain. -/
theorem copyFrom_rejected_memory_unchanged state context start length buffer reason
    (h : (copyFrom state context start length buffer).result = .rejected reason) :
    (copyFrom state context start length buffer).state.memory = state.memory := by
  by_cases hac : state.ac = true
  · simp [copyFrom, hac, reject]
  · cases hv : validate state.memory context start length .read with
    | error copyError => simp [copyFrom, hac, hv, reject]
    | ok locations => simp [copyFrom, hac, hv] at h

/-- Rejection before opening the window cannot modify either memory domain. -/
theorem copyTo_rejected_memory_unchanged state context start length buffer reason
    (h : (copyTo state context start length buffer).result = .rejected reason) :
    (copyTo state context start length buffer).state.memory = state.memory := by
  by_cases hac : state.ac = true
  · simp [copyTo, hac, reject]
  · cases hv : validate state.memory context start length .write with
    | error copyError => simp [copyTo, hac, hv, reject]
    | ok locations => simp [copyTo, hac, hv] at h

end LeanOS.UserCopyWindow
