import LeanOS.UserCopy

/-!
Sequential copy-to progress for the proposed no-SMAP window. The whole request
is validated before any write. `completed` describes a possible interruption
point, not permission to resume or return to CPL3. Actual copy instructions,
root closure and interrupt handling still require a refinement to this model.
-/
namespace LeanOS.UserCopyPrefix

open LeanOS.UserCopy

/-- Apply at most the completed prefix of a fully validated copy-to request.
A rejected request changes no state, even if a nonzero progress count is given.
Counts beyond the requested length saturate at that length. -/
def copyToPrefix (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) (completed : Nat) : State :=
  match validate state context start length .write with
  | .error _ => state
  | .ok locations =>
      let count := min completed length
      let values := List.range count |>.map (state.kernelBytes buffer)
      { state with userBytes := setUserLocations state.userBytes (locations.take count) values }


theorem rejected_unchanged state context start length buffer completed reason
    (h : validate state context start length .write = .error reason) :
    copyToPrefix state context start length buffer completed = state := by
  simp [copyToPrefix, h]

theorem zero_progress_unchanged state context start length buffer :
    copyToPrefix state context start length buffer 0 = state := by
  unfold copyToPrefix
  split <;> simp [setUserLocations]

theorem preserves_kernel state context start length buffer completed :
    (copyToPrefix state context start length buffer completed).kernelBytes = state.kernelBytes := by
  unfold copyToPrefix
  split <;> rfl

theorem preserves_authority state context start length buffer completed :
    (copyToPrefix state context start length buffer completed).virtual = state.virtual := by
  unfold copyToPrefix
  split <;> rfl

/-- Outside the actual prefix, physical bytes retain their original values.
This includes uncompleted destinations only when they do not alias an earlier
prefix byte; no uniqueness or rollback assumption is hidden in the statement. -/
theorem outside_prefix state context start length buffer completed locations frame offset
    (h : validate state context start length .write = .ok locations)
    (hout : ∀ location, location ∈ locations.take (min completed length) →
      location.frame ≠ frame ∨ location.offset ≠ offset) :
    (copyToPrefix state context start length buffer completed).userBytes frame offset =
      state.userBytes frame offset := by
  simp only [copyToPrefix, h]
  exact setUserLocations_outside _ _ _ _ _ hout

/-- Completing the entire request agrees with the existing atomic copy model. -/
theorem complete_agrees state context start length buffer completed
    (h : length ≤ completed) :
    copyToPrefix state context start length buffer completed =
      (copyToUser state context start length buffer).state := by
  cases hv : validate state context start length .write with
  | error reason => simp [copyToPrefix, copyToUser, hv, reject]
  | ok locations =>
      have hl := validate_length state context start .write length locations hv
      simp only [copyToPrefix, copyToUser, hv, Nat.min_eq_right h]
      rw [← hl, List.take_length]

end LeanOS.UserCopyPrefix
