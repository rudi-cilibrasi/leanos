import LeanOS.UserCopy

/-!
Sequential copy progress for the proposed no-SMAP window. The whole request
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

/-- Copy-from progress reads only the completed prefix of the fully validated
source list. Other kernel buffers and the uncompleted destination suffix retain
their original contents. This function does not model an atomic rollback. -/
def copyFromPrefix (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) (completed : Nat) : State :=
  match validate state context start length .read with
  | .error _ => state
  | .ok locations =>
      let values := (locations.take (min completed length)).map
        (fun location => state.userBytes location.frame location.offset)
      { state with kernelBytes := setKernelRange state.kernelBytes buffer values }

theorem from_rejected_unchanged state context start length buffer completed reason
    (h : validate state context start length .read = .error reason) :
    copyFromPrefix state context start length buffer completed = state := by
  simp [copyFromPrefix, h]

theorem from_zero_progress_unchanged state context start length buffer :
    copyFromPrefix state context start length buffer 0 = state := by
  unfold copyFromPrefix
  split
  · rfl
  · simp only [Nat.zero_min, List.take_zero, List.map_nil]
    have hempty : setKernelRange state.kernelBytes buffer [] = state.kernelBytes := by
      funext candidate offset
      simp [setKernelRange]
    rw [hempty]

theorem from_preserves_user state context start length buffer completed :
    (copyFromPrefix state context start length buffer completed).userBytes = state.userBytes := by
  unfold copyFromPrefix
  split <;> rfl

theorem from_preserves_authority state context start length buffer completed :
    (copyFromPrefix state context start length buffer completed).virtual = state.virtual := by
  unfold copyFromPrefix
  split <;> rfl

/-- No other buffer or byte at/after the progress bound can change. -/
theorem from_outside_prefix state context start length buffer completed candidate offset
    (h : candidate ≠ buffer ∨ min completed length ≤ offset) :
    (copyFromPrefix state context start length buffer completed).kernelBytes candidate offset =
      state.kernelBytes candidate offset := by
  unfold copyFromPrefix
  split
  · rfl
  next locations hv =>
    apply setKernelRange_outside
    rcases h with hb | ho
    · exact Or.inl hb
    · right
      have hl := validate_length state context start .read length locations hv
      simpa [hl, Nat.min_assoc] using ho

/-- All copied values come from the validated source prefix in its original
order. There is no unvalidated source read in the modeled result. -/
theorem from_validated_exact state context start length buffer completed locations
    (h : validate state context start length .read = .ok locations) :
    (copyFromPrefix state context start length buffer completed).kernelBytes =
      setKernelRange state.kernelBytes buffer
        ((locations.take (min completed length)).map
          (fun location => state.userBytes location.frame location.offset)) := by
  simp [copyFromPrefix, h]

theorem from_complete_agrees state context start length buffer completed
    (h : length ≤ completed) :
    copyFromPrefix state context start length buffer completed =
      (copyFromUser state context start length buffer).state := by
  cases hv : validate state context start length .read with
  | error reason => simp [copyFromPrefix, copyFromUser, hv, reject]
  | ok locations =>
      have hl := validate_length state context start .read length locations hv
      simp only [copyFromPrefix, copyFromUser, hv, Nat.min_eq_right h]
      rw [← hl, List.take_length]

end LeanOS.UserCopyPrefix
