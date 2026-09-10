import LeanOS.UserCopyPrefix

/-!
Abstract termination contract for the proposed no-SMAP copy transaction.
The caller starts under an established closed root and keeps mapping authority
stable. A cleanup report is an input from a future trusted root-switch and
invalidation boundary, not evidence produced by this model. In particular,
`verifiedClosed` must not be implemented as a CR3-address comparison alone.
There is no transition that resumes an interrupted transaction.
-/
namespace LeanOS.UserCopyTransaction

open LeanOS.UserCopy LeanOS.UserCopyPrefix

inductive Direction where
  | fromUser | toUser
  deriving DecidableEq, Repr

inductive Stop where
  | finished | interrupted | faulted
  deriving DecidableEq, Repr

inductive Cleanup where
  | verifiedClosed | unverified
  deriving DecidableEq, Repr

inductive Disposition where
  | returned | rejected (reason : CopyError)
  | terminal
  deriving DecidableEq, Repr

structure Outcome where
  memory : UserCopy.State
  cleanup : Cleanup
  disposition : Disposition

def access : Direction → VirtualMapping.Access
  | .fromUser => .read
  | .toUser => .write

/-- The outcome is terminal for every non-finished stop, incomplete progress or
unverified cleanup. These inputs describe a completed execution observation;
they do not authorize a copy primitive to perform additional writes. -/
def finish (length completed : Nat) (stop : Stop) (cleanup : Cleanup) : Disposition :=
  if cleanup = .verifiedClosed ∧ stop = .finished ∧ completed = length then .returned
  else .terminal

def run (state : UserCopy.State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) (direction : Direction) (completed : Nat)
    (stop : Stop) (cleanup : Cleanup) : Outcome :=
  match validate state context start length (access direction) with
  | .error reason =>
      -- Validation happens under the already established closed root.
      { memory := state, cleanup := .verifiedClosed, disposition := .rejected reason }
  | .ok _ =>
      let memory := match direction with
        | .fromUser => copyFromPrefix state context start length buffer completed
        | .toUser => copyToPrefix state context start length buffer completed
      { memory, cleanup, disposition := finish length completed stop cleanup }

theorem finish_returned_iff length completed stop cleanup :
    finish length completed stop cleanup = .returned ↔
      cleanup = .verifiedClosed ∧ stop = .finished ∧ completed = length := by
  simp [finish]

/-- Every normal return has a successful whole-request validation and a fully
finished transfer followed by the trusted boundary's verified-closed report. -/
theorem returned_requires_contract state context start length buffer direction completed stop cleanup
    (h : (run state context start length buffer direction completed stop cleanup).disposition =
      .returned) :
    (∃ locations, validate state context start length (access direction) = .ok locations) ∧
      cleanup = .verifiedClosed ∧ stop = .finished ∧ completed = length := by
  unfold run at h
  split at h
  · contradiction
  next locations hv =>
    exact ⟨⟨locations, hv⟩, (finish_returned_iff _ _ _ _).mp h⟩

theorem rejected_memory_unchanged state context start length buffer direction completed stop cleanup reason
    (h : validate state context start length (access direction) = .error reason) :
    (run state context start length buffer direction completed stop cleanup).memory = state := by
  simp [run, h]

/-- Once validation succeeds, failure to establish root closure is terminal.
The outcome keeps the unverified report; it does not pretend closure succeeded. -/
theorem cleanup_failure_terminal state context start length buffer direction completed stop locations
    (h : validate state context start length (access direction) = .ok locations) :
    (run state context start length buffer direction completed stop .unverified).disposition =
      .terminal ∧
    (run state context start length buffer direction completed stop .unverified).cleanup =
      .unverified := by
  simp [run, h, finish]

theorem exceptional_stop_terminal state context start length buffer direction completed stop cleanup locations
    (h : validate state context start length (access direction) = .ok locations)
    (hs : stop ≠ .finished) :
    (run state context start length buffer direction completed stop cleanup).disposition =
      .terminal := by
  simp [run, h, finish, hs]

/-- Even an asserted normal stop and closed root cannot turn incomplete or
excessive progress into a successful return. -/
theorem wrong_progress_terminal state context start length buffer direction completed stop cleanup locations
    (h : validate state context start length (access direction) = .ok locations)
    (hc : completed ≠ length) :
    (run state context start length buffer direction completed stop cleanup).disposition =
      .terminal := by
  simp [run, h, finish, hc]

theorem preserves_authority state context start length buffer direction completed stop cleanup :
    (run state context start length buffer direction completed stop cleanup).memory.virtual =
      state.virtual := by
  unfold run
  split
  · rfl
  · cases direction
    · exact from_preserves_authority _ _ _ _ _ _
    · exact UserCopyPrefix.preserves_authority _ _ _ _ _ _

/-- Termination and cleanup do not roll back the observed copy-to prefix. -/
theorem to_effects state context start length buffer completed stop cleanup :
    (run state context start length buffer .toUser completed stop cleanup).memory =
      copyToPrefix state context start length buffer completed := by
  cases h : validate state context start length .write with
  | error reason => simp [run, access, h, copyToPrefix]
  | ok locations => simp [run, access, h]

theorem from_effects state context start length buffer completed stop cleanup :
    (run state context start length buffer .fromUser completed stop cleanup).memory =
      copyFromPrefix state context start length buffer completed := by
  cases h : validate state context start length .read with
  | error reason => simp [run, access, h, copyFromPrefix]
  | ok locations => simp [run, access, h]

end LeanOS.UserCopyTransaction
