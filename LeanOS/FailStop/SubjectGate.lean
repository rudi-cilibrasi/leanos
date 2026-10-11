import LeanOS.FailStop.AuthoritativeTraces

/-!
# Fail-stop composite: the subject-facing gate

`authoritativeGate` is the kernel's transition engine.  The kernel composes it
for its own purposes: boot creates subjects, the spawn family copies an
endpoint into a child's row and terminates a child, contained cleanup retires
a subject, and the issued lifecycle family creates fresh identities.  None of
those steps has a caller.

`subjectGate` is what a scheduled subject can ask for.  Six ordinary
operations, the blocking wait cancellation and the deferred drain name a
subject (`AuthoritativeOperation.target`): the destination of a delegation, the
victim of a direct or subtree revocation, the subject created, terminated or
admitted to the ready queue, the subject whose wait is cancelled, and the
subject whose deferred cancellation is drained.  When a subject is scheduled
and the operation names another subject, the gate refuses with one fixed
result, `crossSubjectRefused`, before reading anything of the target, and
changes nothing (`CompositeState.refusesCrossSubject`).  It also refuses a
receipt that carries another endpoint with a sealed transfer of its own
pending (`CompositeState.refusesNestedTransfer`, result
`nestedTransferRefused`).
Otherwise it is exactly `authoritativeGate`.

Why.  The ordinary family has no authority relation over another subject: a
delegation could fill any subject's empty slot, a revocation could clear any
slot holding a capability to an object the caller may revoke, and creation,
termination, queue admission, cancellation and drains checked no caller at
all.  Their replies revealed the target's slot occupancy, liveness, issuance,
runnability and wait state, which are outside the caller's view, and a
termination cancelled every pending sealed offer, the caller's own included
(#542, issue #479).  Authorized cross-subject management goes through families
that carry the authority explicitly: sealed transfer (the receiver accepts
into a slot of its own row), subtree revocation of the caller's own lineage
root, the spawn family (the parent/child record), and the fault-handler
binding.  The kernel keeps using `authoritativeGate` for them.

The gate checks the latch first: a busy or halted latch answers exactly as
`authoritativeGate` does.
-/
namespace LeanOS.FailStop

open LeanOS

/-- The subject an operation names other than its caller, if any. -/
def AuthoritativeOperation.target : AuthoritativeOperation → Option Nat
  | .ordinary (.capabilityCopy _ destination _ _) => some destination
  | .ordinary (.capabilityRevoke _ victim _) => some victim
  | .ordinary (.capabilityRevokeSubtree _ victim _) => some victim
  | .ordinary (.createSubject subject) => some subject
  | .ordinary (.terminateSubject subject) => some subject
  | .ordinary (.scheduleAdd subject) => some subject
  | .blocking (.cancel subject) => some subject
  | .drainDeferred subject => some subject
  | _ => none

/-- A scheduled subject asks for an operation that names another subject. -/
def CompositeState.refusesCrossSubject (state : CompositeState)
    (operation : AuthoritativeOperation) : Bool :=
  match state.execution.mode, state.lifecycle.current, operation.target with
  | .running, some caller, some target => target != caller
  | _, _, _ => false

/-- A scheduled subject asks to accept a sealed transfer that carries another
endpoint, which itself has a sealed transfer pending.  The refusal reads only
the endpoint the caller's own handle names, the sealed record pending on it,
and the sealed record pending on the endpoint it carries; it changes nothing.
Receipt would otherwise make the second carried object reachable in the same
step, so a subject could learn, by accepting, the state of an object that no
offer to it carried.  A transfer that carries the endpoint it is pending on is
not refused: receipt consumes that very record. -/
def CompositeState.refusesNestedTransfer (state : CompositeState) :
    AuthoritativeOperation → Bool
  | .ordinary (.transferAccept endpointWord _) =>
      match state.execution.mode with
      | .running =>
          match CapabilityHandle.resolveCurrent state.transfers.capabilities
              { caller := state.execution.core.context.currentSubject } endpointWord
              .endpoint with
          | .ok resolution =>
              match state.transfers.pending resolution.capability.object with
              | some transfer =>
                  transfer.object != resolution.capability.object &&
                    (state.transfers.pending transfer.object).isSome
              | none => false
          | .error _ => false
      | _ => false
  | _ => false

/-- The result a subject observes. -/
inductive SubjectGateResult where
  /-- The kernel performed the operation; its exact gate result. -/
  | gate (result : AuthoritativeGateResult)
  /-- The one fixed refusal of a cross-subject request. -/
  | crossSubjectRefused
  /-- The fixed refusal of a receipt whose carried endpoint has a sealed
  transfer pending. -/
  | nestedTransferRefused
  deriving DecidableEq, Repr

structure SubjectGateOutcome where
  state : CompositeState
  result : SubjectGateResult

/-- The subject gate's refusal of a request, if any. -/
def CompositeState.refusal (state : CompositeState) (operation : AuthoritativeOperation) :
    Option SubjectGateResult :=
  if state.refusesCrossSubject operation then some .crossSubjectRefused
  else if state.refusesNestedTransfer operation then some .nestedTransferRefused
  else none

/-- **The subject-facing gate.** -/
def subjectGate (state : CompositeState) (operation : AuthoritativeOperation) :
    SubjectGateOutcome :=
  match state.refusal operation with
  | some refused => { state, result := refused }
  | none =>
      let outcome := authoritativeGate state operation
      { state := outcome.state, result := .gate outcome.result }

theorem subjectGate_of_refusal {state : CompositeState} {operation : AuthoritativeOperation}
    {refused : SubjectGateResult} (h : state.refusal operation = some refused) :
    subjectGate state operation = { state, result := refused } := by
  simp [subjectGate, h]

theorem subjectGate_of_no_refusal {state : CompositeState} {operation : AuthoritativeOperation}
    (h : state.refusal operation = none) :
    subjectGate state operation =
      { state := (authoritativeGate state operation).state
        result := .gate (authoritativeGate state operation).result } := by
  simp [subjectGate, h]

theorem subjectGate_refused {state : CompositeState} {operation : AuthoritativeOperation}
    (h : state.refusesCrossSubject operation = true) :
    subjectGate state operation = { state, result := .crossSubjectRefused } :=
  subjectGate_of_refusal (by simp [CompositeState.refusal, h])

theorem subjectGate_of_not_refused {state : CompositeState} {operation : AuthoritativeOperation}
    (h : state.refusesCrossSubject operation = false)
    (hnested : state.refusesNestedTransfer operation = false) :
    subjectGate state operation =
      { state := (authoritativeGate state operation).state
        result := .gate (authoritativeGate state operation).result } :=
  subjectGate_of_no_refusal (by simp [CompositeState.refusal, h, hnested])

/-- The gate either refuses without effect or is the authoritative gate. -/
theorem subjectGate_cases (state : CompositeState) (operation : AuthoritativeOperation) :
    (∃ refused, state.refusal operation = some refused ∧
        (subjectGate state operation).state = state ∧
        (subjectGate state operation).result = refused) ∨
      (state.refusal operation = none ∧
        (subjectGate state operation).state = (authoritativeGate state operation).state ∧
        (subjectGate state operation).result =
          .gate (authoritativeGate state operation).result) := by
  cases h : state.refusal operation with
  | none => rw [subjectGate_of_no_refusal h]; exact .inr ⟨rfl, rfl, rfl⟩
  | some refused => rw [subjectGate_of_refusal h]; exact .inl ⟨refused, rfl, rfl, rfl⟩

/-- An operation other than receipt is never refused as a nested transfer. -/
theorem refusesNestedTransfer_eq_false {state : CompositeState} {operation : AuthoritativeOperation}
    (hnot : ∀ endpointWord destinationSlot,
      operation ≠ .ordinary (.transferAccept endpointWord destinationSlot)) :
    state.refusesNestedTransfer operation = false := by
  cases operation with
  | ordinary operation =>
      cases operation <;> simp_all [CompositeState.refusesNestedTransfer]
  | blocking operation => rfl
  | drainDeferred subject => rfl

/-- Refusal reads only the latch mode, the scheduled subject and the
operation. -/
theorem refusesCrossSubject_congr {left right : CompositeState}
    (hmode : left.execution.mode = right.execution.mode)
    (hcurrent : left.lifecycle.current = right.lifecycle.current)
    (operation : AuthoritativeOperation) :
    left.refusesCrossSubject operation = right.refusesCrossSubject operation := by
  simp [CompositeState.refusesCrossSubject, hmode, hcurrent]

/-- An operation that names no subject, or names the scheduled subject
itself, is never refused. -/
theorem refusesCrossSubject_eq_false_of_target {state : CompositeState}
    {operation : AuthoritativeOperation}
    (htarget : ∀ target, operation.target = some target →
      state.lifecycle.current = some target) :
    state.refusesCrossSubject operation = false := by
  unfold CompositeState.refusesCrossSubject
  cases hop : operation.target with
  | none => split <;> simp_all
  | some target =>
      have hcurrent := htarget target hop
      split <;> simp_all

/-- A refused request names a subject other than the scheduled one. -/
theorem refusesCrossSubject_true {state : CompositeState} {operation : AuthoritativeOperation}
    (h : state.refusesCrossSubject operation = true) :
    state.execution.mode = .running ∧
      ∃ caller target, state.lifecycle.current = some caller ∧
        operation.target = some target ∧ target ≠ caller := by
  unfold CompositeState.refusesCrossSubject at h
  cases hmode : state.execution.mode <;> cases hcurrent : state.lifecycle.current <;>
    cases htarget : operation.target <;> simp_all

/-- The subject gate preserves the authoritative runtime invariant. -/
theorem subjectGate_preserves_authoritativeRuntimeWellFormed (state : CompositeState)
    (operation : AuthoritativeOperation) (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (subjectGate state operation).state := by
  rcases subjectGate_cases state operation with ⟨_, _, hsame, _⟩ | ⟨_, hgate, _⟩
  · rw [hsame]; exact hstate
  · rw [hgate]
    exact authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation hstate

/-- Run a finite list of subject requests. -/
def runSubjectOperations (state : CompositeState) :
    List AuthoritativeOperation → CompositeState
  | [] => state
  | operation :: rest => runSubjectOperations (subjectGate state operation).state rest

theorem runSubjectOperations_preserves_authoritativeRuntimeWellFormed (state : CompositeState)
    (operations : List AuthoritativeOperation) (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (runSubjectOperations state operations) := by
  induction operations generalizing state with
  | nil => exact hstate
  | cons operation rest ih =>
      exact ih _ (subjectGate_preserves_authoritativeRuntimeWellFormed state operation hstate)

end LeanOS.FailStop
