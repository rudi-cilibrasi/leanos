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
changes nothing (`CompositeState.refusesCrossSubject`).  Otherwise it is
exactly `authoritativeGate`.

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

/-- The result a subject observes. -/
inductive SubjectGateResult where
  /-- The kernel performed the operation; its exact gate result. -/
  | gate (result : AuthoritativeGateResult)
  /-- The one fixed refusal of a cross-subject request. -/
  | crossSubjectRefused
  deriving DecidableEq, Repr

structure SubjectGateOutcome where
  state : CompositeState
  result : SubjectGateResult

/-- **The subject-facing gate.** -/
def subjectGate (state : CompositeState) (operation : AuthoritativeOperation) :
    SubjectGateOutcome :=
  if state.refusesCrossSubject operation then { state, result := .crossSubjectRefused }
  else
    let outcome := authoritativeGate state operation
    { state := outcome.state, result := .gate outcome.result }

theorem subjectGate_refused {state : CompositeState} {operation : AuthoritativeOperation}
    (h : state.refusesCrossSubject operation = true) :
    subjectGate state operation = { state, result := .crossSubjectRefused } := by
  simp [subjectGate, h]

theorem subjectGate_of_not_refused {state : CompositeState} {operation : AuthoritativeOperation}
    (h : state.refusesCrossSubject operation = false) :
    subjectGate state operation =
      { state := (authoritativeGate state operation).state
        result := .gate (authoritativeGate state operation).result } := by
  simp [subjectGate, h]

/-- The gate either refuses without effect or is the authoritative gate. -/
theorem subjectGate_cases (state : CompositeState) (operation : AuthoritativeOperation) :
    ((subjectGate state operation).state = state ∧
        (subjectGate state operation).result = .crossSubjectRefused) ∨
      ((subjectGate state operation).state = (authoritativeGate state operation).state ∧
        (subjectGate state operation).result =
          .gate (authoritativeGate state operation).result) := by
  cases h : state.refusesCrossSubject operation
  · rw [subjectGate_of_not_refused h]; exact .inr ⟨rfl, rfl⟩
  · rw [subjectGate_refused h]; exact .inl ⟨rfl, rfl⟩

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
  rcases subjectGate_cases state operation with ⟨hsame, _⟩ | ⟨hgate, _⟩
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
