import LeanOS.Interrupt
import LeanOS.KernelRootPublication

/-!
Return preparation under the closed kernel root, followed by a terminal-only
machine tail. Root construction, registry ownership, immutable frame storage,
actual CR3 execution/readback, and IRET remain trusted implementation boundaries.
This composition neither admits a platform nor implements a machine return.
-/
namespace LeanOS.KernelRootReturn

open LeanOS.Interrupt LeanOS.X86PageTable

/-- A trusted registry binds root identities to already constructed tables.
The caller retains this registry and subject/lifecycle authority throughout the
return. It must establish that `closedRoot` actually excludes protected frames.
An arbitrary numeric equality with `closedRoot` is not a closure proof. -/
structure Context where
  closedRoot : UInt64
  activeRoot : UInt64
  current : KernelRootPublication.State
  controls : KernelRootPublication.Controls
  interruptsEnabled : Bool
  tables : UInt64 → Option PageTable

structure Plan where
  request : UserReturnRequest
  before : KernelRootPublication.State
  after : KernelRootPublication.State
  targetRoot : UInt64
  effect : KernelRootPublication.Effect

inductive Error where
  | notClosed | interruptsEnabled | unsupportedControls | invalidRoot | missingTable
  | returnRejected (reason : ReturnRejectReason)
  deriving DecidableEq, Repr

/-- Preparation only returns a plan. The input state is not published or
mutated. The pending root is checked by the existing return validator separately
from the currently active closed root. No wrong-CR3 exception is introduced. -/
def prepare (context : Context) (request : UserReturnRequest) : Except Error Plan :=
  if context.activeRoot != context.closedRoot then .error .notClosed
  else if context.interruptsEnabled then .error .interruptsEnabled
  else if context.controls.pcid || context.controls.globalPages then
    .error .unsupportedControls
  else if request.expectedCr3 = 0 || request.expectedCr3 % 4096 != 0 ||
      request.expectedCr3 = context.closedRoot then .error .invalidRoot
  else
    match validateUserReturn request with
    | .rejected reason => .error (.returnRejected reason)
    | .accepted attested =>
      match context.tables attested.expectedCr3 with
      | none => .error .missingTable
      | some target =>
        let publication := KernelRootPublication.publish context.current target context.controls
        .ok { request := attested, before := context.current, after := publication.state,
              targetRoot := attested.expectedCr3, effect := publication.effect }

/-- No ordinary-C state exists in the tail. `reloadVerified` is a report from
the checked machine primitive, not a claim that a CR3 comparison alone suffices.
Interruption/failure terminate even after successful reload; they never resume
this plan. Terminal cleanup itself must use the separately verified entry path. -/
inductive Phase where
  | awaitingReload | awaitingIret | user | terminal
  deriving DecidableEq, Repr

inductive Event where
  | reloadVerified | reloadFailed | interrupted | iretCompleted
  deriving DecidableEq, Repr

def advance (phase : Phase) (event : Event) : Phase :=
  match phase, event with
  | .awaitingReload, .reloadVerified => .awaitingIret
  | .awaitingIret, .iretCompleted => .user
  | .terminal, _ => .terminal
  | _, _ => .terminal

theorem terminal_absorbing event : advance .terminal event = .terminal := by
  cases event <;> rfl

theorem interruption_terminal phase : advance phase .interrupted = .terminal := by
  cases phase <;> rfl

theorem failed_reload_terminal phase : advance phase .reloadFailed = .terminal := by
  cases phase <;> rfl

theorem user_requires_iret phase event (h : advance phase event = .user) :
    phase = .awaitingIret ∧ event = .iretCompleted := by
  cases phase <;> cases event <;> simp_all [advance]

theorem iret_requires_reload phase event (h : advance phase event = .awaitingIret) :
    phase = .awaitingReload ∧ event = .reloadVerified := by
  cases phase <;> cases event <;> simp_all [advance]

theorem preparation_requires_closed context request plan
    (h : prepare context request = .ok plan) :
    context.activeRoot = context.closedRoot ∧ context.interruptsEnabled = false ∧
      context.controls.pcid = false ∧ context.controls.globalPages = false := by
  unfold prepare at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all

/-- The machine tail carries the exact plan, with no replacement-frame input. -/
structure Tail where
  plan : Plan
  phase : Phase

def step (tail : Tail) (event : Event) : Tail :=
  { tail with phase := advance tail.phase event }

theorem step_preserves_plan tail event : (step tail event).plan = tail.plan := rfl

/-- Frame attestation is inherited from the existing return policy. -/
theorem prepared_request_validated context request plan
    (h : prepare context request = .ok plan) :
    validateUserReturn request = .accepted plan.request := by
  unfold prepare at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all
  cases h
  rfl

theorem prepared_request_exact context request plan
    (h : prepare context request = .ok plan) : plan.request = request :=
  accepted_attests_exact_request _ _ (prepared_request_validated _ _ _ h)

theorem prepared_publication context request plan
    (h : prepare context request = .ok plan) :
    plan.before = context.current ∧ plan.targetRoot = request.expectedCr3 ∧
      plan.effect = .reloadRoot ∧ plan.after.cache = [] := by
  have exactRequest := prepared_request_exact _ _ _ h
  unfold prepare at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h
  cases h
  simp_all [KernelRootPublication.publish]

end LeanOS.KernelRootReturn
