import LeanOS.InterruptEntry
import LeanOS.ResumablePreemption

/-!
# Atomic user-fault cleanup and survivor dispatch

This is the first composition slice between the normalized inbound interrupt
contract and the authoritative scheduler/context-bank state.  A valid user
page fault terminates the kernel-selected current subject and selects the next
context in one total transition.  Kernel and terminal entry failures halt;
malformed nonterminal inputs reject without exposing cleanup.
-/
namespace LeanOS.FaultDispatch

open LeanOS
set_option linter.unusedSimpArgs false

inductive RejectReason where
  | malformedEntry (reason : InterruptEntry.RejectReason)
  | wrongPurpose | staleCurrent | staleAddressSpace
  | scheduler (reason : Scheduler.Error) | missingContext | staleContext
  deriving DecidableEq, Repr

inductive Action where
  | idle
  | dispatch (context : ResumablePreemption.Context)
  | rejected (reason : RejectReason)
  | fatal
  deriving DecidableEq, Repr

structure Outcome where
  state : ResumablePreemption.State
  action : Action

def reject (state : ResumablePreemption.State) (reason : RejectReason) : Outcome :=
  { state, action := .rejected reason }

def halt (state : ResumablePreemption.State) : Outcome :=
  { state := { state with halted := true }, action := .fatal }

def terminalEntryFailure : InterruptEntry.RejectReason → Bool
  | .unsupportedVector | .nested => true
  | _ => false

def validUserFault (frame : InterruptEntry.NormalizedFrame) : Bool :=
  frame.vector = 14 && frame.purpose = .userFault && frame.origin = .user &&
    frame.errorCode.isSome && frame.cs % 4 = 3 && frame.userRsp.isSome &&
    frame.userSs.isSome

/-- Atomically consume one normalized page fault.  Destination identity comes
only from `Scheduler.selectNext`; the selected kernel-owned context is consumed
from the existing resumable bank and its address space is installed through
the existing TLB transition. -/
def dispatch (state : ResumablePreemption.State)
    (entry : InterruptEntry.Result) : Outcome :=
  if state.halted then halt state
  else match entry with
  | .fatal reason =>
      if terminalEntryFailure reason then halt state
      else reject state (.malformedEntry reason)
  | .accepted frame =>
      if frame.origin = .kernel then halt state
      else if !validUserFault frame then reject state .wrongPurpose
      else match state.scheduler.lifecycle.current with
      | none => reject state .staleCurrent
      | some current =>
          if frame.currentSubject != current then reject state .staleCurrent
          else if frame.activeAddressSpace != current ||
              state.scheduler.lifecycle.addressOwner current != some current ||
              state.translations.active != some current ||
              state.translations.virtual.owner current != some current then
            reject state .staleAddressSpace
          else
            let cleaned := ResumablePreemption.cleanupSubject state current
            let selected := Scheduler.selectNext cleaned.scheduler
            match selected.result with
            | .rejected reason => reject state (.scheduler reason)
            | .accepted none =>
                { state := { cleaned with scheduler := selected.state }, action := .idle }
            | .accepted (some trusted) =>
                match ResumablePreemption.contextFor cleaned.contexts
                    trusted.currentSubject with
                | none => reject state .missingContext
                | some context =>
                    if context.owner != trusted.currentSubject ||
                        context.addressSpace != trusted.activeAddressSpace ||
                        Interrupt.validSavedUserFrame context.frame != true ||
                        selected.state.lifecycle.capabilities.subjects context.owner != true ||
                        selected.state.lifecycle.runnable context.owner != true ||
                        selected.state.lifecycle.addressOwner context.addressSpace !=
                          some context.owner then
                      reject state .staleContext
                    else
                      { state := { cleaned with
                          scheduler := selected.state
                          contexts := ResumablePreemption.eraseContext cleaned.contexts context.owner
                          translations := TLB.switch cleaned.translations context.addressSpace }
                        action := .dispatch context }

theorem total state entry : ∃ outcome, dispatch state entry = outcome :=
  ⟨_, rfl⟩

theorem deterministic state entry first second
    (hfirst : dispatch state entry = first)
    (hsecond : dispatch state entry = second) : first = second := by
  rw [← hfirst, hsecond]

/-- Every typed nonfatal rejection is atomic: lifecycle, scheduler queue,
context bank, mappings, translations, and the halt latch are all unchanged. -/
theorem rejected_unchanged state entry reason
    (h : (dispatch state entry).action = .rejected reason) :
    (dispatch state entry).state = state := by
  simp only [dispatch] at h ⊢
  split <;> simp_all [halt, reject]
  split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]

/-- The authoritative fatal primitive changes only the absorbing latch. -/
theorem halt_preserves_authoritative_stores state :
    (halt state).state.halted = true ∧
      (halt state).state.scheduler = state.scheduler ∧
      (halt state).state.contexts = state.contexts ∧
      (halt state).state.translations = state.translations := by
  simp [halt]

theorem kernel_origin_is_fatal state frame
    (hrunning : state.halted = false)
    (horigin : frame.origin = .kernel) :
    dispatch state (.accepted frame) = halt state := by
  simp [dispatch, hrunning, horigin]

theorem nested_is_fatal state (hrunning : state.halted = false) :
    dispatch state (.fatal .nested) = halt state := by
  simp [dispatch, hrunning, terminalEntryFailure]

/-- A dispatched context is exactly the deterministic scheduler selection and
is live, runnable, and address-space-owned in the post-state. -/
theorem dispatched_context_safe state entry context
    (h : (dispatch state entry).action = .dispatch context) :
    let next := (dispatch state entry).state
    next.scheduler.lifecycle.capabilities.subjects context.owner = true ∧
      next.scheduler.lifecycle.runnable context.owner = true ∧
      next.scheduler.lifecycle.addressOwner context.addressSpace = some context.owner := by
  generalize hd : dispatch state entry = outcome at h ⊢
  cases outcome with
  | mk next action =>
    simp only at h ⊢
    subst action
    simp only [dispatch] at hd
    split at hd <;> try simp_all [halt, reject]
    split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals split at hd <;> try simp_all [halt, reject]
    all_goals rcases hd with ⟨rfl, rfl⟩
    all_goals grind

/-- The cleanup primitive used by every successful branch removes both live
identity and the authoritative resumable slot for the faulting subject. -/
theorem cleanup_nonresumption state subject :
    ResumablePreemption.contextFor
        (ResumablePreemption.cleanupSubject state subject).contexts subject = none ∧
      (ResumablePreemption.cleanupSubject state subject).scheduler.lifecycle.capabilities.subjects
        subject = false :=
  ⟨ResumablePreemption.cleanup_removes_context state subject,
    ResumablePreemption.cleanup_terminates_subject state subject⟩

end LeanOS.FaultDispatch
