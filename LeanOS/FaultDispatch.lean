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

/-- Explicit attacker data is not consulted by fault cleanup or survivor
selection. -/
def dispatchWithPayload {Payload : Type} (state : ResumablePreemption.State)
    (entry : InterruptEntry.Result) (_payload : Payload) : Outcome :=
  dispatch state entry

theorem attacker_payload_independent {Payload : Type} state entry
    (left right : Payload) :
    dispatchWithPayload state entry left = dispatchWithPayload state entry right := by
  rfl

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

/-- A survivor-dispatch outcome carries the cleanup boundary into the returned
state: the faulting subject is dead, absent from the ready queue and current
slot, and has no resumable context. -/
theorem dispatched_nonresumption state entry context
    (hdispatch : (dispatch state entry).action = .dispatch context) :
    ∃ faulting,
      (dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        faulting ∉ (dispatch state entry).state.scheduler.ready ∧
        (dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (dispatch state entry).state.contexts faulting = none := by
  generalize hd : dispatch state entry = outcome at hdispatch ⊢
  cases outcome with
  | mk next action =>
    simp only at hdispatch ⊢
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
    all_goals
      let faulting := state.scheduler.lifecycle.current.getD 0
      have hdead := ResumablePreemption.cleanup_terminates_subject state faulting
      have habsent := ResumablePreemption.cleanup_removes_scheduler_membership state faulting
      have hcontext := ResumablePreemption.cleanup_removes_context state faulting
      refine ⟨faulting, ?_⟩
      simp_all only [Option.getD_some]
      grind [Scheduler.selectNext, Scheduler.reject,
        ResumablePreemption.eraseContext, ResumablePreemption.contextFor,
        List.find?_eq_none]

private theorem cleanupCurrent_preserves_coreWellFormed state subject
    (hstate : ResumablePreemption.WellFormed state)
    (hcurrent : state.scheduler.lifecycle.current = some subject) :
    ResumablePreemption.CleanupCoreWellFormed
      (ResumablePreemption.cleanupSubject state subject) := by
  exact ResumablePreemption.cleanupSubject_preserves_coreWellFormed
    state subject hstate (by
      simp [ResumablePreemption.cleanupSubject, SubjectLifecycle.terminateState,
        hcurrent])

/-- Fault dispatch preserves the scheduler/lifecycle invariant and the bounded
no-PCID translation-cache invariant as one composite transition. -/
theorem dispatch_preserves_scheduler_and_tlb state entry
    (hstate : ResumablePreemption.WellFormed state) :
    Scheduler.WellFormed (dispatch state entry).state.scheduler ∧
      TLB.Coherent (dispatch state entry).state.translations := by
  have hparts := hstate
  rcases hparts with ⟨hscheduler, _, _, _, _, _, _, _, _, htlb⟩
  simp only [dispatch]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals (try split) <;> try simp_all [halt, reject]
  all_goals
    have hcore := cleanupCurrent_preserves_coreWellFormed state
      (state.scheduler.lifecycle.current.getD 0) hstate (by simp_all)
    simp_all
    rcases hcore with ⟨hcleanScheduler, _, _, _, _, _, _, hcleanTlb⟩
    constructor
    · exact Scheduler.selectNext_preserves_wellFormed _ hcleanScheduler
    · first | exact hcleanTlb | exact TLB.switch_coherent _ _

/-- A successful dispatch consumes exactly the post-cleanup FIFO head. -/
theorem dispatch_uses_survivor_head state entry context
    (h : (dispatch state entry).action = .dispatch context) :
    ∃ faulting rest,
      (ResumablePreemption.cleanupSubject state faulting).scheduler.ready =
        context.owner :: rest := by
  simp only [dispatch] at h
  split at h <;> try simp_all [halt, reject]
  split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals grind [Scheduler.selectNext, Scheduler.ownsAddressSpace, Scheduler.reject]

/-- Idle is exposed only after cleanup and an actually empty survivor queue. -/
private theorem selectNext_none_eq scheduler
    (h : (Scheduler.selectNext scheduler).result = .accepted none) :
    Scheduler.selectNext scheduler = { state := scheduler, result := .accepted none } := by
  grind [Scheduler.selectNext, Scheduler.reject]

theorem idle_is_clean_empty state entry
    (h : (dispatch state entry).action = .idle) :
    ∃ faulting,
      (dispatch state entry).state = ResumablePreemption.cleanupSubject state faulting ∧
      (dispatch state entry).state.scheduler.ready = [] ∧
      (dispatch state entry).state.scheduler.lifecycle.current = none := by
  simp only [dispatch] at h ⊢
  split at h <;> try simp_all [halt, reject]
  split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals split at h <;> try simp_all [halt, reject]
  all_goals (try split at h) <;> try simp_all [halt, reject]
  all_goals (try split at h) <;> try simp_all [halt, reject]
  all_goals (try split at h) <;> try simp_all [halt, reject]
  all_goals
    have hselected := selectNext_none_eq _ (by assumption)
    simp_all [hselected]
    grind [Scheduler.selectNext, Scheduler.reject]

/-- The idle success branch has the same non-resumption boundary as survivor
dispatch; an empty queue never turns the terminated subject into a fallback. -/
theorem idle_nonresumption state entry
    (hidle : (dispatch state entry).action = .idle) :
    ∃ faulting,
      (dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        faulting ∉ (dispatch state entry).state.scheduler.ready ∧
        (dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (dispatch state entry).state.contexts faulting = none := by
  rcases idle_is_clean_empty state entry hidle with
    ⟨faulting, hstate, _, _⟩
  rw [hstate]
  exact ⟨faulting,
    ResumablePreemption.cleanup_terminates_subject state faulting,
    (ResumablePreemption.cleanup_removes_scheduler_membership state faulting).1,
    (ResumablePreemption.cleanup_removes_scheduler_membership state faulting).2,
    ResumablePreemption.cleanup_removes_context state faulting⟩

/-- Every successful composite result excludes resumption of the subject that
faulted, regardless of whether the deterministic scheduler finds a survivor. -/
theorem successful_nonresumption state entry
    (hsuccess : (dispatch state entry).action = .idle ∨
      ∃ context, (dispatch state entry).action = .dispatch context) :
    ∃ faulting,
      (dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        faulting ∉ (dispatch state entry).state.scheduler.ready ∧
        (dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (dispatch state entry).state.contexts faulting = none := by
  rcases hsuccess with hidle | ⟨context, hdispatch⟩
  · exact idle_nonresumption state entry hidle
  · exact dispatched_nonresumption state entry context hdispatch

end LeanOS.FaultDispatch
