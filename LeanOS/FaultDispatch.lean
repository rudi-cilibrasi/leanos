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
    (hstate : ResumablePreemption.WellFormed state) :
    ResumablePreemption.CleanupCoreWellFormed
      (ResumablePreemption.cleanupSubject state subject) := by
  exact ResumablePreemption.cleanupSubject_preserves_coreWellFormed
    state subject hstate

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
      (state.scheduler.lifecycle.current.getD 0) hstate
    simp_all
    rcases hcore with ⟨hcleanScheduler, _, _, _, _, _, _, hcleanTlb⟩
    constructor
    · exact Scheduler.selectNext_preserves_wellFormed _ hcleanScheduler
    · first | exact hcleanTlb | exact TLB.switch_coherent _ _

private theorem consumeSelected_preserves_wellFormed state trusted context
    (hstate : ResumablePreemption.WellFormed state)
    (hselected : (Scheduler.selectNext state.scheduler).result =
      .accepted (some trusted))
    (hcontext : ResumablePreemption.contextFor state.contexts
      trusted.currentSubject = some context) :
    ResumablePreemption.WellFormed
      { state with
        scheduler := (Scheduler.selectNext state.scheduler).state
        contexts := ResumablePreemption.eraseContext state.contexts context.owner
        translations := TLB.switch state.translations context.addressSpace } := by
  rcases hstate with
    ⟨hscheduler, hcapacity, hunique, hvalid, habsent, hagreement,
      htranslations, hvirtual, hkinds, htlb⟩
  have hcontextOwner := ResumablePreemption.contextFor_owner _ _ _ hcontext
  simp only [Scheduler.selectNext] at hselected
  split at hselected <;> try simp_all [Scheduler.reject]
  split at hselected <;> try simp_all [Scheduler.reject]
  all_goals
    have hcontextMem := List.mem_of_find?_eq_some hcontext
    have hcontextValid := hvalid context hcontextMem
    have hcontextSpace : context.addressSpace = trusted.activeAddressSpace := by
      simp only [ResumablePreemption.validContext] at hcontextValid
      grind [Scheduler.ownsAddressSpace]
    have hpostScheduler := Scheduler.selectNext_preserves_wellFormed
      state.scheduler hscheduler
    have hpostCurrent :
        (Scheduler.selectNext state.scheduler).state.lifecycle.current =
          some trusted.currentSubject := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hcapabilityProjection :
        (Scheduler.selectNext state.scheduler).state.lifecycle.capabilities =
          state.scheduler.lifecycle.capabilities := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hrunnable :
        (Scheduler.selectNext state.scheduler).state.lifecycle.runnable =
          state.scheduler.lifecycle.runnable := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have haddressOwner :
        (Scheduler.selectNext state.scheduler).state.lifecycle.addressOwner =
          state.scheduler.lifecycle.addressOwner := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hownedMemory :
        (Scheduler.selectNext state.scheduler).state.lifecycle.ownedMemory =
          state.scheduler.lifecycle.ownedMemory := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hendpointOwner :
        (Scheduler.selectNext state.scheduler).state.lifecycle.endpointOwner =
          state.scheduler.lifecycle.endpointOwner := by
      grind [Scheduler.selectNext, Scheduler.reject]
    have hselectedSpace : trusted.activeAddressSpace = trusted.currentSubject := by
      grind [Scheduler.ownsAddressSpace]
    refine ⟨hpostScheduler, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, TLB.switch_coherent _ _⟩
    · exact Nat.le_trans (List.length_filter_le _ _) hcapacity
    · exact hunique.filter _
    · intro retained hretained
      have hold := hvalid retained (List.mem_filter.mp hretained).1
      simpa [ResumablePreemption.validContext, TLB.switch, hcapabilityProjection,
        hrunnable, haddressOwner] using hold
    · intro candidate hcurrent
      have hc : candidate = trusted.currentSubject := by grind
      subst candidate
      exact ResumablePreemption.contextFor_erase_self _ _
    · refine ⟨?_, ?_⟩
      · intro queued hqueued
        have hqueuedOld : queued ∈ state.scheduler.ready := by
          simp [Scheduler.selectNext] at hqueued
          simp_all
        obtain ⟨saved, hsaved, howner⟩ := hagreement.1 queued hqueuedOld
        have hne : saved.owner ≠ trusted.currentSubject := by
          intro heq
          have hnotReady := hpostScheduler.2.2.2.2 trusted.currentSubject
            hpostCurrent |>.2.2.2
          apply hnotReady
          have hqueuedEq : queued = trusted.currentSubject := by
            rw [← howner, heq]
          simpa [hqueuedEq] using hqueued
        exact ⟨saved, by
          simp [ResumablePreemption.eraseContext, hsaved, hne], howner⟩
      · intro retained hretained hsuspended
        have holdMem := (List.mem_filter.mp hretained).1
        have holdReady := hagreement.2 retained holdMem hsuspended
        have hne : retained.owner ≠ trusted.currentSubject := by
          simpa using (List.mem_filter.mp hretained).2
        grind [Scheduler.selectNext, Scheduler.reject]
    · rcases htranslations with ⟨howner, hactive⟩
      constructor
      · simpa [TLB.switch, haddressOwner] using howner
      · simp [TLB.switch, hpostCurrent, hcontextSpace, hselectedSpace]
    · rcases hvirtual with ⟨hvirtualCapabilities, hvirtualWellFormed⟩
      exact ⟨by simpa [TLB.switch, hcapabilityProjection] using hvirtualCapabilities,
        by simpa [TLB.switch] using hvirtualWellFormed⟩
    · simpa [ResumablePreemption.ResourceKindAgreement, TLB.switch,
        hcapabilityProjection, hownedMemory, hendpointOwner] using hkinds

private theorem fatal_state_eq_halt state entry
    (h : (dispatch state entry).action = .fatal) :
    (dispatch state entry).state = (halt state).state := by
  simp only [dispatch] at h ⊢
  split <;> try simp_all [halt, reject]
  split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> try simp_all [halt, reject]
  all_goals split <;> simp_all [halt, reject]

private theorem dispatched_is_authoritative_transition state entry context
    (h : (dispatch state entry).action = .dispatch context) :
    ∃ faulting trusted,
      (Scheduler.selectNext
          (ResumablePreemption.cleanupSubject state faulting).scheduler).result =
        .accepted (some trusted) ∧
      ResumablePreemption.contextFor
          (ResumablePreemption.cleanupSubject state faulting).contexts
          trusted.currentSubject = some context ∧
      (dispatch state entry).state =
        { ResumablePreemption.cleanupSubject state faulting with
          scheduler := (Scheduler.selectNext
            (ResumablePreemption.cleanupSubject state faulting).scheduler).state
          contexts := ResumablePreemption.eraseContext
            (ResumablePreemption.cleanupSubject state faulting).contexts context.owner
          translations := TLB.switch
            (ResumablePreemption.cleanupSubject state faulting).translations
            context.addressSpace } := by
  simp only [dispatch] at h ⊢
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
  all_goals rcases h with ⟨rfl⟩
  all_goals grind

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

/-! Executable regressions for the invariant boundary closed by this slice:
one queued survivor becomes the sole current subject, while no survivor yields
idle.  Neither result retains the faulting subject's resumable slot. -/

private def traceCapabilities (survivor : Bool) : Capability.State :=
  { subjects := fun subject => subject = 1 || (survivor && subject = 2)
    objects := fun object => object = 1 || (survivor && object = 2)
    kinds := fun object =>
      if object = 1 || (survivor && object = 2) then some .addressSpace else none
    slots := fun _ _ => none }

private def traceLifecycle (survivor : Bool) : SubjectLifecycle.State :=
  { capabilities := traceCapabilities survivor
    issuedSubjects := fun subject => subject = 1 || (survivor && subject = 2)
    ownedMemory := fun _ => none
    addressOwner := fun space =>
      if space = 1 || (survivor && space = 2) then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject = 1 || (survivor && subject = 2)
    current := some 1 }

private def traceHardwareFrame : Interrupt.HardwareFrame :=
  { vector := 14
    errorCode := 0
    savedPrivilege := .user
    instructionPointer := 0x400200
    stackPointer := 0x500ff8
    codeSelector := 0x23
    stackSelector := 0x1b
    flags := 0x202
    canonicalInstructionPointer := true
    canonicalStackPointer := true
    flagsAllowed := true }

private def traceRegisters : ResumablePreemption.Registers :=
  { accumulator := 0
    base := 0
    count := 0
    data := 0
    source := 0
    destination := 0
    basePointer := 0
    r8 := 0
    r9 := 0
    r10 := 0
    r11 := 0
    r12 := 0
    r13 := 0
    r14 := 0
    r15 := 0 }

private def traceSurvivorContext : ResumablePreemption.Context :=
  { owner := 2
    addressSpace := 2
    frame := traceHardwareFrame
    registers := traceRegisters
    kind := .suspended }

private def traceState (survivor : Bool) : ResumablePreemption.State :=
  let lifecycle := traceLifecycle survivor
  let capabilities := traceCapabilities survivor
  { scheduler := {
      lifecycle
      ready := if survivor then [2] else []
      capacity := 2 }
    contexts := if survivor then [traceSurvivorContext] else []
    capacity := 2
    translations := {
      virtual := {
        memory := {
          capabilities
          allocator := { frames := [], status := fun _ => .free }
          binding := fun _ => none
          issued := fun object => object = 1 || (survivor && object = 2) }
        owner := lifecycle.addressOwner
        mappings := fun _ _ => none
        issuedAddressSpace := fun space => space = 1 || (survivor && space = 2) }
      active := some 1
      entries := [] } }

private def traceEntry : InterruptEntry.Result :=
  .accepted {
    vector := 14
    purpose := .userFault
    origin := .user
    errorCode := some 0
    rip := 0x400100
    cs := 0x23
    flags := 0x202
    userRsp := some 0x500ff8
    userSs := some 0x1b
    currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0
    stackIdentity := 1 }

example : (dispatch (traceState true) traceEntry).action =
    .dispatch traceSurvivorContext := by native_decide

example :
    (dispatch (traceState true) traceEntry).state.scheduler.lifecycle.current = some 2 ∧
      (dispatch (traceState true) traceEntry).state.scheduler.ready = [] ∧
      (dispatch (traceState true) traceEntry).state.scheduler.lifecycle.capabilities.subjects 1 =
        false ∧
      ResumablePreemption.contextFor
        (dispatch (traceState true) traceEntry).state.contexts 1 = none := by
  native_decide

example : (dispatch (traceState false) traceEntry).action = .idle ∧
    (dispatch (traceState false) traceEntry).state.scheduler.lifecycle.current = none ∧
    (dispatch (traceState false) traceEntry).state.scheduler.ready = [] ∧
    ResumablePreemption.contextFor
      (dispatch (traceState false) traceEntry).state.contexts 1 = none := by
  native_decide

/-- The atomic fault transition preserves the complete authoritative runtime
invariant on every result.  In the survivor branch, selecting the ready head
makes it current while consuming exactly its saved context; every unrelated
context and all cleanup-preserved lifecycle/virtual projections remain
unchanged. -/
theorem dispatch_preserves_wellFormed state entry
    (hstate : ResumablePreemption.WellFormed state) :
    ResumablePreemption.WellFormed (dispatch state entry).state := by
  cases haction : (dispatch state entry).action with
  | idle =>
      obtain ⟨faulting, hnext, _, _⟩ := idle_is_clean_empty state entry haction
      rw [hnext]
      exact ResumablePreemption.cleanupSubject_preserves_wellFormed state faulting hstate
  | dispatch context =>
      obtain ⟨faulting, trusted, hselected, hcontext, hnext⟩ :=
        dispatched_is_authoritative_transition state entry context haction
      rw [hnext]
      exact consumeSelected_preserves_wellFormed _ trusted context
        (ResumablePreemption.cleanupSubject_preserves_wellFormed state faulting hstate)
        hselected hcontext
  | rejected reason =>
      rw [rejected_unchanged state entry reason haction]
      exact hstate
  | fatal =>
      rw [fatal_state_eq_halt state entry haction]
      simpa [halt, ResumablePreemption.wellFormed_set_halted] using hstate

end LeanOS.FaultDispatch
