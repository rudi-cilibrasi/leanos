import LeanOS.Preemption
import LeanOS.TLB

/-!
# Bounded resumable preemption

This model makes the machine save area explicit.  Context ownership is stored
in kernel state and destination selection is taken only from `Scheduler.tick`;
no general register is interpreted as a subject or address-space identifier.
The assembly save/restore sequence, `iretq`, CR3 operation, and timer delivery
remain trusted boundaries.
-/
namespace LeanOS.ResumablePreemption

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := Scheduler.SubjectId
abbrev AddressSpaceId := Scheduler.AddressSpaceId

structure Registers where
  accumulator : UInt64
  base : UInt64
  count : UInt64
  data : UInt64
  source : UInt64
  destination : UInt64
  basePointer : UInt64
  deriving BEq, DecidableEq, Repr

inductive ContextKind where | initial | suspended
  deriving BEq, DecidableEq, Repr

/-- Ownership fields are kernel metadata, never copied from user registers. -/
structure Context where
  owner : SubjectId
  addressSpace : AddressSpaceId
  frame : Interrupt.HardwareFrame
  registers : Registers
  kind : ContextKind
  deriving DecidableEq, Repr

structure State where
  scheduler : Scheduler.State
  contexts : List Context
  capacity : Nat
  translations : TLB.State

def contextFor (contexts : List Context) (subject : SubjectId) : Option Context :=
  contexts.find? (fun context => context.owner == subject)

def eraseContext (contexts : List Context) (subject : SubjectId) : List Context :=
  contexts.filter (fun context => context.owner != subject)

theorem contextFor_owner contexts subject context
    (h : contextFor contexts subject = some context) :
    context.owner = subject := by
  simpa [contextFor] using List.find?_some h

theorem contextFor_erase_self contexts subject :
    contextFor (eraseContext contexts subject) subject = none := by
  simp [contextFor, eraseContext, List.find?_eq_none]

/-- Saving a context installs exactly its kernel-owned slot. -/
theorem contextFor_save_consume contexts saved destination :
    contextFor (saved :: eraseContext contexts destination) saved.owner = some saved := by
  simp [contextFor]

def validContext (state : State) (context : Context) : Prop :=
  Interrupt.validUserReturn context.frame = true ∧
    state.scheduler.lifecycle.capabilities.subjects context.owner = true ∧
    state.scheduler.lifecycle.runnable context.owner = true ∧
    state.scheduler.lifecycle.addressOwner context.addressSpace = some context.owner

/-- In addition to scheduler invariants, the bank has unique, live ownership,
and never contains the currently executing context. -/
def WellFormed (state : State) : Prop :=
  Scheduler.WellFormed state.scheduler ∧
    state.contexts.length ≤ state.capacity ∧
    state.contexts.Pairwise (fun first second => first.owner ≠ second.owner) ∧
    (∀ context, context ∈ state.contexts → validContext state context) ∧
    (∀ subject, state.scheduler.lifecycle.current = some subject →
      contextFor state.contexts subject = none) ∧
    TLB.Coherent state.translations

inductive Error where
  | nonTimer | fatalEntry | malformedIncoming | noCurrent | duplicateSave
  | bankFull | schedulerRejected | noDestination | staleDestination
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  restored : Option Context
  error : Option Error

def reject (state : State) (reason : Error) : Outcome :=
  { state, restored := none, error := some reason }

/-- One accepted timer entry validates and saves the current user frame,
performs the authoritative scheduler step, consumes exactly the selected
context, and flushes cached translations by the no-PCID `TLB.switch` model. -/
def switch (state : State) (interruptState : Interrupt.State)
    (incomingFrame : Interrupt.HardwareFrame) (incomingRegisters : Registers) : Outcome :=
  match (Interrupt.dispatchHardware interruptState incomingFrame).action with
  | .fatal _ => reject state .fatalEntry
  | .timer =>
    if Interrupt.validUserReturn incomingFrame != true then reject state .malformedIncoming
    else match state.scheduler.lifecycle.current with
      | none => reject state .noCurrent
      | some current =>
        if (contextFor state.contexts current).isSome then reject state .duplicateSave
        else if state.capacity ≤ state.contexts.length then reject state .bankFull
        else
          let scheduled := Scheduler.tick state.scheduler
          match scheduled.result with
          | .rejected _ => reject state .schedulerRejected
          | .accepted none => reject state .noDestination
          | .accepted (some selected) =>
            match contextFor state.contexts selected.currentSubject with
            | none => reject state .noDestination
            | some destination =>
              if destination.addressSpace != selected.activeAddressSpace ||
                  destination.owner != selected.currentSubject ||
                  Interrupt.validUserReturn destination.frame != true ||
                  scheduled.state.lifecycle.capabilities.subjects destination.owner != true ||
                  scheduled.state.lifecycle.runnable destination.owner != true ||
                  scheduled.state.lifecycle.addressOwner destination.addressSpace !=
                    some destination.owner then
                reject state .staleDestination
              else
                let saved : Context :=
                  { owner := current
                    addressSpace := current
                    frame := incomingFrame
                    registers := incomingRegisters
                    kind := .suspended }
                { state :=
                    { state with
                      scheduler := scheduled.state
                      contexts := saved :: eraseContext state.contexts destination.owner
                      translations := TLB.switch state.translations destination.addressSpace }
                  restored := some destination
                  error := none }
  | _ => reject state .nonTimer

theorem rejected_unchanged state interruptState frame registers reason
    (h : (switch state interruptState frame registers).error = some reason) :
    (switch state interruptState frame registers).state = state := by
  simp only [switch] at h ⊢
  split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]

theorem rejected_exposes_no_restore state interruptState frame registers reason
    (h : (switch state interruptState frame registers).error = some reason) :
    (switch state interruptState frame registers).restored = none := by
  simp only [switch] at h ⊢
  split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]

/-- A successful restore is the context-bank entry named by the scheduler's
trusted result.  In particular, neither the incoming register file nor a
scalar subject word participates in destination selection. -/
theorem restored_context_is_scheduler_selected state interruptState frame registers context
    (h : (switch state interruptState frame registers).restored = some context) :
    ∃ selected,
      (Scheduler.tick state.scheduler).result = .accepted (some selected) ∧
      contextFor state.contexts selected.currentSubject = some context ∧
      context.owner = selected.currentSubject ∧
      context.addressSpace = selected.activeAddressSpace := by
  simp only [switch] at h
  split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> simp_all [reject]

/-- Every successful restore is live in the post-scheduler lifecycle and is
bound there to the address space recorded in its kernel-owned slot. -/
theorem restored_context_is_live_and_owned state interruptState frame registers context
    (h : (switch state interruptState frame registers).restored = some context) :
    let next := (switch state interruptState frame registers).state
    next.scheduler.lifecycle.capabilities.subjects context.owner = true ∧
      next.scheduler.lifecycle.runnable context.owner = true ∧
      next.scheduler.lifecycle.addressOwner context.addressSpace = some context.owner := by
  generalize hs : switch state interruptState frame registers = outcome at h ⊢
  cases outcome with
  | mk next restored error =>
    simp only at h ⊢
    subst restored
    simp only [switch] at hs
    split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals rcases hs with ⟨rfl, rfl, rfl⟩
    all_goals grind

/-- Save/select/restore preserves the already-proved scheduler invariant and
the bounded no-PCID translation-cache invariant.  The stronger context-bank
component is stated separately by the ownership and separation theorems. -/
theorem switch_preserves_scheduler_and_tlb state interruptState frame registers
    (hscheduler : Scheduler.WellFormed state.scheduler)
    (htlb : TLB.Coherent state.translations) :
    Scheduler.WellFormed
        (switch state interruptState frame registers).state.scheduler ∧
      TLB.Coherent (switch state interruptState frame registers).state.translations := by
  simp only [switch]
  split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals exact ⟨Scheduler.tick_preserves_wellFormed _ hscheduler,
    TLB.switch_coherent _ _⟩

/-- Attacker-controlled general registers can affect only the saved payload;
they cannot influence which bank entry is selected for restoration. -/
theorem registers_cannot_select_restore state interruptState frame first second :
    (switch state interruptState frame first).restored =
      (switch state interruptState frame second).restored := by
  simp only [switch]
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> rfl

/-- Saving one owner and consuming another leaves every third subject's slot
byte-for-byte unchanged.  This is the context-bank separation step used by an
accepted switch. -/
theorem save_consume_preserves_other contexts saved destination other context
    (howner : context.owner = other) (hsaved : saved.owner ≠ other)
    (hdestination : destination ≠ other) :
    context ∈ saved :: eraseContext contexts destination ↔ context ∈ contexts := by
  have hcontext : context ≠ saved := by
    intro heq
    apply hsaved
    rw [← heq]
    exact howner
  have hother : other ≠ destination := Ne.symm hdestination
  simp [eraseContext, howner, hcontext, hother]

/-- Subject termination is one composite cleanup step: lifecycle ownership,
scheduler membership, the resumable slot, and cached translations disappear
together.  The scheduler model currently identifies each subject's owned
address space with the same identifier; this is the explicit no-reuse boundary
used by `Scheduler.ownsAddressSpace`. -/
def cleanupSubject (state : State) (subject : SubjectId) : State :=
  { state with
    scheduler := {
      state.scheduler with
      lifecycle := SubjectLifecycle.terminateState state.scheduler.lifecycle subject
      ready := state.scheduler.ready.filter (· != subject) }
    contexts := eraseContext state.contexts subject
    translations := TLB.invalidateSpace state.translations subject }

theorem cleanup_removes_context state subject :
    contextFor (cleanupSubject state subject).contexts subject = none := by
  simp [cleanupSubject, contextFor, eraseContext, List.find?_eq_none]

theorem cleanup_removes_scheduler_membership state subject :
    subject ∉ (cleanupSubject state subject).scheduler.ready ∧
      (cleanupSubject state subject).scheduler.lifecycle.current ≠ some subject := by
  simp [cleanupSubject, SubjectLifecycle.terminateState]

theorem cleanup_terminates_subject state subject :
    (cleanupSubject state subject).scheduler.lifecycle.capabilities.subjects subject = false := by
  simp [cleanupSubject, SubjectLifecycle.terminateState,
    SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool]

private def demoLifecycle (current : SubjectId) : SubjectLifecycle.State :=
  { capabilities := {
      subjects := fun subject => subject = 1 || subject = 2 || subject = 3
      objects := fun _ => false
      kinds := fun _ => none
      slots := fun _ _ => none }
    issuedSubjects := fun subject => subject = 1 || subject = 2 || subject = 3
    ownedMemory := fun _ => none
    addressOwner := fun space =>
      if space = 1 || space = 2 || space = 3 then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject = 1 || subject = 2 || subject = 3
    current := some current }

private def demoInterrupt (current : SubjectId) : Interrupt.State :=
  { lifecycle := demoLifecycle current
    context := {
      currentSubject := current
      activeAddressSpace := current
      kernelStack := 0
      entryActive := false } }

private def demoFrame (rip rsp marker : UInt64) : Interrupt.HardwareFrame :=
  { vector := 32
    errorCode := 0
    savedPrivilege := .user
    instructionPointer := rip
    stackPointer := rsp
    codeSelector := 0x1b
    stackSelector := 0x23
    flags := marker
    canonicalInstructionPointer := true
    canonicalStackPointer := true
    flagsAllowed := true }

private def demoRegisters (marker : UInt64) : Registers :=
  { accumulator := marker
    base := marker + 1
    count := marker + 2
    data := marker + 3
    source := marker + 4
    destination := marker + 5
    basePointer := marker + 6 }

private def initialContext (owner : SubjectId) (marker : UInt64) : Context :=
  { owner
    addressSpace := owner
    frame := demoFrame (0x400000 + marker) (0x800000 + marker) (0x202 + marker)
    registers := demoRegisters marker
    kind := .initial }

private def roundTripStart (translations : TLB.State) : State :=
  { scheduler := {
      lifecycle := demoLifecycle 1
      ready := [2]
      capacity := 3 }
    contexts := [initialContext 2 0x20, initialContext 3 0x30]
    capacity := 3
    translations }

private def switchAToB (translations : TLB.State) : Outcome :=
  switch (roundTripStart translations) (demoInterrupt 1)
    (demoFrame 0x401000 0x801000 0x246) (demoRegisters 0x10)

private def switchBToA (translations : TLB.State) : Outcome :=
  let afterA := (switchAToB translations).state
  switch afterA (demoInterrupt 2)
    (demoFrame 0x402000 0x802000 0x286) (demoRegisters 0x20)

/-- Executable A -> B -> A witness: A's entire suspended return frame and
register file survive B's run, while the queued third subject stays separate. -/
theorem bounded_round_trip_preserves_a (translations : TLB.State) :
    (switchAToB translations).restored = some (initialContext 2 0x20) ∧
    (switchBToA translations).restored = some {
      owner := 1
      addressSpace := 1
      frame := demoFrame 0x401000 0x801000 0x246
      registers := demoRegisters 0x10
      kind := .suspended } ∧
    contextFor (switchBToA translations).state.contexts 3 =
      some (initialContext 3 0x30) := by
  simp [switchAToB, switchBToA, roundTripStart, demoInterrupt, demoLifecycle,
    initialContext, demoFrame, demoRegisters, switch, Interrupt.dispatchHardware,
    Interrupt.decodeVector, Interrupt.validUserReturn, Scheduler.tick, Scheduler.yield,
    Scheduler.selectNext, Scheduler.ownsAddressSpace, contextFor, eraseContext,
    TLB.switch]

example (translations : TLB.State) :
    (switch (roundTripStart translations) (demoInterrupt 1)
      { demoFrame 0x401000 0x801000 0x246 with flagsAllowed := false }
      (demoRegisters 0x10)).error = some .malformedIncoming := by
  simp [roundTripStart, demoInterrupt, demoLifecycle, demoFrame, demoRegisters,
    switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, reject]

example (translations : TLB.State) :
    let state := roundTripStart translations
    let duplicate := initialContext 1 0x10
    (switch { state with contexts := duplicate :: state.contexts } (demoInterrupt 1)
      (demoFrame 0x401000 0x801000 0x246) (demoRegisters 0x10)).error =
        some .duplicateSave := by
  simp [roundTripStart, initialContext, demoInterrupt, demoLifecycle, demoFrame,
    demoRegisters, switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, contextFor, reject]

example (translations : TLB.State) :
    let state := roundTripStart translations
    (switch { state with contexts := eraseContext state.contexts 2 } (demoInterrupt 1)
      (demoFrame 0x401000 0x801000 0x246) (demoRegisters 0x10)).error =
        some .noDestination := by
  simp [roundTripStart, initialContext, demoInterrupt, demoLifecycle, demoFrame,
    demoRegisters, switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, Scheduler.tick, Scheduler.yield, Scheduler.selectNext,
    Scheduler.ownsAddressSpace, contextFor, eraseContext, reject]

example (translations : TLB.State) :
    let state := roundTripStart translations
    let stale := { initialContext 2 0x20 with addressSpace := 3 }
    (switch { state with contexts := stale :: eraseContext state.contexts 2 }
      (demoInterrupt 1) (demoFrame 0x401000 0x801000 0x246)
      (demoRegisters 0x10)).error = some .staleDestination := by
  simp [roundTripStart, initialContext, demoInterrupt, demoLifecycle, demoFrame,
    demoRegisters, switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, Scheduler.tick, Scheduler.yield, Scheduler.selectNext,
    Scheduler.ownsAddressSpace, contextFor, eraseContext, reject]

example (translations : TLB.State) :
    let state := roundTripStart translations
    (switch { state with capacity := state.contexts.length } (demoInterrupt 1)
      (demoFrame 0x401000 0x801000 0x246) (demoRegisters 0x10)).error = some .bankFull := by
  simp [roundTripStart, initialContext, demoInterrupt, demoLifecycle, demoFrame,
    demoRegisters, switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, contextFor, reject]

example (translations : TLB.State) :
    (switchBToA translations).state.translations.active = some 1 ∧
      (switchBToA translations).state.translations.entries = [] := by
  simp [switchAToB, switchBToA, roundTripStart, demoInterrupt, demoLifecycle,
    initialContext, demoFrame, demoRegisters, switch, Interrupt.dispatchHardware,
    Interrupt.decodeVector, Interrupt.validUserReturn, Scheduler.tick, Scheduler.yield,
    Scheduler.selectNext, Scheduler.ownsAddressSpace, contextFor, eraseContext,
    TLB.switch]

/-! The next three executable counterexamples document why the trusted design
does not accept a scalar selector, reuse one global save area, or reload an
address space independently of the restored owner. -/

private def untrustedSelect (contexts : List Context) (subjectWord : SubjectId) :
    Option Context :=
  contextFor contexts subjectWord

example (translations : TLB.State) :
    untrustedSelect (roundTripStart translations).contexts 3 =
      some (initialContext 3 0x30) ∧
    (Scheduler.tick (roundTripStart translations).scheduler).result =
      .accepted (some ⟨2, 2⟩) := by
  simp [untrustedSelect, roundTripStart, initialContext, demoLifecycle, demoFrame,
    demoRegisters, contextFor, Scheduler.tick, Scheduler.yield,
    Scheduler.selectNext, Scheduler.ownsAddressSpace]

private def sharedSaveArea (_old saved : Context) : Context := saved

example :
    sharedSaveArea (initialContext 1 0x10) (initialContext 2 0x20) =
      initialContext 2 0x20 ∧
    sharedSaveArea (initialContext 1 0x10) (initialContext 2 0x20) ≠
      initialContext 1 0x10 := by
  native_decide

example (translations : TLB.State) :
    let restored := initialContext 2 0x20
    (TLB.switch translations 3).active ≠ some restored.addressSpace := by
  simp [initialContext, TLB.switch]

end LeanOS.ResumablePreemption
