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
  r8 : UInt64
  r9 : UInt64
  r10 : UInt64
  r11 : UInt64
  r12 : UInt64
  r13 : UInt64
  r14 : UInt64
  r15 : UInt64
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
  /-- Irreversible execution latch.  This is the resumable layer's projection
  of the repository-wide fail-stop mode; once set, no later call may restore. -/
  halted : Bool := false

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
    context.addressSpace = context.owner ∧
    state.scheduler.lifecycle.capabilities.subjects context.owner = true ∧
    state.scheduler.lifecycle.runnable context.owner = true ∧
    state.scheduler.lifecycle.addressOwner context.addressSpace = some context.owner

/-- Every queued subject has a restorable context, and every suspended context
belongs to the ready queue.  An `.initial` context may be staged before its
subject is first added to the queue; this is the only permitted non-ready bank
entry.  A current subject needs a nonempty queue for a resumable timer tick. -/
def ReadyContextAgreement (state : State) : Prop :=
  (∀ subject, subject ∈ state.scheduler.ready →
    ∃ context, context ∈ state.contexts ∧ context.owner = subject) ∧
  (∀ context, context ∈ state.contexts →
    context.kind = .suspended → context.owner ∈ state.scheduler.ready) ∧
  (state.scheduler.lifecycle.current.isSome → state.scheduler.ready ≠ [])

/-- The modeled CR3 and page-table ownership view are projections of the same
authoritative lifecycle used by the scheduler.  This prevents a switch from
silently repairing a stale active space or entering a destination whose page
tables are attributed to another subject. -/
def TranslationAgreement (state : State) : Prop :=
  state.translations.virtual.owner = state.scheduler.lifecycle.addressOwner ∧
    match state.scheduler.lifecycle.current with
    | none => state.translations.active = none
    | some subject => state.translations.active = some subject

/-- The scheduler and virtual-memory model share one capability registry, and
the latter carries its complete mapping/lifecycle invariant.  Keeping this in
the composite predicate prevents cleanup from manufacturing authority by
copying between independently well-formed capability projections. -/
def VirtualAgreement (state : State) : Prop :=
  state.translations.virtual.memory.capabilities =
      state.scheduler.lifecycle.capabilities ∧
    VirtualMapping.LifecycleWellFormed state.translations.virtual

/-- The lifecycle's resource projections agree with the type of each live
capability object.  Object identifiers share one namespace, so this rules out
an identifier being treated as owned memory (and retired with that owner)
while the virtual projection simultaneously treats it as a live address
space owned by another subject. -/
def ResourceKindAgreement (state : State) : Prop :=
  (∀ object owner frame,
    state.scheduler.lifecycle.ownedMemory object = some (owner, frame) →
      state.scheduler.lifecycle.capabilities.kinds object = some .memory) ∧
  (∀ object owner,
    state.scheduler.lifecycle.endpointOwner object = some owner →
      state.scheduler.lifecycle.capabilities.kinds object = some .endpoint)

/-- In addition to scheduler invariants, the bank has unique, live ownership,
and never contains the currently executing context. -/
def WellFormed (state : State) : Prop :=
  Scheduler.WellFormed state.scheduler ∧
    state.contexts.length ≤ state.capacity ∧
    state.contexts.Pairwise (fun first second => first.owner ≠ second.owner) ∧
    (∀ context, context ∈ state.contexts → validContext state context) ∧
    (∀ subject, state.scheduler.lifecycle.current = some subject →
      contextFor state.contexts subject = none) ∧
    ReadyContextAgreement state ∧
    TranslationAgreement state ∧
    VirtualAgreement state ∧
    ResourceKindAgreement state ∧
    TLB.Coherent state.translations

theorem wellFormed_set_halted state halted :
    WellFormed { state with halted := halted } ↔ WellFormed state := by
  rfl

inductive Error where
  | nonTimer | fatalEntry | malformedIncoming | noCurrent | contextMismatch | duplicateSave
  | staleActiveSpace | bankFull | schedulerRejected | noDestination | staleDestination
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  restored : Option Context
  error : Option Error

def reject (state : State) (reason : Error) : Outcome :=
  { state, restored := none, error := some reason }

def halt (state : State) : Outcome :=
  { state := { state with halted := true }, restored := none, error := some .fatalEntry }

/-- One accepted timer entry validates and saves the current user frame,
performs the authoritative scheduler step, consumes exactly the selected
context, and flushes cached translations by the no-PCID `TLB.switch` model. -/
def switch (state : State) (interruptState : Interrupt.State)
    (incomingFrame : Interrupt.HardwareFrame) (incomingRegisters : Registers) : Outcome :=
  if state.halted then reject state .fatalEntry
  else match (Interrupt.dispatchHardware interruptState incomingFrame).action with
  | .fatal _ => halt state
  | .timer =>
    if Interrupt.validUserReturn incomingFrame != true then reject state .malformedIncoming
    else match state.scheduler.lifecycle.current with
      | none => reject state .noCurrent
      | some current =>
        if interruptState.context.currentSubject != current ||
            interruptState.context.activeAddressSpace != current then
          reject state .contextMismatch
        else if state.translations.active != some current ||
            state.translations.virtual.owner current != some current then
          reject state .staleActiveSpace
        else if (contextFor state.contexts current).isSome then reject state .duplicateSave
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
                    some destination.owner ||
                  state.translations.virtual.owner destination.addressSpace !=
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
    (hreason : reason ≠ .fatalEntry)
    (h : (switch state interruptState frame registers).error = some reason) :
    (switch state interruptState frame registers).state = state := by
  simp only [switch] at h ⊢
  split <;> simp_all [reject, halt]
  split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
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
  split <;> simp_all [reject, halt]
  split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
  all_goals split <;> simp_all [reject]
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
  split at h <;> try simp_all [reject, halt]
  split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
  all_goals split at h <;> try simp_all [reject]
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
    split at hs <;> try simp_all [reject, halt]
    split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
    all_goals split at hs <;> try simp_all [reject]
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
  split <;> try simp_all [reject, halt]
  split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals
    exact ⟨Scheduler.tick_preserves_wellFormed _ hscheduler,
      TLB.switch_coherent _ _⟩

private theorem accepted_tick_is_select scheduler current selected
    (hcurrent : scheduler.lifecycle.current = some current)
    (hselected : (Scheduler.tick scheduler).result = .accepted (some selected)) :
    Scheduler.tick scheduler = Scheduler.selectNext { scheduler with
      ready := scheduler.ready ++ [current]
      lifecycle := { scheduler.lifecycle with current := none } } := by
  simp only [Scheduler.tick, Scheduler.yield, hcurrent]
  split
  · rename_i hfull
    unfold Scheduler.tick Scheduler.yield at hselected
    simp [hcurrent, hfull, Scheduler.reject] at hselected
  generalize hs : Scheduler.selectNext { scheduler with
    ready := scheduler.ready ++ [current]
    lifecycle := { scheduler.lifecycle with current := none } } = outcome
  cases outcome with
  | mk next result =>
    cases result with
    | rejected reason =>
      have hrejected : (Scheduler.tick scheduler).result = .rejected reason := by
        simp [Scheduler.tick, Scheduler.yield, hcurrent, *, Scheduler.reject]
      rw [hrejected] at hselected
      contradiction
    | accepted context => simp_all

private theorem accepted_tick_facts scheduler current selected
    (hcurrent : scheduler.lifecycle.current = some current)
    (hselected : (Scheduler.tick scheduler).result = .accepted (some selected)) :
    let next := (Scheduler.tick scheduler).state
    next.lifecycle.current = some selected.currentSubject ∧
      next.lifecycle.capabilities = scheduler.lifecycle.capabilities ∧
      next.lifecycle.runnable = scheduler.lifecycle.runnable ∧
      next.lifecycle.addressOwner = scheduler.lifecycle.addressOwner ∧
      next.lifecycle.ownedMemory = scheduler.lifecycle.ownedMemory ∧
      next.lifecycle.endpointOwner = scheduler.lifecycle.endpointOwner ∧
      selected.activeAddressSpace = selected.currentSubject := by
  have heq := accepted_tick_is_select scheduler current selected hcurrent hselected
  rw [heq] at hselected ⊢
  grind [Scheduler.selectNext, Scheduler.ownsAddressSpace, Scheduler.reject]

private theorem accepted_tick_rotates_ready scheduler current selected
    (hcurrent : scheduler.lifecycle.current = some current)
    (hready : scheduler.ready ≠ [])
    (hselected : (Scheduler.tick scheduler).result = .accepted (some selected)) :
    ∃ rest, scheduler.ready = selected.currentSubject :: rest ∧
      (Scheduler.tick scheduler).state.ready = rest ++ [current] := by
  have heq := accepted_tick_is_select scheduler current selected hcurrent hselected
  rw [heq] at hselected ⊢
  cases hqueue : scheduler.ready with
  | nil => contradiction
  | cons queued rest =>
    simp only [hqueue, List.cons_append, Scheduler.selectNext] at hselected ⊢
    split at hselected <;> simp_all [Scheduler.reject]
    next space hspace =>
      have : queued = selected.currentSubject := by grind
      subst queued
      grind

/-- A well-formed resumable state cannot accept a timer selection for a
subject whose kernel-owned context is absent.  The destination is valid and
its address space is exactly the scheduler-selected address space. -/
theorem accepted_tick_has_restorable_destination state current selected
    (hstate : WellFormed state)
    (hcurrent : state.scheduler.lifecycle.current = some current)
    (hselected : (Scheduler.tick state.scheduler).result = .accepted (some selected)) :
    ∃ destination,
      contextFor state.contexts selected.currentSubject = some destination ∧
      validContext state destination ∧
      destination.owner = selected.currentSubject ∧
      destination.addressSpace = selected.activeAddressSpace := by
  rcases hstate with ⟨_, _, _, hvalid, _, hagreement, _, _, _, _⟩
  rcases accepted_tick_rotates_ready state.scheduler current selected hcurrent
      (hagreement.2.2 (by simp [hcurrent])) hselected with ⟨rest, hqueue, _⟩
  obtain ⟨queued, hqueuedMem, hqueuedOwner⟩ :=
    hagreement.1 selected.currentSubject (by simp [hqueue])
  have hdestinationSome : (contextFor state.contexts selected.currentSubject).isSome := by
    simp only [contextFor, List.find?_isSome]
    exact ⟨queued, hqueuedMem, by simpa using hqueuedOwner⟩
  rw [Option.isSome_iff_exists] at hdestinationSome
  obtain ⟨destination, hdestination⟩ := hdestinationSome
  refine ⟨destination, hdestination, hvalid destination ?_,
    contextFor_owner _ _ _ hdestination, ?_⟩
  · exact List.mem_of_find?_eq_some hdestination
  · have howner := contextFor_owner _ _ _ hdestination
    have hspace := (accepted_tick_facts state.scheduler current selected
      hcurrent hselected).2.2.2.2
    have hvalidDestination := hvalid destination
      (List.mem_of_find?_eq_some hdestination)
    simp only [validContext] at hvalidDestination
    grind

/-- Every save/select/restore transition preserves the complete composite
invariant, including bounded unique ownership and validity of the rewritten
context bank. -/
theorem switch_preserves_wellFormed state interruptState frame registers
    (hstate : WellFormed state) :
    WellFormed (switch state interruptState frame registers).state := by
  simp only [switch]
  split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject, halt, wellFormed_set_halted]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  all_goals split <;> try simp_all [reject]
  next action haction hframe maybeCurrent current hcurrent hbinding hactive hnone hroom
      schedulerResult selected hselected maybeDestination destination hdestination
      hdestinationValid =>
    rcases hstate with
      ⟨hscheduler, hcapacity, hunique, hvalid, habsent, hagreement,
        htranslations, hvirtual, hkinds, htlb⟩
    have hscheduler' := Scheduler.tick_preserves_wellFormed state.scheduler hscheduler
    obtain ⟨hnextCurrent, hcapabilities, hrunnable, haddressOwner, hownedMemory,
      hendpointOwner, hselectedSpace⟩ :=
      accepted_tick_facts state.scheduler current selected hcurrent hselected
    obtain ⟨rest, hqueue, hnextReady⟩ := accepted_tick_rotates_ready
      state.scheduler current selected hcurrent
        (hagreement.2.2 (by simp [hcurrent])) hselected
    have hselectedNe : selected.currentSubject ≠ current := by
      intro hequal
      rw [hequal, hnone] at hdestination
      contradiction
    have hnoCurrentOwner : ∀ context, context ∈ state.contexts →
        context.owner ≠ current := by
      simpa [contextFor, List.find?_eq_none] using hnone
    have hcurrentValid :
        state.scheduler.lifecycle.capabilities.subjects current = true ∧
          state.scheduler.lifecycle.runnable current = true ∧
          state.scheduler.lifecycle.addressOwner current = some current := by
      grind [Scheduler.WellFormed, Scheduler.ownsAddressSpace]
    refine ⟨hscheduler', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, TLB.switch_coherent _ _⟩
    · simp only [List.length_cons]
      calc
        (eraseContext state.contexts selected.currentSubject).length + 1 ≤
            state.contexts.length + 1 := by
              exact Nat.add_le_add_right (List.length_filter_le _ _) 1
        _ ≤ state.capacity := hroom
    · simp only [List.pairwise_cons]
      refine ⟨?_, hunique.filter _⟩
      intro context hcontext
      exact Ne.symm (hnoCurrentOwner context (List.mem_filter.mp hcontext).1)
    · intro context hcontext
      rcases List.mem_cons.mp hcontext with rfl | hcontext
      · exact ⟨hframe, rfl, by
          simpa [hcapabilities, hrunnable, haddressOwner] using hcurrentValid⟩
      · have hold := hvalid context (List.mem_filter.mp hcontext).1
        simpa [validContext, hcapabilities, hrunnable, haddressOwner] using hold
    · intro subject hsubject
      have : subject = selected.currentSubject := by grind
      subst subject
      simp [contextFor, eraseContext, Ne.symm hselectedNe]
    · refine ⟨?_, ?_, ?_⟩
      · intro subject hsubject
        rw [hnextReady] at hsubject
        have hcases : subject ∈ rest ∨ subject = current := by
          simpa using hsubject
        rcases hcases with hrest | hsubjectCurrent
        · obtain ⟨context, hcontextMem, hcontextOwner⟩ := hagreement.1 subject (by
            rw [hqueue]
            simp [hrest])
          have hsubjectNe : subject ≠ selected.currentSubject := by
            intro heq
            subst subject
            have := hscheduler.2.1
            rw [hqueue] at this
            simp_all
          have hcurrentNe : current ≠ subject := by
            intro heq
            subst subject
            have hcurrentNotReady := hscheduler.2.2.2.2 current hcurrent |>.2.2.2
            have hcurrentRest : current ∈ rest := by simpa [heq] using hrest
            apply hcurrentNotReady
            rw [hqueue]
            exact List.mem_cons_of_mem _ hcurrentRest
          refine ⟨context, ?_⟩
          exact ⟨by simp [eraseContext, hcontextMem, hcontextOwner, hsubjectNe],
            hcontextOwner⟩
        · subst subject
          refine ⟨{
            owner := current
            addressSpace := current
            frame := frame
            registers := registers
            kind := .suspended }, ?_⟩
          simp
      · intro context hcontext hsuspended
        rcases List.mem_cons.mp hcontext with hsaved | hretained
        · subst context
          simp [hnextReady]
        · have holdMem := (List.mem_filter.mp hretained).1
          have holdReady := hagreement.2.1 context holdMem hsuspended
          have hnotSelected : context.owner ≠ selected.currentSubject := by
            simpa using (List.mem_filter.mp hretained).2
          rw [hqueue] at holdReady
          rw [hnextReady]
          simp_all
      · intro _
        rw [hnextReady]
        simp
    · rcases htranslations with ⟨hownerProjection, hactiveProjection⟩
      constructor
      · simpa [TLB.switch, haddressOwner] using hownerProjection
      · simp [TLB.switch, hnextCurrent, hselectedSpace]
    · rcases hvirtual with ⟨hcapabilityProjection, hvirtualWellFormed⟩
      constructor
      · simpa [TLB.switch, hcapabilities] using hcapabilityProjection
      · simpa [TLB.switch] using hvirtualWellFormed
    · simpa [ResourceKindAgreement, hcapabilities, hownedMemory, hendpointOwner] using hkinds

/-- Attacker-controlled general registers can affect only the saved payload;
they cannot influence which bank entry is selected for restoration. -/
theorem registers_cannot_select_restore state interruptState frame first second :
    (switch state interruptState frame first).restored =
      (switch state interruptState frame second).restored := by
  simp only [switch]
  split <;> try rfl
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl
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

/-- Retire every address-space capability object owned by `subject`, including
all delegated handles.  `SubjectLifecycle.terminateState` does not know that
address-space identifiers are capability objects, so the resumable composition
must close that lifecycle projection explicitly. -/
def retireOwnedAddressSpaces (state : SubjectLifecycle.State) (subject : SubjectId)
    (base : Capability.State) : Capability.State :=
  { base with
    objects := fun object =>
      if state.addressOwner object = some subject then false
      else base.objects object
    kinds := fun object =>
      if state.addressOwner object = some subject then none
      else base.kinds object
    slots := fun holder slot =>
      match base.slots holder slot with
      | none => none
      | some capability =>
          if state.addressOwner capability.object = some subject then none
          else some capability }

theorem retireOwnedAddressSpaces_preserves_retired_object state subject base object
    (hretired : base.objects object = false) :
    (retireOwnedAddressSpaces state subject base).objects object = false := by
  simp [retireOwnedAddressSpaces, hretired]

/-- Subject termination is one composite cleanup step: lifecycle ownership,
scheduler membership, the resumable slot, and cached translations disappear
together.  The scheduler model currently identifies each subject's owned
address space with the same identifier; this is the explicit no-reuse boundary
used by `Scheduler.ownsAddressSpace`. -/
def cleanupSubject (state : State) (subject : SubjectId) : State :=
  let oldLifecycle := state.scheduler.lifecycle
  let terminated := SubjectLifecycle.terminateState oldLifecycle subject
  let lifecycle := { terminated with
    capabilities := retireOwnedAddressSpaces oldLifecycle subject terminated.capabilities }
  let virtual := state.translations.virtual
  let mappings := fun addressSpace page =>
    match virtual.mappings addressSpace page with
    | some mapping =>
        if lifecycle.addressOwner addressSpace = none then none
        else if lifecycle.capabilities.objects mapping.object != true then none
        else if lifecycle.mapping addressSpace page = some mapping.object then some mapping
        else none
    | none => none
  { state with
    scheduler := {
      state.scheduler with
      lifecycle := lifecycle
      ready := state.scheduler.ready.filter (· != subject) }
    contexts := eraseContext state.contexts subject
    translations := {
      TLB.invalidateSpace state.translations subject with
      virtual := { virtual with
        memory := { virtual.memory with capabilities := lifecycle.capabilities }
        owner := lifecycle.addressOwner
        mappings := mappings }
      active := lifecycle.current } }

theorem cleanup_removes_context state subject :
    contextFor (cleanupSubject state subject).contexts subject = none := by
  simp [cleanupSubject, contextFor, eraseContext, List.find?_eq_none]

theorem cleanup_removes_scheduler_membership state subject :
    subject ∉ (cleanupSubject state subject).scheduler.ready ∧
      (cleanupSubject state subject).scheduler.lifecycle.current ≠ some subject := by
  simp [cleanupSubject, SubjectLifecycle.terminateState]

theorem cleanup_terminates_subject state subject :
    (cleanupSubject state subject).scheduler.lifecycle.capabilities.subjects subject = false := by
  simp [cleanupSubject, retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
    SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool]

/-- Every address-space object owned by the terminated subject is retired from
both lifecycle projections rather than merely becoming ownerless. -/
theorem cleanup_retires_owned_address_space state subject addressSpace
    (howner : state.scheduler.lifecycle.addressOwner addressSpace = some subject) :
    (cleanupSubject state subject).scheduler.lifecycle.capabilities.objects addressSpace = false ∧
      (cleanupSubject state subject).scheduler.lifecycle.capabilities.kinds addressSpace = none ∧
      (cleanupSubject state subject).translations.virtual.memory.capabilities.objects
        addressSpace = false := by
  simp [cleanupSubject, retireOwnedAddressSpaces, howner]

/-- Delegated capabilities cannot keep a destroyed address space reachable. -/
theorem cleanup_clears_owned_address_space_handles state subject holder slot capability
    (hslot : state.scheduler.lifecycle.capabilities.slots holder slot = some capability)
    (howner : state.scheduler.lifecycle.addressOwner capability.object = some subject) :
    (cleanupSubject state subject).scheduler.lifecycle.capabilities.slots holder slot = none ∧
      (cleanupSubject state subject).translations.virtual.memory.capabilities.slots
        holder slot = none := by
  simp [cleanupSubject, retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
    SubjectLifecycle.terminatedCapabilities, hslot, howner]
  split <;> simp_all

/-- Cleanup removes every encoded page-table mapping in an address space whose
owner is terminated; changing only the owner projection would leave stale
authoritative mappings behind. -/
theorem cleanup_removes_owned_space_mappings state subject addressSpace page
    (howner : state.scheduler.lifecycle.addressOwner addressSpace = some subject) :
    (cleanupSubject state subject).translations.virtual.mappings addressSpace page = none := by
  simp [cleanupSubject, SubjectLifecycle.terminateState, howner]
  split <;> rfl

/-- Cleanup also removes a page-table entry whose backing object is retired by
subject termination, even when the entry occurs in a different address space.
Keeping such an entry would violate `VirtualMapping.WellFormed` because the
mapping would no longer name a live capability object. -/
theorem cleanup_removes_retired_object_mapping state subject addressSpace page mapping
    (hmapping : state.translations.virtual.mappings addressSpace page = some mapping)
    (hretired :
      (SubjectLifecycle.terminateState state.scheduler.lifecycle subject).capabilities.objects
        mapping.object = false) :
    (cleanupSubject state subject).translations.virtual.mappings addressSpace page = none := by
  have hretired' := retireOwnedAddressSpaces_preserves_retired_object
    state.scheduler.lifecycle subject
    (SubjectLifecycle.terminateState state.scheduler.lifecycle subject).capabilities
    mapping.object hretired
  simp [cleanupSubject, hmapping, hretired']

/-- Lifecycle and translation ownership are updated as one cleanup projection;
terminating the current subject also clears the modeled active address space. -/
theorem cleanup_preserves_translationAgreement state subject :
    TranslationAgreement (cleanupSubject state subject) := by
  simp only [TranslationAgreement, cleanupSubject]
  split <;> constructor
  · trivial
  · assumption
  · trivial
  · assumption

/-- Cleanup preserves the mapping-safety portion of the virtual lifecycle from
the composite pre-state.  Any retained mapping still has a live owner and
backing object, agrees with the authoritative lifecycle mapping, and keeps the
owner's capability witness; mappings whose authority is retired are filtered
out by the cleanup transition. -/
theorem cleanup_preserves_virtualMappingWellFormed state subject
    (hstate : WellFormed state) :
    VirtualMapping.WellFormed (cleanupSubject state subject).translations.virtual := by
  rcases hstate with
    ⟨hscheduler, _, _, _, _, _, htranslations, hvirtual, _, _⟩
  rcases hscheduler with ⟨hlifecycle, _, _, _, _⟩
  rcases hlifecycle with ⟨_, _, haddressLive, _, _, _⟩
  rcases hvirtual.2 with ⟨hwell, _, _, _⟩
  unfold VirtualMapping.WellFormed at hwell ⊢
  constructor
  · intro addressSpace owner howner
    have hownerFacts :
        state.scheduler.lifecycle.addressOwner addressSpace ≠ some subject ∧
          state.scheduler.lifecycle.addressOwner addressSpace = some owner := by
      simpa [cleanupSubject, SubjectLifecycle.terminateState] using howner
    have hownerOld := hownerFacts.2
    have hlive := haddressLive addressSpace owner hownerOld
    have hownerNe : owner ≠ subject := by
      intro heq
      subst owner
      simp [cleanupSubject, SubjectLifecycle.terminateState, hownerOld] at howner
    simpa [cleanupSubject, retireOwnedAddressSpaces,
      SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
      SubjectLifecycle.setBool, hownerNe] using hlive
  · intro addressSpace page mapping hmapping
    have hmappingOld :
        state.translations.virtual.mappings addressSpace page = some mapping := by
      simp only [cleanupSubject] at hmapping
      split at hmapping <;> simp_all
    have hownerSome :
        (SubjectLifecycle.terminateState state.scheduler.lifecycle subject).addressOwner
          addressSpace ≠ none := by
      simp only [cleanupSubject] at hmapping
      split at hmapping <;> simp_all
    have hobjectLive :
        (retireOwnedAddressSpaces state.scheduler.lifecycle subject
          (SubjectLifecycle.terminateState state.scheduler.lifecycle subject).capabilities).objects
            mapping.object = true := by
      simp only [cleanupSubject] at hmapping
      split at hmapping <;> simp_all
    rcases hwell.2 addressSpace page mapping hmappingOld with
      ⟨owner, frame, hownerOld, hpermissions, hbinding, howned, hread, hwrite⟩
    have hownerLifecycle :
        state.scheduler.lifecycle.addressOwner addressSpace = some owner := by
      rw [← htranslations.1]
      exact hownerOld
    have hownerNe : owner ≠ subject := by
      intro heq
      subst owner
      simp [SubjectLifecycle.terminateState, hownerLifecycle] at hownerSome
    have hownerNew :
        (SubjectLifecycle.terminateState state.scheduler.lifecycle subject).addressOwner
          addressSpace = some owner := by
      simp [SubjectLifecycle.terminateState, hownerLifecycle, hownerNe]
    have preserveAuthority (right : Capability.Right)
        (hauthority : Capability.HasAuthority
          state.translations.virtual.memory.capabilities owner mapping.object right) :
        Capability.HasAuthority
          (retireOwnedAddressSpaces state.scheduler.lifecycle subject
            (SubjectLifecycle.terminateState state.scheduler.lifecycle subject).capabilities)
          owner mapping.object right := by
      rcases hauthority with ⟨slot, capability, hslot, hobject, hright⟩
      refine ⟨slot, capability, ?_, hobject, hright⟩
      rw [hvirtual.1] at hslot
      simp [retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
        SubjectLifecycle.terminatedCapabilities] at hobjectLive
      simp [retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
        SubjectLifecycle.terminatedCapabilities, hslot, hownerNe, hobject,
        hobjectLive]
    refine ⟨owner, frame, ?_, hpermissions, hbinding, howned, ?_, ?_⟩
    · simpa [cleanupSubject] using hownerNew
    · intro hpermission
      simpa [cleanupSubject] using
        preserveAuthority Capability.Right.read (hread hpermission)
    · intro hpermission
      simpa [cleanupSubject] using
        preserveAuthority Capability.Right.write (hwrite hpermission)

/-- Cleanup preserves ready/context agreement whenever it leaves a queued
destination for a still-current subject.  If cleanup removes the final peer,
the resulting single runnable subject deliberately leaves the resumable-state
domain: a timer tick has no distinct context to restore. -/
theorem cleanup_preserves_readyContextAgreement state subject
    (hstate : ReadyContextAgreement state)
    (hpeer : (cleanupSubject state subject).scheduler.lifecycle.current.isSome →
      (cleanupSubject state subject).scheduler.ready ≠ []) :
    ReadyContextAgreement (cleanupSubject state subject) := by
  refine ⟨?_, ?_, hpeer⟩
  · intro queued hqueued
    have hqueuedOld : queued ∈ state.scheduler.ready := by
      simpa [cleanupSubject] using (List.mem_filter.mp hqueued).1
    have hqueuedNe : queued ≠ subject := by
      simpa using (List.mem_filter.mp hqueued).2
    obtain ⟨context, hcontext, howner⟩ := hstate.1 queued hqueuedOld
    refine ⟨context, ?_, howner⟩
    simp [cleanupSubject, eraseContext, hcontext, howner, hqueuedNe]
  · intro context hcontext hsuspended
    have hcontextOld := (List.mem_filter.mp hcontext).1
    have hownerNe : context.owner ≠ subject := by
      simpa using (List.mem_filter.mp hcontext).2
    have hreadyOld := hstate.2.1 context hcontextOld hsuspended
    simp [cleanupSubject, hreadyOld, hownerNe]

/-- The cleanup properties derived here solely from the pre-state invariant.
This deliberately excludes the virtual-lifecycle and resource-kind fields:
their preservation still needs a proof about the composed capability cleanup,
not assumptions that restate those desired postconditions. -/
def CleanupCoreWellFormed (state : State) : Prop :=
  Scheduler.WellFormed state.scheduler ∧
    state.contexts.length ≤ state.capacity ∧
    state.contexts.Pairwise (fun first second => first.owner ≠ second.owner) ∧
    (∀ context, context ∈ state.contexts → validContext state context) ∧
    (∀ subject, state.scheduler.lifecycle.current = some subject →
      contextFor state.contexts subject = none) ∧
    ReadyContextAgreement state ∧
    TranslationAgreement state ∧
    TLB.Coherent state.translations

/-- Regression for the cross-kind cleanup bug: a well-formed composite state
cannot give one live identifier both memory ownership and address-space
ownership, so terminating the memory owner cannot retire another subject's
address space through an identifier collision. -/
theorem wellFormed_excludes_memory_addressSpace_alias state object memoryOwner frame
    addressOwner (hstate : WellFormed state)
    (hmemory : state.scheduler.lifecycle.ownedMemory object = some (memoryOwner, frame))
    (haddress : state.scheduler.lifecycle.addressOwner object = some addressOwner) : False := by
  rcases hstate with ⟨_, _, _, _, _, _, htranslations, hvirtual, hkinds, _⟩
  have hmemoryKind := hkinds.1 object memoryOwner frame hmemory
  have haddressKind := (hvirtual.2.2.2.1 object addressOwner (by
    rw [htranslations.1]
    exact haddress)).2.1
  rw [hvirtual.1] at haddressKind
  simp [hmemoryKind] at haddressKind

/-- Composite cleanup preserves the lifecycle resource-kind projection.  The
proof rules out both ways the capability cleanup could otherwise erase the
kind of a retained resource: ownership by the terminated subject and a
cross-kind alias with one of that subject's other resources. -/
theorem cleanup_preserves_resourceKindAgreement state subject
    (hstate : WellFormed state) :
    ResourceKindAgreement (cleanupSubject state subject) := by
  have hfull := hstate
  rcases hstate with ⟨_, _, _, _, _, _, _, _, hkinds, _⟩
  constructor
  · intro object owner frame howned
    have holdOwned : state.scheduler.lifecycle.ownedMemory object = some (owner, frame) := by
      simp only [cleanupSubject, SubjectLifecycle.terminateState] at howned
      split at howned <;> simp_all
    have hownerNe : owner ≠ subject := by
      intro heq
      subst owner
      simp [cleanupSubject, SubjectLifecycle.terminateState, holdOwned] at howned
    have hmemoryKind := hkinds.1 object owner frame holdOwned
    have hendpointNe : state.scheduler.lifecycle.endpointOwner object ≠ some subject := by
      intro hendpoint
      have hendpointKind := hkinds.2 object subject hendpoint
      simp [hmemoryKind] at hendpointKind
    have haddressNe : state.scheduler.lifecycle.addressOwner object ≠ some subject := by
      intro haddress
      exact wellFormed_excludes_memory_addressSpace_alias state object owner frame subject
        hfull holdOwned haddress
    simp [cleanupSubject, retireOwnedAddressSpaces,
      SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
      holdOwned, hownerNe, hendpointNe, haddressNe, hmemoryKind]
  · intro object owner hendpoint
    have holdEndpoint : state.scheduler.lifecycle.endpointOwner object = some owner := by
      simp [cleanupSubject, SubjectLifecycle.terminateState] at hendpoint
      exact hendpoint.2
    have hownerNe : owner ≠ subject := by
      intro heq
      subst owner
      simp [cleanupSubject, SubjectLifecycle.terminateState, holdEndpoint] at hendpoint
    have hendpointKind := hkinds.2 object owner holdEndpoint
    have hmemoryNe : ∀ memoryOwner frame,
        state.scheduler.lifecycle.ownedMemory object ≠ some (memoryOwner, frame) := by
      intro memoryOwner frame hmemory
      have hmemoryKind := hkinds.1 object memoryOwner frame hmemory
      simp [hmemoryKind] at hendpointKind
    have hmemoryAny :
        Option.any (fun ownership => decide (ownership.1 = subject))
          (state.scheduler.lifecycle.ownedMemory object) = false := by
      cases hmemory : state.scheduler.lifecycle.ownedMemory object with
      | none => simp
      | some ownership =>
        rcases ownership with ⟨memoryOwner, frame⟩
        exact False.elim (hmemoryNe memoryOwner frame hmemory)
    have haddressNe : state.scheduler.lifecycle.addressOwner object ≠ some subject := by
      intro haddress
      rcases hfull with ⟨_, _, _, _, _, _, htranslations, hvirtual, _, _⟩
      have haddressKind := (hvirtual.2.2.2.1 object subject (by
        rw [htranslations.1]
        exact haddress)).2.1
      rw [hvirtual.1] at haddressKind
      simp [hendpointKind] at haddressKind
    simp [cleanupSubject, retireOwnedAddressSpaces,
      SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
      holdEndpoint, hownerNe, hmemoryAny, haddressNe, hendpointKind]

/-- Subject cleanup preserves the scheduler, context-bank, ownership projection,
and bounded TLB invariants derived from a well-formed pre-state.  This theorem
intentionally makes no full `WellFormed` claim until virtual-lifecycle cleanup
preservation is proved rather than assumed. -/
theorem cleanupSubject_preserves_coreWellFormed state subject
    (hstate : WellFormed state)
    (hreadyPeer : (cleanupSubject state subject).scheduler.lifecycle.current.isSome →
      (cleanupSubject state subject).scheduler.ready ≠ []) :
    CleanupCoreWellFormed (cleanupSubject state subject) := by
  rcases hstate with
    ⟨hscheduler, hcapacity, hunique, hvalid, habsent, hagreement,
      _htranslations, _hvirtual, _hkinds, htlb⟩
  refine ⟨?_, ?_, ?_, ?_, ?_,
    cleanup_preserves_readyContextAgreement state subject hagreement hreadyPeer,
    cleanup_preserves_translationAgreement state subject,
    ?_⟩
  · unfold Scheduler.WellFormed at hscheduler ⊢
    rcases hscheduler with ⟨hlifecycle, hnodup, hbound, hready, hcurrent⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hterminated := SubjectLifecycle.terminateState_preserves_wellFormed
        state.scheduler.lifecycle subject hlifecycle
      unfold SubjectLifecycle.WellFormed at hterminated ⊢
      simpa [cleanupSubject, retireOwnedAddressSpaces,
        SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
        SubjectLifecycle.setBool] using hterminated
    · exact hnodup.filter (fun candidate => candidate != subject)
    · exact Nat.le_trans (List.length_filter_le _ _) hbound
    · intro candidate hcandidate
      have hold : candidate ∈ state.scheduler.ready := (List.mem_filter.mp hcandidate).1
      have hne : candidate ≠ subject := by simpa using (List.mem_filter.mp hcandidate).2
      rcases hready candidate hold with ⟨hlive, hrunnable, hspace⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [cleanupSubject, retireOwnedAddressSpaces,
          SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
          SubjectLifecycle.setBool, hne] using hlive
      · simpa [cleanupSubject, SubjectLifecycle.terminateState,
          SubjectLifecycle.setBool, hne] using hrunnable
      · have haddress : state.scheduler.lifecycle.addressOwner candidate = some candidate := by
          unfold Scheduler.ownsAddressSpace at hspace
          split at hspace
          · assumption
          · simp at hspace
        unfold Scheduler.ownsAddressSpace
        simp only [cleanupSubject]
        have haddressNe : state.scheduler.lifecycle.addressOwner candidate ≠ some subject := by
          rw [haddress]
          simp [hne]
        simp [SubjectLifecycle.terminateState, haddressNe, haddress, hne]
    · intro candidate hcandidate
      have hne : candidate ≠ subject := by
        intro heq
        subst candidate
        simp [cleanupSubject, SubjectLifecycle.terminateState] at hcandidate
      have hcurrentFacts : state.scheduler.lifecycle.current ≠ some subject ∧
          state.scheduler.lifecycle.current = some candidate := by
        simpa [cleanupSubject, SubjectLifecycle.terminateState, hne] using hcandidate
      have holdCurrent : state.scheduler.lifecycle.current = some candidate := hcurrentFacts.2
      rcases hcurrent candidate holdCurrent with ⟨hlive, hrunnable, hspace, hnotReady⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [cleanupSubject, retireOwnedAddressSpaces,
          SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
          SubjectLifecycle.setBool, hne] using hlive
      · simpa [cleanupSubject, SubjectLifecycle.terminateState,
          SubjectLifecycle.setBool, hne] using hrunnable
      · have haddress : state.scheduler.lifecycle.addressOwner candidate = some candidate := by
          unfold Scheduler.ownsAddressSpace at hspace
          split at hspace
          · assumption
          · simp at hspace
        unfold Scheduler.ownsAddressSpace
        simp only [cleanupSubject]
        have haddressNe : state.scheduler.lifecycle.addressOwner candidate ≠ some subject := by
          rw [haddress]
          simp [hne]
        simp [SubjectLifecycle.terminateState, haddressNe, haddress, hne]
      · simp [cleanupSubject, hnotReady]
  · exact Nat.le_trans (List.length_filter_le _ _) hcapacity
  · exact hunique.filter (fun context => context.owner != subject)
  · intro context hcontext
    have holdMem := (List.mem_filter.mp hcontext).1
    have hownerNe : context.owner ≠ subject := by
      simpa using (List.mem_filter.mp hcontext).2
    rcases hvalid context holdMem with ⟨hframe, hspaceEq, hlive, hrunnable, howner⟩
    refine ⟨hframe, hspaceEq, ?_, ?_, ?_⟩
    · simpa [cleanupSubject, retireOwnedAddressSpaces,
        SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
        SubjectLifecycle.setBool, hownerNe] using hlive
    · simpa [cleanupSubject, SubjectLifecycle.terminateState,
        SubjectLifecycle.setBool, hownerNe] using hrunnable
    · have hspaceNe : state.scheduler.lifecycle.addressOwner context.addressSpace ≠
          some subject := by
        rw [howner]
        simp [hownerNe]
      simpa [cleanupSubject, SubjectLifecycle.terminateState, hspaceNe] using howner
  · intro candidate hcurrent
    have hne : candidate ≠ subject := by
      intro heq
      subst candidate
      simp [cleanupSubject, SubjectLifecycle.terminateState] at hcurrent
    have holdCurrent : state.scheduler.lifecycle.current = some candidate := by
      have hcurrentFacts : state.scheduler.lifecycle.current ≠ some subject ∧
          state.scheduler.lifecycle.current = some candidate := by
        simpa [cleanupSubject, SubjectLifecycle.terminateState, hne] using hcurrent
      exact hcurrentFacts.2
    have holdAbsent := habsent candidate holdCurrent
    apply List.find?_eq_none.mpr
    intro context hmem
    have holdNoOwner := List.find?_eq_none.mp holdAbsent context
      (List.mem_filter.mp hmem).1
    simpa using holdNoOwner
  · exact Nat.le_trans (TLB.erase_space_length state.translations.entries subject) htlb

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
    basePointer := marker + 6
    r8 := marker + 8
    r9 := marker + 9
    r10 := marker + 10
    r11 := marker + 11
    r12 := marker + 12
    r13 := marker + 13
    r14 := marker + 14
    r15 := marker + 15 }

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
    translations := { translations with
      virtual := { translations.virtual with owner := (demoLifecycle 1).addressOwner }
      active := some 1 } }

/-- Executable cleanup fixture with distinct address-space and memory object
identifiers.  It catches the earlier cross-kind collision bug by requiring
termination of subject 1 to retire its own resources without retiring subject
2's live address space. -/
private def cleanupRegressionState (translations : TLB.State) : State :=
  let base := roundTripStart translations
  let capabilities : Capability.State := {
    (demoLifecycle 1).capabilities with
    objects := fun object => object = 1 || object = 2 || object = 10
    kinds := fun object =>
      if object = 1 || object = 2 then some .addressSpace
      else if object = 10 then some .memory else none }
  let lifecycle : SubjectLifecycle.State := {
    demoLifecycle 1 with
    capabilities := capabilities
    ownedMemory := fun object => if object = 10 then some (1, 10) else none }
  { base with
    scheduler := { base.scheduler with lifecycle := lifecycle }
    translations := { base.translations with
      virtual := { base.translations.virtual with
        memory := { base.translations.virtual.memory with capabilities := capabilities }
        owner := lifecycle.addressOwner } } }

example (translations : TLB.State) :
    let cleaned := cleanupSubject (cleanupRegressionState translations) 1
    cleaned.scheduler.lifecycle.capabilities.objects 1 = false ∧
      cleaned.scheduler.lifecycle.capabilities.objects 10 = false ∧
      cleaned.scheduler.lifecycle.capabilities.objects 2 = true ∧
      cleaned.scheduler.lifecycle.capabilities.kinds 2 = some .addressSpace ∧
      cleaned.scheduler.lifecycle.addressOwner 2 = some 2 := by
  simp [cleanupRegressionState, roundTripStart, demoLifecycle, cleanupSubject,
    retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
    SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool]

/-- Negative regression for the former cross-kind cleanup collision.  Object
`2` is still the live address space of subject `2`, but the lifecycle also
attributes that identifier as memory owned by subject `3`.  The composite
resource-kind invariant rejects this pre-state; without that gate, cleaning
subject `3` retires object `2` while leaving its address-space owner intact. -/
private def crossKindAliasRegressionState (translations : TLB.State) : State :=
  let base := cleanupRegressionState translations
  { base with
    scheduler := { base.scheduler with
      lifecycle := { base.scheduler.lifecycle with
        ownedMemory := fun object => if object = 2 then some (3, 10) else none } } }

example (translations : TLB.State) :
    ¬ ResourceKindAgreement (crossKindAliasRegressionState translations) := by
  intro hagreement
  have hkind := hagreement.1 2 3 10 (by
    simp [crossKindAliasRegressionState])
  simp [crossKindAliasRegressionState, cleanupRegressionState, roundTripStart,
    demoLifecycle] at hkind

example (translations : TLB.State) :
    let cleaned := cleanupSubject (crossKindAliasRegressionState translations) 3
    cleaned.scheduler.lifecycle.addressOwner 2 = some 2 ∧
      cleaned.scheduler.lifecycle.capabilities.objects 2 = false := by
  simp [crossKindAliasRegressionState, cleanupRegressionState, roundTripStart,
    demoLifecycle, cleanupSubject, retireOwnedAddressSpaces,
    SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
    SubjectLifecycle.setBool]

/-- Executable retained-mapping regression for the mapping-safety preservation
lemma: cleaning subject `1` leaves subject `2`'s mapping and its read-authority
witness intact. -/
private def cleanupMappingRegressionState (translations : TLB.State) : State :=
  let base := cleanupRegressionState translations
  let capability : Capability.Capability :=
    { object := 10, kind := .memory, rights := { read := true } }
  let capabilities : Capability.State := {
    base.scheduler.lifecycle.capabilities with
    slots := fun holder slot =>
      if holder = 2 ∧ slot = 0 then some capability else none }
  let lifecycle : SubjectLifecycle.State := {
    base.scheduler.lifecycle with
    capabilities := capabilities
    ownedMemory := fun object => if object = 10 then some (2, 10) else none
    mapping := fun addressSpace page =>
      if addressSpace = 2 ∧ page = 7 then some 10 else none }
  { base with
    scheduler := { base.scheduler with lifecycle := lifecycle }
    translations := { base.translations with
      virtual := { base.translations.virtual with
        memory := { base.translations.virtual.memory with capabilities := capabilities }
        mappings := fun addressSpace page =>
          if addressSpace = 2 ∧ page = 7 then
            some { object := 10, permissions := { read := true } }
          else none } } }

example (translations : TLB.State) :
    let cleaned := cleanupSubject (cleanupMappingRegressionState translations) 1
    cleaned.translations.virtual.mappings 2 7 =
        some { object := 10, permissions := { read := true } } ∧
      Capability.HasAuthority cleaned.translations.virtual.memory.capabilities
        2 10 .read := by
  simp [cleanupMappingRegressionState, cleanupRegressionState, roundTripStart,
    demoLifecycle, cleanupSubject, retireOwnedAddressSpaces,
    SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
    Capability.HasAuthority]
  exact ⟨0, { object := 10, kind := .memory, rights := { read := true } },
    by rfl, rfl, rfl⟩

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

/- A fatal entry irreversibly closes the resumable path: even a later valid
timer entry cannot expose a context or alter the latched state. -/
example (translations : TLB.State) :
    let fatalFrame := { demoFrame 0x401000 0x801000 0x246 with vector := 77 }
    let halted := (switch (roundTripStart translations) (demoInterrupt 1)
      fatalFrame (demoRegisters 0x10)).state
    halted.halted = true ∧
      (switch halted (demoInterrupt 1) (demoFrame 0x401000 0x801000 0x246)
        (demoRegisters 0x10)).restored = none ∧
      (switch halted (demoInterrupt 1) (demoFrame 0x401000 0x801000 0x246)
        (demoRegisters 0x10)).state = halted := by
  simp [roundTripStart, demoInterrupt, demoLifecycle, demoFrame, demoRegisters,
    switch, Interrupt.dispatchHardware, Interrupt.decodeVector, halt, reject]

/-- A timer entry whose interrupt-side subject/address-space binding disagrees
with the scheduler is rejected before any context is saved or restored. -/
example (translations : TLB.State) :
    (switch (roundTripStart translations) (demoInterrupt 2)
      (demoFrame 0x401000 0x801000 0x246) (demoRegisters 0x10)).error =
        some .contextMismatch := by
  simp [roundTripStart, demoInterrupt, demoLifecycle, demoFrame, demoRegisters,
    switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, reject]

/-- A scheduler-valid destination is still rejected when the encoded virtual
ownership view attributes its page tables to a different subject. -/
example (translations : TLB.State) :
    let state := roundTripStart translations
    let staleVirtual := { state.translations.virtual with
      owner := fun space => if space = 2 then some 3 else state.translations.virtual.owner space }
    (switch { state with translations := { state.translations with virtual := staleVirtual } }
      (demoInterrupt 1) (demoFrame 0x401000 0x801000 0x246)
      (demoRegisters 0x10)).error = some .staleDestination := by
  simp [roundTripStart, initialContext, demoInterrupt, demoLifecycle, demoFrame,
    demoRegisters, switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, Scheduler.tick, Scheduler.yield, Scheduler.selectNext,
    Scheduler.ownsAddressSpace, contextFor, reject]

/-- A matching active CR3 is insufficient when the encoded virtual-memory
ownership view assigns the current address space to another subject. -/
example (translations : TLB.State) :
    let state := roundTripStart translations
    let staleVirtual := { state.translations.virtual with
      owner := fun space => if space = 1 then some 3 else state.translations.virtual.owner space }
    (switch { state with translations := { state.translations with virtual := staleVirtual } }
      (demoInterrupt 1) (demoFrame 0x401000 0x801000 0x246)
      (demoRegisters 0x10)).error = some .staleActiveSpace := by
  simp [roundTripStart, demoInterrupt, demoLifecycle, demoFrame, demoRegisters,
    switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, reject]

/-- A stale CR3/TLB projection is rejected even when the scheduler and
interrupt-entry projections agree on the current subject. -/
example (translations : TLB.State) :
    let state := roundTripStart translations
    (switch { state with translations := { state.translations with active := some 3 } }
      (demoInterrupt 1) (demoFrame 0x401000 0x801000 0x246)
      (demoRegisters 0x10)).error = some .staleActiveSpace := by
  simp [roundTripStart, demoInterrupt, demoLifecycle, demoFrame, demoRegisters,
    switch, Interrupt.dispatchHardware, Interrupt.decodeVector,
    Interrupt.validUserReturn, reject]

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
