import LeanOS.Interrupt
import LeanOS.BootPageTablePlan
import LeanOS.IPCSyscall
import LeanOS.Preemption
import LeanOS.CapabilityTransfer
import LeanOS.ResumablePreemption

/-!
# Irreversible exception fail-stop model

This composite layer makes interrupt entry transactional and fatality absorbing.
The underlying interrupt classifier remains the source of vector, origin, and
subject-containment policy; this layer is the authoritative execution latch.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

inductive FatalReason where
  | kernelFault | unsupportedVector | nestedEntry | doubleFault
  | invalidUserReturn (purpose : Interrupt.ReturnPurpose)
      (reason : Interrupt.ReturnRejectReason)
  deriving DecidableEq, Repr

/-- Kernel-owned entry identity.  General-purpose registers are absent. -/
structure ActiveEntry where
  vector : Nat
  origin : Interrupt.Privilege
  frame : Interrupt.HardwareFrame
  deriving DecidableEq, Repr

structure HaltRecord where
  reason : FatalReason
  active : Option ActiveEntry
  incomingVector : Nat
  incomingOrigin : Interrupt.Privilege
  deriving DecidableEq, Repr

inductive Mode where
  | running
  | handling (entry : ActiveEntry)
  | halted (record : HaltRecord)
  deriving DecidableEq, Repr

structure ReturnAddressSpace where
  subject : Interrupt.SubjectId
  expectedCr3 : UInt64
  codeRegion : Interrupt.UserRegion
  stackRegion : Interrupt.UserRegion
  deriving DecidableEq, Repr

structure State where
  core : Interrupt.State
  mode : Mode
  /-- Kernel-owned projection of the installed page-table plan.  The return
  selector reads this view; an outgoing proposal cannot supply it. -/
  returnAddressSpace : Interrupt.AddressSpaceId → Option ReturnAddressSpace := fun _ => none
  /-- Proof-carrying page-table plan installed for the live boot image. -/
  returnPlan : Option BootPageTablePlan.Plan := none
  /-- Kernel-selected purpose and address-space policy for the next return. -/
  returnAuthority : Interrupt.TrustedReturnAuthority := Interrupt.defaultReturnAuthority
  /-- True only after `selectReturnAuthority` has bound the authority record to
  the live scheduler subject and its installed address-space view. -/
  returnAuthorityArmed : Bool := false
  /-- The kernel-owned SMAP AC override. Entry closes it before classification. -/
  copyOverride : Bool := false

def ActiveEntry.WellFormed (entry : ActiveEntry) : Prop :=
  entry.vector = entry.frame.vector ∧ entry.origin = entry.frame.savedPrivilege

def ReturnAddressSpace.planBound (view : ReturnAddressSpace)
    (addressSpace : Interrupt.AddressSpaceId) (plan : BootPageTablePlan.Plan) : Bool :=
  let selected :=
    if view.subject = 1 && addressSpace = 1 then
      some (BootPageTablePlan.Space.subjectA, BootPageTablePlan.Owner.subjectA)
    else if view.subject = 2 && addressSpace = 2 then
      some (BootPageTablePlan.Space.subjectB, BootPageTablePlan.Owner.subjectB)
    else none
  match selected with
  | none => false
  | some (space, owner) =>
      let codeFirst := view.codeRegion.first.toNat
      let codeLast := view.codeRegion.pastLast.toNat
      let stackFirst := view.stackRegion.first.toNat
      let stackLast := view.stackRegion.pastLast.toNat
      view.expectedCr3 = UInt64.ofNat (plan.rootFrame space * X86PageTable.pageBytes) &&
        codeFirst % X86PageTable.pageBytes = 0 &&
        codeLast = codeFirst + X86PageTable.pageBytes &&
        stackFirst % X86PageTable.pageBytes = 0 &&
        stackLast = stackFirst + X86PageTable.pageBytes &&
        plan.hasPolicyLeaf space (codeFirst / X86PageTable.pageBytes) .userText owner &&
        plan.hasPolicyLeaf space (stackFirst / X86PageTable.pageBytes) .userStack owner

/-- The armed record is an exact projection of the live subject's installed
address-space view, rather than a free-standing collection of numbers. -/
def ReturnAuthorityBound (state : State) : Prop :=
  ∃ view plan, state.returnAddressSpace state.core.context.activeAddressSpace = some view ∧
    state.returnPlan = some plan ∧
    view.planBound state.core.context.activeAddressSpace plan = true ∧
    view.subject = state.core.context.currentSubject ∧
    state.core.lifecycle.current = some view.subject ∧
    state.core.lifecycle.capabilities.subjects view.subject = true ∧
    state.core.lifecycle.runnable view.subject = true ∧
    state.core.lifecycle.addressOwner state.core.context.activeAddressSpace = some view.subject ∧
    state.returnAuthority.expectedCr3 = view.expectedCr3 ∧
    state.returnAuthority.codeRegion = view.codeRegion ∧
    state.returnAuthority.stackRegion = view.stackRegion

/-- Lifecycle consistency, a bound armed return policy, and the kernel-owned
entry transaction invariant. -/
def WellFormed (state : State) : Prop :=
  Interrupt.WellFormed state.core ∧
    (state.returnAuthorityArmed = true → ReturnAuthorityBound state) ∧
    match state.mode with
    | .running => state.core.context.entryActive = false
    | .handling entry => entry.WellFormed ∧ state.core.context.entryActive = true
    | .halted _ => state.core.context.entryActive = true

inductive EntryAction where
  | contained (subject : Interrupt.SubjectId)
  | timer | syscall
  | rejected (reason : Interrupt.RejectReason)
  | fatal (reason : FatalReason)
  | alreadyHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure EntryOutcome where
  state : State
  action : EntryAction

def activeEntry (frame : Interrupt.HardwareFrame) : ActiveEntry :=
  { vector := frame.vector, origin := frame.savedPrivilege, frame }

/-- The only modeled escalation pair that becomes vector 8 is a page fault
while a page fault is already being handled.  Every other second entry is the
bounded forbidden-nesting case. -/
def escalation (active : ActiveEntry) (incoming : Interrupt.HardwareFrame) : FatalReason :=
  if active.vector = 14 && incoming.vector = 14 then .doubleFault else .nestedEntry

def halt (state : State) (reason : FatalReason) (active : Option ActiveEntry)
    (incoming : Interrupt.HardwareFrame) : EntryOutcome :=
  let record := HaltRecord.mk reason active incoming.vector incoming.savedPrivilege
  { state := { state with
      mode := .halted record
      returnAuthorityArmed := false
      copyOverride := false }
    action := .fatal reason }

/-- Begin entry without changing lifecycle, authority, scheduling, mailbox, or
resource state.  A second entry escalates immediately and atomically. -/
def beginEntry (state : State) (frame : Interrupt.HardwareFrame) : EntryOutcome :=
  match state.mode with
  | .halted record => { state, action := .alreadyHalted record }
  | .handling active => halt state (escalation active frame) (some active) frame
  | .running =>
      { state := { state with
          core := { state.core with context := { state.core.context with entryActive := true } }
          mode := .handling (activeEntry frame)
          returnAuthorityArmed := false
          copyOverride := false }
        action := .rejected .wrongOrigin }

def mapFatal : Interrupt.FatalReason → FatalReason
  | .kernelFault => .kernelFault
  | .unsupportedVector => .unsupportedVector
  | .nestedEntry => .nestedEntry

/-- Complete the active entry.  Fatal classification freezes the pre-entry
core; nonfatal completion is the only path back to `running`. -/
def finishEntry (state : State) : EntryOutcome :=
  match state.mode with
  | .running => { state, action := .rejected .wrongOrigin }
  | .halted record => { state, action := .alreadyHalted record }
  | .handling active =>
      let prepared : Interrupt.State := { state.core with context :=
        { state.core.context with entryActive := false } }
      let outcome := Interrupt.dispatchHardware prepared active.frame
      match outcome.action with
      | .fatal reason => halt { state with core := state.core } (mapFatal reason)
          (some active) active.frame
      | .contained subject =>
          { state := { state with core := outcome.state, mode := .running },
            action := .contained subject }
      | .timer =>
          { state := { state with core := outcome.state, mode := .running }, action := .timer }
      | .syscall =>
          { state := { state with core := outcome.state, mode := .running }, action := .syscall }
      | .rejected reason =>
          { state := { state with core := outcome.state, mode := .running },
            action := .rejected reason }

/-- One complete first entry, or one escalation attempt if entry is active. -/
def dispatchHardware (state : State) (frame : Interrupt.HardwareFrame) : EntryOutcome :=
  match state.mode with
  | .running => finishEntry (beginEntry state frame).state
  | .handling active => halt state (escalation active frame) (some active) frame
  | .halted record => { state, action := .alreadyHalted record }

def dispatch (state : State) (trap : Interrupt.Trap) : EntryOutcome :=
  dispatchHardware state trap.hardware

/-! ## Terminal outgoing user-return transaction -/

/-- Select the next return policy from the installed address-space view.  The
selection is armed only when scheduler identity, liveness, and ownership agree;
the proposed hardware frame is not an input to this transition. -/
def selectReturnAuthority (state : State) (purpose : Interrupt.ReturnPurpose) : State :=
  match state.returnPlan, state.returnAddressSpace state.core.context.activeAddressSpace with
  | some plan, some view =>
      if view.subject = state.core.context.currentSubject ∧
          state.core.lifecycle.current = some view.subject ∧
          state.core.lifecycle.capabilities.subjects view.subject = true ∧
          state.core.lifecycle.runnable view.subject = true ∧
          state.core.lifecycle.addressOwner state.core.context.activeAddressSpace =
            some view.subject ∧ view.planBound state.core.context.activeAddressSpace plan = true then
        { state with
          returnAuthority :=
            { purpose
              expectedCr3 := view.expectedCr3
              codeRegion := view.codeRegion
              stackRegion := view.stackRegion }
          returnAuthorityArmed := true }
      else { state with returnAuthorityArmed := false }
  | _, _ => { state with returnAuthorityArmed := false }

@[simp] theorem selectReturnAuthority_core state purpose :
    (selectReturnAuthority state purpose).core = state.core := by
  unfold selectReturnAuthority
  split
  · split <;> rfl
  · rfl

@[simp] theorem selectReturnAuthority_mode state purpose :
    (selectReturnAuthority state purpose).mode = state.mode := by
  unfold selectReturnAuthority
  split
  · split <;> rfl
  · rfl

@[simp] theorem selectReturnAuthority_returnPlan state purpose :
    (selectReturnAuthority state purpose).returnPlan = state.returnPlan := by
  unfold selectReturnAuthority
  split
  · split <;> rfl
  · rfl

@[simp] theorem selectReturnAuthority_returnAddressSpace state purpose :
    (selectReturnAuthority state purpose).returnAddressSpace = state.returnAddressSpace := by
  unfold selectReturnAuthority
  split
  · split <;> rfl
  · rfl

theorem selectReturnAuthority_wellFormed state purpose
    (hstate : WellFormed state) : WellFormed (selectReturnAuthority state purpose) := by
  rcases hstate with ⟨hcore, _hbound, hmode⟩
  unfold selectReturnAuthority
  split
  · rename_i plan view hplan hview
    by_cases hchecks : view.subject = state.core.context.currentSubject ∧
        state.core.lifecycle.current = some view.subject ∧
        state.core.lifecycle.capabilities.subjects view.subject = true ∧
        state.core.lifecycle.runnable view.subject = true ∧
        state.core.lifecycle.addressOwner state.core.context.activeAddressSpace = some view.subject ∧
        view.planBound state.core.context.activeAddressSpace plan = true
    · rw [if_pos hchecks]
      refine ⟨hcore, ?_, hmode⟩
      intro _
      exact ⟨view, plan, hview, hplan, hchecks.2.2.2.2.2, hchecks.1,
        hchecks.2.1, hchecks.2.2.1, hchecks.2.2.2.1,
        hchecks.2.2.2.2.1, rfl, rfl, rfl⟩
    · rw [if_neg hchecks]
      exact ⟨hcore, by simp, hmode⟩
  · exact ⟨hcore, by simp, hmode⟩

inductive UserReturnAction where
  | accepted (attested : Interrupt.UserReturnRequest)
  | fatal (record : HaltRecord)
  | alreadyHalted (record : HaltRecord)

structure UserReturnOutcome where
  state : State
  action : UserReturnAction

/-- Replace every caller-supplied policy field with execution-latch state. -/
def authoritativeReturnRequest (state : State) (request : Interrupt.UserReturnRequest) :
    Interrupt.UserReturnRequest :=
  { request with
      lifecycle := state.core.lifecycle
      expectedSubject := state.core.context.currentSubject
      expectedAddressSpace := state.core.context.activeAddressSpace
      expectedCr3 := state.returnAuthority.expectedCr3
      codeRegion := state.returnAuthority.codeRegion
      stackRegion := state.returnAuthority.stackRegion
      purpose := state.returnAuthority.purpose
      executionMode := .running }

private def latchInvalidUserReturn (state : State) (request : Interrupt.UserReturnRequest)
    (reason : Interrupt.ReturnRejectReason) (active : Option ActiveEntry) :
    UserReturnOutcome :=
  let record : HaltRecord :=
    { reason := .invalidUserReturn state.returnAuthority.purpose reason
      active
      incomingVector := request.hardware.vector
      incomingOrigin := request.hardware.savedPrivilege }
  { state := { state with
      core := { state.core with context := { state.core.context with entryActive := true } }
      mode := .halted record
      copyOverride := false }
    action := .fatal record }

/-- Latching a rejected outgoing return preserves the execution invariant:
the lifecycle and bound authority are unchanged, while the entry-active bit
is set exactly as required by terminal mode. -/
private theorem latchInvalidUserReturn_preserves_wellFormed state request reason active
    (hstate : WellFormed state) :
    WellFormed (latchInvalidUserReturn state request reason active).state := by
  rcases hstate with ⟨hcore, hbound, _⟩
  exact ⟨hcore, hbound, by simp [latchInvalidUserReturn]⟩

/-- Authoritative epilogue gate. Rejection records its purpose/reason and
latches the absorbing terminal mode before any modeled frame consumption. -/
def completeUserReturn (state : State) (request : Interrupt.UserReturnRequest) :
    UserReturnOutcome :=
  match state.mode with
  | .halted record => { state, action := .alreadyHalted record }
  | .handling active => latchInvalidUserReturn state request .fatalMode (some active)
  | .running =>
      if state.returnAuthorityArmed != true then
        latchInvalidUserReturn state request .unselectedAuthority none
      else
        let normalized := authoritativeReturnRequest state request
        match Interrupt.validateUserReturn normalized with
        | .accepted attested => { state, action := .accepted attested }
        | .rejected reason => latchInvalidUserReturn state normalized reason none

theorem accepted_user_return_is_atomic state request attested
    (hmode : state.mode = .running)
    (harmed : state.returnAuthorityArmed = true)
    (haccepted : Interrupt.validateUserReturn
      (authoritativeReturnRequest state request) = .accepted attested) :
    completeUserReturn state request = { state, action := .accepted attested } := by
  simp [completeUserReturn, hmode, harmed, haccepted]

theorem rejected_user_return_latches state request reason
    (hmode : state.mode = .running)
    (harmed : state.returnAuthorityArmed = true)
    (hrejected : Interrupt.validateUserReturn
      (authoritativeReturnRequest state request) = .rejected reason) :
    (completeUserReturn state request).state.mode =
      .halted
        { reason := .invalidUserReturn state.returnAuthority.purpose reason
          active := none
          incomingVector := request.hardware.vector
          incomingOrigin := request.hardware.savedPrivilege } ∧
      (completeUserReturn state request).state.core.lifecycle = state.core.lifecycle ∧
      (completeUserReturn state request).state.copyOverride = false := by
  simp only [completeUserReturn, hmode, harmed]
  rw [hrejected]
  simp [latchInvalidUserReturn, authoritativeReturnRequest]

theorem halted_user_return_absorbing state request record
    (hmode : state.mode = .halted record) :
    completeUserReturn state request = { state, action := .alreadyHalted record } := by
  simp [completeUserReturn, hmode]

/-- Acceptance is pinned to the kernel-owned policy record; changing policy
copies in the proposal cannot select another purpose, CR3, or memory region. -/
theorem accepted_user_return_uses_authority state request attested
    (hmode : state.mode = .running)
    (haccepted : (completeUserReturn state request).action = .accepted attested) :
    attested.purpose = state.returnAuthority.purpose ∧
      attested.expectedCr3 = state.returnAuthority.expectedCr3 ∧
      attested.codeRegion = state.returnAuthority.codeRegion ∧
      attested.stackRegion = state.returnAuthority.stackRegion := by
  simp only [completeUserReturn, hmode] at haccepted
  split at haccepted
  · simp [latchInvalidUserReturn] at haccepted
  generalize hnormalized : authoritativeReturnRequest state request = normalized at haccepted
  cases hvalidation : Interrupt.validateUserReturn normalized with
  | rejected reason => simp [hvalidation, latchInvalidUserReturn] at haccepted
  | accepted actual =>
      simp [hvalidation] at haccepted
      subst actual
      have hexact := Interrupt.accepted_attests_exact_request normalized attested hvalidation
      subst attested
      rw [← hnormalized]
      simp [authoritativeReturnRequest]

theorem accepted_user_return_has_bound_authority state request attested
    (hstate : WellFormed state)
    (haccepted : (completeUserReturn state request).action = .accepted attested) :
    ReturnAuthorityBound state := by
  rcases hstate with ⟨_, hbound, _⟩
  apply hbound
  cases hmode : state.mode with
  | running =>
      simp only [completeUserReturn, hmode] at haccepted
      split at haccepted
      · simp [latchInvalidUserReturn] at haccepted
      · simp_all
  | handling active => simp [completeUserReturn, hmode, latchInvalidUserReturn] at haccepted
  | halted record => simp [completeUserReturn, hmode] at haccepted

theorem accepted_user_return_requires_running state request attested
    (haccepted : (completeUserReturn state request).action = .accepted attested) :
    state.mode = .running := by
  cases hmode : state.mode with
  | running => rfl
  | handling active => simp [completeUserReturn, hmode, latchInvalidUserReturn] at haccepted
  | halted record => simp [completeUserReturn, hmode] at haccepted

/-- An accepted outgoing return only attests the kernel-normalized request; it
does not mutate any execution-latch field. -/
theorem accepted_user_return_state_unchanged state request attested
    (haccepted : (completeUserReturn state request).action = .accepted attested) :
    (completeUserReturn state request).state = state := by
  cases hmode : state.mode with
  | handling active => simp [completeUserReturn, hmode, latchInvalidUserReturn] at haccepted
  | halted record => simp [completeUserReturn, hmode] at haccepted
  | running =>
      simp only [completeUserReturn, hmode] at haccepted ⊢
      split at haccepted
      · simp [latchInvalidUserReturn] at haccepted
      · split at haccepted
        · simp_all [latchInvalidUserReturn]
        · simp_all [latchInvalidUserReturn]

/-- The state of the modeled subsystems whose transitions can run after entry.
Keeping these states under the execution latch makes bypassing it impossible in
the composite transition system. -/
structure CompositeState where
  execution : State
  scheduler : Scheduler.State
  preemption : Preemption.State
  virtualMemory : VirtualMapping.State
  ipc : IPCSyscall.State
  capabilities : Capability.State
  lifecycle : SubjectLifecycle.State
  /-- The exact authoritative context-bank model completed by issue #74. -/
  resumable : ResumablePreemption.State
  /-- The exact authoritative sealed-transfer model completed by issue #71. -/
  transfers : CapabilityTransfer.State

/-- A compiled return plan refines the active live virtual-memory view exactly
at the two leaves used by the return gate.  The live object bindings must name
the same physical frames as the compiled user-text/user-stack leaves. -/
def ReturnAddressSpace.liveBound (view : ReturnAddressSpace)
    (addressSpace : Interrupt.AddressSpaceId) (plan : BootPageTablePlan.Plan)
    (virtualMemory : VirtualMapping.State) : Bool :=
  let selected :=
    if view.subject = 1 && addressSpace = 1 then
      some (BootPageTablePlan.Space.subjectA, BootPageTablePlan.Owner.subjectA)
    else if view.subject = 2 && addressSpace = 2 then
      some (BootPageTablePlan.Space.subjectB, BootPageTablePlan.Owner.subjectB)
    else none
  match selected with
  | none => false
  | some (space, owner) =>
      let codePage := view.codeRegion.first.toNat / X86PageTable.pageBytes
      let stackPage := view.stackRegion.first.toNat / X86PageTable.pageBytes
      match virtualMemory.mappings addressSpace codePage,
          virtualMemory.mappings addressSpace stackPage with
      | some codeMapping, some stackMapping =>
          match virtualMemory.memory.binding codeMapping.object,
              virtualMemory.memory.binding stackMapping.object with
          | some codeFrame, some stackFrame =>
              virtualMemory.owner addressSpace = some view.subject &&
                virtualMemory.memory.capabilities.objects codeMapping.object &&
                virtualMemory.memory.capabilities.kinds codeMapping.object = some .memory &&
                virtualMemory.memory.allocator.status codeFrame =
                  .owned codeMapping.object &&
                virtualMemory.memory.capabilities.objects stackMapping.object &&
                virtualMemory.memory.capabilities.kinds stackMapping.object = some .memory &&
                virtualMemory.memory.allocator.status stackFrame =
                  .owned stackMapping.object &&
                codeMapping.permissions.read && !codeMapping.permissions.write &&
                stackMapping.permissions.read && stackMapping.permissions.write &&
                plan.hasPolicyLeafAtFrame space codePage codeFrame .userText owner &&
                plan.hasPolicyLeafAtFrame space stackPage stackFrame .userStack owner
          | _, _ => false
      | _, _ => false

/-- Cross-subsystem refinement checked whenever return authority is selected
or consumed.  A detached compiled plan cannot authorize an unmapped target. -/
def CompositeState.ReturnPlanLive (state : CompositeState) : Bool :=
  match state.execution.returnPlan,
      state.execution.returnAddressSpace state.execution.core.context.activeAddressSpace with
  | some plan, some view =>
      view.liveBound state.execution.core.context.activeAddressSpace plan state.virtualMemory
  | _, _ => false

/-- Select authority only from a compiled plan that agrees with the current
live virtual-memory mappings. -/
def selectLiveReturnAuthority (state : CompositeState)
    (purpose : Interrupt.ReturnPurpose) : CompositeState :=
  if state.ReturnPlanLive then
    { state with execution := selectReturnAuthority state.execution purpose }
  else
    { state with execution := { state.execution with returnAuthorityArmed := false } }

theorem selectLiveReturnAuthority_armed_implies_live state purpose
    (harmed : (selectLiveReturnAuthority state purpose).execution.returnAuthorityArmed = true) :
    state.ReturnPlanLive = true := by
  unfold selectLiveReturnAuthority at harmed
  split at harmed
  · assumption
  · simp at harmed

theorem selectLiveReturnAuthority_eq_execution_update state purpose :
    selectLiveReturnAuthority state purpose =
      { state with execution := (selectLiveReturnAuthority state purpose).execution } := by
  unfold selectLiveReturnAuthority
  split <;> rfl

@[simp] theorem selectLiveReturnAuthority_core state purpose :
    (selectLiveReturnAuthority state purpose).execution.core = state.execution.core := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_mode state purpose :
    (selectLiveReturnAuthority state purpose).execution.mode = state.execution.mode := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_execution_returnPlan state purpose :
    (selectLiveReturnAuthority state purpose).execution.returnPlan =
      state.execution.returnPlan := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_execution_returnAddressSpace state purpose :
    (selectLiveReturnAuthority state purpose).execution.returnAddressSpace =
      state.execution.returnAddressSpace := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_returnPlanLive state purpose :
    (selectLiveReturnAuthority state purpose).ReturnPlanLive = state.ReturnPlanLive := by
  rw [selectLiveReturnAuthority_eq_execution_update]
  simp [CompositeState.ReturnPlanLive]

theorem selectLiveReturnAuthority_execution_wellFormed state purpose
    (hstate : WellFormed state.execution) :
    WellFormed (selectLiveReturnAuthority state purpose).execution := by
  unfold selectLiveReturnAuthority
  split
  · exact selectReturnAuthority_wellFormed state.execution purpose hstate
  · rcases hstate with ⟨hcore, hbound, hmode⟩
    exact ⟨hcore, by simp, hmode⟩

/-- Every subsystem view is a projection of one authoritative lifecycle.  In
particular, scheduling and interrupt containment cannot disagree about whether
a subject is still live. -/
def CompositeState.Coherent (state : CompositeState) : Prop :=
  state.execution.core.lifecycle = state.lifecycle ∧
  state.scheduler.lifecycle = state.lifecycle ∧
  state.preemption.scheduler = state.scheduler ∧
  state.capabilities = state.lifecycle.capabilities ∧
  state.virtualMemory.memory.capabilities = state.lifecycle.capabilities ∧
  state.ipc.virtualMemory = state.virtualMemory ∧
  state.ipc.endpoints.capabilities = state.lifecycle.capabilities ∧
  state.resumable.scheduler = state.scheduler ∧
  state.resumable.translations.virtual = state.virtualMemory ∧
  state.transfers.toEndpointState = state.ipc.endpoints ∧
  (∀ subject, state.lifecycle.current = some subject →
    state.execution.core.context.currentSubject = subject ∧
    state.execution.core.context.activeAddressSpace = subject) ∧
  (∀ object, state.lifecycle.capabilities.objects object ≠ true →
    state.ipc.endpoints.mailbox object = none) ∧
  (∀ object envelope, state.ipc.endpoints.mailbox object = some envelope →
    state.lifecycle.capabilities.subjects envelope.sender = true)

/-- The global invariant advertised by the composite runtime boundary.  It
collects every invariant represented in `CompositeState`; cross-view equality
is explicit rather than inferred from repair after a transition. -/
def RuntimeWellFormed (state : CompositeState) : Prop :=
  state.Coherent ∧
  WellFormed state.execution ∧
  SubjectLifecycle.WellFormed state.lifecycle ∧
  Capability.WellFormed state.capabilities ∧
  VirtualMapping.LifecycleWellFormed state.virtualMemory ∧
  IPCSyscall.WellFormed state.ipc ∧
  Scheduler.WellFormed state.scheduler ∧
  Preemption.WellFormed state.preemption ∧
  ResumablePreemption.WellFormed state.resumable ∧
  CapabilityTransfer.WellFormed state.transfers ∧
  (state.resumable.halted = true ↔ ∃ record, state.execution.mode = .halted record) ∧
  (state.execution.returnAuthorityArmed = true → state.ReturnPlanLive = true)

private def restrictMappings (lifecycle : SubjectLifecycle.State)
    (mappings : VirtualMapping.AddressSpaceId → VirtualMapping.VirtualPage →
      Option VirtualMapping.Mapping) :=
  fun space page => match mappings space page with
    | some mapping =>
        if lifecycle.mapping space page = some mapping.object then some mapping else none
    | none => none

private def restrictMailboxes (lifecycle : SubjectLifecycle.State)
    (mailbox : EndpointIPC.ObjectId → Option EndpointIPC.Envelope) :=
  fun object => match mailbox object with
    | some envelope =>
        if lifecycle.capabilities.objects object = true ∧
            lifecycle.capabilities.subjects envelope.sender = true then some envelope else none
    | none => none

private def synchronizeMemory (lifecycle : SubjectLifecycle.State)
    (memory : MemoryLifecycle.State) : MemoryLifecycle.State :=
  { memory with
    capabilities := lifecycle.capabilities
    binding := fun object => (lifecycle.ownedMemory object).map (·.2)
    allocator := { memory.allocator with
      status := fun frame =>
        match memory.allocator.status frame with
        | .owned object =>
            match lifecycle.ownedMemory object with
            | some (_, ownedFrame) => if ownedFrame = frame then .owned object else .free
            | none => .free
        | status => status } }

/-- Atomically publish a lifecycle change to every overlapping subsystem
projection.  Rich subsystem-only data is retained only while the authoritative
lifecycle still names it. -/
private def installLifecycle (state : CompositeState)
    (lifecycle : SubjectLifecycle.State) : CompositeState :=
  let scheduler := { state.scheduler with lifecycle }
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  let virtualMemory := { state.virtualMemory with
    memory := synchronizeMemory lifecycle state.virtualMemory.memory
    owner := lifecycle.addressOwner
    mappings := restrictMappings lifecycle state.virtualMemory.mappings }
  let endpoints := { state.ipc.endpoints with
    capabilities := lifecycle.capabilities
    mailbox := restrictMailboxes lifecycle state.ipc.endpoints.mailbox }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with
      virtualMemory
      endpoints }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints } }

private def installCapabilities (state : CompositeState)
    (capabilities : Capability.State) : CompositeState :=
  installLifecycle state { state.lifecycle with capabilities }

/-- Publish subject creation without rebuilding unrelated resources.  Creation
only promotes the subject registry and issuance history, so memory bindings,
mappings, mailboxes, saved contexts, and cached translations remain exact. -/
private def installCreatedSubject (state : CompositeState)
    (subject : SubjectLifecycle.SubjectId) : CompositeState :=
  let lifecycle := (SubjectLifecycle.create state.lifecycle subject).state
  let scheduler := { state.scheduler with lifecycle }
  let preemption := { state.preemption with scheduler }
  let virtualMemory := { state.virtualMemory with
    memory := { state.virtualMemory.memory with capabilities := lifecycle.capabilities } }
  let endpoints := { state.ipc.endpoints with capabilities := lifecycle.capabilities }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints } }

@[simp] theorem createSubject_current lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.current = lifecycle.current := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

@[simp] theorem createSubject_objects lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.objects =
      lifecycle.capabilities.objects := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

theorem createSubject_preserves_live lifecycle subject candidate
    (hlive : lifecycle.capabilities.subjects candidate = true) :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.subjects candidate = true := by
  simp only [SubjectLifecycle.create]
  split <;> try assumption
  split <;> try assumption
  simp only [SubjectLifecycle.setBool]
  split <;> simp_all

theorem installCreatedSubject_coherent state subject
    (hstate : state.Coherent) :
    (installCreatedSubject state subject).Coherent := by
  rcases hstate with
    ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
      hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
      htransfers, hauthority, hdeadMailbox, hliveSender⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [installCreatedSubject] using hauthority
  · intro object hdead
    apply hdeadMailbox object
    simpa [installCreatedSubject] using hdead
  · intro object envelope hmailbox
    have hmailbox' : state.ipc.endpoints.mailbox object = some envelope := by
      simpa [installCreatedSubject] using hmailbox
    have hold := hliveSender object envelope hmailbox'
    exact createSubject_preserves_live state.lifecycle subject envelope.sender hold

/-- Capability publication has one authoritative result and updates every
consumer in the same composite step.  In particular, legacy scheduler and
preemption views cannot retain the pre-revocation registry while IPC or the
resumable-context path observes the new one. -/
theorem installCapabilities_synchronizes_consumers state capabilities :
    let next := installCapabilities state capabilities
    next.capabilities = capabilities ∧
      next.lifecycle.capabilities = capabilities ∧
      next.execution.core.lifecycle.capabilities = capabilities ∧
      next.virtualMemory.memory.capabilities = capabilities ∧
      next.ipc.endpoints.capabilities = capabilities ∧
      next.scheduler.lifecycle.capabilities = capabilities ∧
      next.preemption.scheduler.lifecycle.capabilities = capabilities ∧
      next.resumable.scheduler.lifecycle.capabilities = capabilities ∧
      next.transfers.capabilities = capabilities := by
  simp [installCapabilities, installLifecycle, synchronizeMemory]

private def installScheduler (state : CompositeState)
    (scheduler : Scheduler.State) : CompositeState :=
  installLifecycle { state with scheduler, preemption := { state.preemption with scheduler } }
    scheduler.lifecycle

/-- Installing an authoritative scheduler retains its queue and capacity
exactly; only the lifecycle shared with the other projections is republished. -/
@[simp] theorem installScheduler_scheduler state scheduler :
    (installScheduler state scheduler).scheduler = scheduler := by
  simp [installScheduler, installLifecycle]

/-- The legacy preemption projection observes the same scheduler that was
installed by the composite scheduler step. -/
@[simp] theorem installScheduler_preemption_scheduler state scheduler :
    (installScheduler state scheduler).preemption.scheduler = scheduler := by
  simp [installScheduler, installLifecycle]

/-- Scheduler installation publishes the scheduler's lifecycle as the unique
authoritative lifecycle projection. -/
@[simp] theorem installScheduler_lifecycle state scheduler :
    (installScheduler state scheduler).lifecycle = scheduler.lifecycle := by
  simp [installScheduler, installLifecycle]

/-- Scheduler publication is one synchronization step: execution,
preemption, and resumable-context consumers all observe the exact installed
scheduler lifecycle and queue state. -/
theorem installScheduler_synchronizes_consumers state scheduler :
    let next := installScheduler state scheduler
    next.execution.core.lifecycle = scheduler.lifecycle ∧
      next.scheduler = scheduler ∧
      next.preemption.scheduler = scheduler ∧
      next.resumable.scheduler = scheduler := by
  simp [installScheduler, installLifecycle]

/-- Publish the exact #74 context-bank state through every legacy projection.
The context list, TLB entries, and terminal latch are retained verbatim. -/
private def installResumable (state : CompositeState)
    (resumable : ResumablePreemption.State) : CompositeState :=
  installLifecycle
    { state with
      scheduler := resumable.scheduler
      preemption := { state.preemption with scheduler := resumable.scheduler }
      virtualMemory := resumable.translations.virtual
      resumable }
    resumable.scheduler.lifecycle

/-- Publish a resumable-aware scheduler removal without rebuilding unrelated
resource projections.  `ResumablePreemption.remove` changes only runnable/current
scheduler fields, the removed saved context, and the active translation. -/
private def installSchedulerRemoval (state : CompositeState)
    (resumable : ResumablePreemption.State) : CompositeState :=
  let lifecycle := resumable.scheduler.lifecycle
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler := resumable.scheduler
    preemption := { state.preemption with scheduler := resumable.scheduler }
    lifecycle
    resumable }

/-- Publish the exact #71 capability/mailbox state through every consumer of
the shared capability registry.  Pending sealed descendants and their trace
remain owned solely by `CapabilityTransfer.State`. -/
private def installTransfers (state : CompositeState)
    (transfers : CapabilityTransfer.State) : CompositeState :=
  installLifecycle
    { state with
      ipc := { state.ipc with endpoints := transfers.toEndpointState }
      transfers }
    { state.lifecycle with capabilities := transfers.capabilities }

/-- Publish a mapping-only transition without running the general lifecycle
synchronizer.  Map and unmap preserve the memory registry and address-space
owners, so rebuilding those projections would be both unnecessary and capable
of hiding an invalid pre-state. -/
private def installVirtualMemory (state : CompositeState)
    (virtualMemory : VirtualMapping.State) (translations : TLB.State) : CompositeState :=
  let lifecycle := { state.lifecycle with
    mapping := fun space page => (virtualMemory.mappings space page).map (·.object) }
  let scheduler := { state.scheduler with lifecycle }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory }
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { translations with virtual := virtualMemory } } }

theorem installLifecycle_coherent state lifecycle :
    (installLifecycle state lifecycle).Coherent := by
  simp [installLifecycle, CompositeState.Coherent, restrictMailboxes, synchronizeMemory]
  constructor
  · intro subject hcurrent
    simp [hcurrent]
  constructor
  · intro object hdead
    split <;> simp_all
  · intro object envelope hmailbox
    cases hsource : state.ipc.endpoints.mailbox object with
    | none => simp [hsource] at hmailbox
    | some actual =>
        simp [hsource] at hmailbox
        rw [← hmailbox.2]
        exact hmailbox.1.2

private theorem installVirtualMemory_preserves_runtimeWellFormed state virtualMemory translations
    (hstate : RuntimeWellFormed state)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory)
    (howner : virtualMemory.owner = state.virtualMemory.owner)
    (hvirtual : VirtualMapping.LifecycleWellFormed virtualMemory)
    (htlb : TLB.Coherent translations)
    (hactive : translations.active = state.resumable.translations.active) :
    RuntimeWellFormed (installVirtualMemory state virtualMemory translations) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, _hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent,
      hipcVirtualCoherent, hipcCapabilitiesCoherent,
      hresumableSchedulerCoherent, hresumableVirtualCoherent,
      htransfersCoherent, hauthorityCoherent, hdeadMailbox, hliveSender⟩
  have hcapabilitiesVirtual : virtualMemory.memory.capabilities = state.lifecycle.capabilities := by
    rw [hmemory, hvirtualCapabilitiesCoherent]
  have hownerLifecycle : virtualMemory.owner = state.lifecycle.addressOwner := by
    have hold := hresumable.2.2.2.2.2.2.1.1
    rw [hresumableVirtualCoherent, hresumableSchedulerCoherent,
      hschedulerCoherent] at hold
    rw [howner]
    exact hold
  rcases hexecution with ⟨_hcore, hbound, hmode⟩
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with
        mapping := fun space page => (virtualMemory.mappings space page).map (·.object) } := by
    simpa [SubjectLifecycle.WellFormed] using hlifecycle
  rcases hscheduler with ⟨_hschedulerLifecycle, hreadyNodup, hreadyCapacity,
    hreadyValid, hcurrentValid⟩
  simp only [Scheduler.ownsAddressSpace] at hreadyValid hcurrentValid
  rw [hschedulerCoherent] at hreadyValid hcurrentValid
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with
          mapping := fun space page => (virtualMemory.mappings space page).map (·.object) } } := by
    refine ⟨hlifecycle', hreadyNodup, hreadyCapacity, ?_, ?_⟩
    · simpa [Scheduler.ownsAddressSpace] using hreadyValid
    · simpa [Scheduler.ownsAddressSpace] using hcurrentValid
  refine ⟨?_, ?_, ?_, hcapabilities, hvirtual, ?_, ?_, ?_, ?_, htransfers, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, hcapabilitiesCoherent, ?_, rfl, ?_, rfl, rfl,
      htransfersCoherent, ?_, hdeadMailbox, hliveSender⟩
    · exact hcapabilitiesVirtual
    · exact hipcCapabilitiesCoherent
    · exact hauthorityCoherent
  · exact ⟨hlifecycle', by simp [installVirtualMemory], hmode⟩
  · exact hlifecycle'
  · exact ⟨hvirtual, hipc.2⟩
  · exact hscheduler'
  · rcases hpreemption with ⟨_, hticks⟩
    exact ⟨hscheduler', hticks⟩
  · rcases hresumable with
      ⟨_, hcapacity, hunique, hvalid, habsent, hagreement,
        htranslation, _hvirtualAgreement, hkinds, _htlb⟩
    simp only [ResumablePreemption.validContext] at hvalid
    simp only [ResumablePreemption.ReadyContextAgreement] at hagreement
    simp only [ResumablePreemption.TranslationAgreement] at htranslation
    rw [hresumableSchedulerCoherent, hschedulerCoherent] at hvalid habsent hagreement htranslation
    simp only [ResumablePreemption.ResourceKindAgreement] at hkinds
    rw [hresumableSchedulerCoherent, hschedulerCoherent] at hkinds
    refine ⟨?_, hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, htlb⟩
    · exact hscheduler'
    · simpa [installVirtualMemory, ResumablePreemption.validContext,
        hownerLifecycle] using hvalid
    · simpa [installVirtualMemory] using habsent
    · simpa [installVirtualMemory, ResumablePreemption.ReadyContextAgreement] using hagreement
    · refine ⟨hownerLifecycle, ?_⟩
      simpa [installVirtualMemory, hactive] using htranslation.2
    · exact ⟨hcapabilitiesVirtual, hvirtual⟩
    · simpa [installVirtualMemory, ResumablePreemption.ResourceKindAgreement] using hkinds
  · simpa [installVirtualMemory] using hhalted
  · simp [installVirtualMemory]

theorem installLifecycle_clears_retired_mailbox state lifecycle object
    (hdead : lifecycle.capabilities.objects object ≠ true) :
    (installLifecycle state lifecycle).ipc.endpoints.mailbox object = none := by
  simp [installLifecycle, restrictMailboxes]
  cases state.ipc.endpoints.mailbox object <;> simp [hdead]

theorem installLifecycle_clears_dead_sender state lifecycle object envelope
    (hdead : lifecycle.capabilities.subjects envelope.sender ≠ true) :
    (installLifecycle state lifecycle).ipc.endpoints.mailbox object ≠ some envelope := by
  simp [installLifecycle, restrictMailboxes]
  cases hmailbox : state.ipc.endpoints.mailbox object with
  | none => simp
  | some actual =>
      by_cases hlive : lifecycle.capabilities.objects object = true ∧
          lifecycle.capabilities.subjects actual.sender = true
      · simp [hlive]
        intro heq
        subst actual
        exact hdead hlive.2
      · simp [hlive]

theorem installLifecycle_releases_retired_memory state lifecycle object frame
    (_hbinding : state.virtualMemory.memory.binding object = some frame)
    (howned : state.virtualMemory.memory.allocator.status frame = .owned object)
    (hretired : lifecycle.ownedMemory object = none) :
    (installLifecycle state lifecycle).virtualMemory.memory.binding object = none ∧
      (installLifecycle state lifecycle).virtualMemory.memory.allocator.status frame = .free := by
  simp [installLifecycle, synchronizeMemory, howned, hretired]

/-- Typed inputs to the actual subsystem transitions.  This is deliberately not
a tag paired with a caller-supplied post-state. -/
inductive Operation where
  | interrupt (frame : Interrupt.HardwareFrame)
  | selectUserReturn (purpose : Interrupt.ReturnPurpose)
  | userReturn (request : Interrupt.UserReturnRequest)
  | syscall (call : Syscall.UntrustedCall)
  | preempt (frame : Interrupt.HardwareFrame)
  | ipc (call : IPCSyscall.Call)
  | resumePreempt (frame : Interrupt.HardwareFrame)
      (registers : ResumablePreemption.Registers)
  | transferOffer (endpointWord sourceWord : UInt64)
      (sourceKind : Capability.ObjectKind) (payload : EndpointIPC.Payload)
      (rights : Capability.Rights)
  | transferAccept (endpointWord : UInt64) (destinationSlot : Nat)
  | capabilityCopy (source destination destinationSlot : Nat)
      (rights : Capability.Rights)
  | capabilityRevoke (authoritySlot victim victimSlot : Nat)
  | capabilityRevokeSubtree (authoritySlot victim victimSlot : Nat)
  | map (slot page : Nat) (permissions : VirtualMapping.Permissions)
  | unmap (page : Nat)
  | createSubject (subject : Nat)
  | terminateSubject (subject : Nat)
  | scheduleAdd (subject : Nat)
  | scheduleRemove (subject : Nat)
  | scheduleNext | scheduleYield | scheduleTick | terminateCurrent | restart

inductive UserReturnReply where
  | accepted
  | fatal (record : HaltRecord)
  | alreadyHalted (record : HaltRecord)
  deriving DecidableEq, Repr

/-- Composite IPC observation.  A data-only receive must not consume a
mailbox that carries a sealed capability descendant; that mailbox is reserved
for `transferAccept`, which installs the descendant atomically. -/
inductive CompositeIPCReply where
  | syscall (reply : IPCSyscall.Reply)
  | sealedTransferPending
  deriving DecidableEq, Repr

inductive OperationReply where
  | interrupt (action : EntryAction)
  | returnSelection (armed : Bool)
  | userReturn (reply : UserReturnReply)
  | syscall (reply : Syscall.Reply)
  | preempt (action : EntryAction)
  | ipc (reply : CompositeIPCReply)
  | resume (restored : Option ResumablePreemption.Context)
      (error : Option ResumablePreemption.Error)
  | transferOffer (result : CapabilityTransfer.Result CapabilityTransfer.OfferError)
  | transferAccept (result : CapabilityTransfer.AcceptResult)
      (deliveredWord : Option UInt64)
  | capability (result : Capability.Result)
  | map (result : VirtualMapping.Result VirtualMapping.MapError)
  | unmap (result : VirtualMapping.Result VirtualMapping.UnmapError)
  | createSubject (result : SubjectLifecycle.Result SubjectLifecycle.CreateError)
  | terminateSubject (result : SubjectLifecycle.Result SubjectLifecycle.TerminateError)
  | scheduleRemove (result : ResumablePreemption.RemoveResult)
  | scheduler (result : Scheduler.Result)
  | restarted
  deriving DecidableEq, Repr

inductive GateResult where
  | completed (reply : OperationReply)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure GateOutcome where
  state : CompositeState
  result : GateResult

/-- The public operation vocabulary carries only untrusted scalar call data.
Privileged identity is projected from the authoritative execution latch. -/
def CompositeState.syscallContext (state : CompositeState) : Syscall.TrustedContext :=
  { caller := state.execution.core.context.currentSubject
    activeAddressSpace := state.execution.core.context.activeAddressSpace }

def CompositeState.ipcContext (state : CompositeState) : IPCSyscall.TrustedContext :=
  { caller := state.execution.core.context.currentSubject
    activeAddressSpace := state.execution.core.context.activeAddressSpace }

@[simp] theorem syscallContext_caller (state : CompositeState) :
    state.syscallContext.caller = state.execution.core.context.currentSubject := rfl

@[simp] theorem syscallContext_addressSpace (state : CompositeState) :
    state.syscallContext.activeAddressSpace =
      state.execution.core.context.activeAddressSpace := rfl

@[simp] theorem ipcContext_caller (state : CompositeState) :
    state.ipcContext.caller = state.execution.core.context.currentSubject := rfl

@[simp] theorem ipcContext_addressSpace (state : CompositeState) :
    state.ipcContext.activeAddressSpace =
      state.execution.core.context.activeAddressSpace := rfl

private structure CompositeIPCOutcome where
  state : CompositeState
  reply : CompositeIPCReply

private def installIPC (state : CompositeState) (ipc : IPCSyscall.State) : CompositeState :=
  { state with
    ipc
    transfers := { state.transfers with toEndpointState := ipc.endpoints } }

/-- Invoke data-only IPC through the sealed-transfer authority boundary.  A
receive aimed at a tagged mailbox is rejected before the embedded endpoint
transition can consume either the envelope or its attachment metadata. -/
private def dispatchIPC (state : CompositeState) (call : IPCSyscall.Call) :
    CompositeIPCOutcome :=
  match call with
  | .send handleWord word0 word1 =>
      let outcome := IPCSyscall.dispatch state.ipc state.ipcContext
        (.send handleWord word0 word1)
      { state := installIPC state outcome.state, reply := .syscall outcome.reply }
  | .receive handleWord =>
      match CapabilityHandle.resolveCurrent state.transfers.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint with
      | .ok endpoint =>
          match state.transfers.pending endpoint.capability.object with
          | some _ => { state, reply := .sealedTransferPending }
          | none =>
              let outcome := IPCSyscall.dispatch state.ipc state.ipcContext
                (.receive handleWord)
              { state := installIPC state outcome.state, reply := .syscall outcome.reply }
      | .error _ =>
          let outcome := IPCSyscall.dispatch state.ipc state.ipcContext
            (.receive handleWord)
          { state := installIPC state outcome.state, reply := .syscall outcome.reply }

/-- Exact composite post-state selected by one typed operation.  This is public
so refinement layers can state that their adapter agrees with the gate. -/
def applyOperation (state : CompositeState) : Operation → CompositeState
  | .interrupt frame =>
      let entry := dispatchHardware state.execution frame
      installLifecycle { state with execution := entry.state }
        entry.state.core.lifecycle
  | .selectUserReturn purpose =>
      selectLiveReturnAuthority state purpose
  | .userReturn request =>
      let execution :=
        if state.ReturnPlanLive then state.execution
        else { state.execution with returnAuthorityArmed := false }
      let outcome := completeUserReturn execution request
      match outcome.action with
      | .fatal _ =>
          { state with
            execution := outcome.state
            resumable := { state.resumable with halted := true } }
      | .accepted _ | .alreadyHalted _ => { state with execution := outcome.state }
  | .syscall call =>
      let outcome := Syscall.dispatch state.virtualMemory state.syscallContext call
      match outcome.reply with
      | .rejected _ => state
      | .accepted =>
          match Syscall.decode call with
          | .ok (.access _ _) =>
              -- Translation checks do not mutate virtual memory; do not run a
              -- synchronization helper that could mask an invalid pre-state.
              selectLiveReturnAuthority state .syscallResume
          | .ok (.unmap page) =>
              let translations := TLB.invalidatePage
                { state.resumable.translations with virtual := outcome.state }
                state.execution.core.context.activeAddressSpace page
              let installed := installVirtualMemory state outcome.state translations
              selectLiveReturnAuthority installed .syscallResume
          | _ =>
              let translations := { state.resumable.translations with virtual := outcome.state }
              let installed := installVirtualMemory state outcome.state translations
              selectLiveReturnAuthority installed .syscallResume
  | .preempt frame =>
      let entry := dispatchHardware state.execution frame
      let entered := installLifecycle { state with execution := entry.state }
        entry.state.core.lifecycle
      match entry.action with
      | .timer =>
          let preemption :=
            (Preemption.oneShotTick entered.preemption entered.execution.core frame).state
          let scheduled := installScheduler { entered with preemption } preemption.scheduler
          selectLiveReturnAuthority scheduled .schedulerRestore
      | _ => entered
  | .ipc call =>
      let outcome := dispatchIPC state call
      match outcome.reply with
      | .sealedTransferPending => state
      | .syscall (.sendHandleRejected _) => state
      | .syscall (.sendRejected _) => state
      | .syscall (.receiveHandleRejected _) => state
      | .syscall (.receiveRejected _) => state
      | .syscall .sent => outcome.state
      | .syscall (.delivered _ _ _) => outcome.state
  | .resumePreempt frame registers =>
      let outcome := ResumablePreemption.switch state.resumable state.execution.core
        frame registers
      if outcome.state.halted then
        let entry := dispatchHardware state.execution frame
        installResumable { state with execution := entry.state } outcome.state
      else
        installResumable state outcome.state
  | .transferOffer endpointWord sourceWord sourceKind payload rights =>
      let outcome := CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights
      match outcome.result with
      | .rejected _ => state
      | .accepted => installTransfers state outcome.state
  | .transferAccept endpointWord destinationSlot =>
      let outcome := CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot
      match outcome.result with
      | .rejected _ => state
      | .delivered _ => installTransfers state outcome.state
  | .capabilityCopy source destination destinationSlot rights =>
      let outcome := Capability.copy state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCapabilities state outcome.state
  | .capabilityRevoke authoritySlot victim victimSlot =>
      let outcome := Capability.revoke state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCapabilities state outcome.state
  | .capabilityRevokeSubtree authoritySlot victim victimSlot =>
      let outcome := Capability.revokeSubtree state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCapabilities state outcome.state
  | .map slot page permissions =>
      let outcome := VirtualMapping.map state.virtualMemory
        state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          installVirtualMemory state outcome.state
            { state.resumable.translations with virtual := outcome.state }
  | .unmap page =>
      let outcome := VirtualMapping.unmap state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page
      match outcome.result with
      | .rejected _ => state
      | .accepted =>
          let translations := TLB.invalidatePage
            { state.resumable.translations with virtual := outcome.state }
            state.execution.core.context.activeAddressSpace page
          installVirtualMemory state outcome.state translations
  | .createSubject subject =>
      let outcome := SubjectLifecycle.create state.lifecycle subject
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCreatedSubject state subject
  | .terminateSubject subject =>
      let outcome := SubjectLifecycle.terminate state.lifecycle subject
      match outcome.result with
      | .rejected _ => state
      | .accepted => installLifecycle state outcome.state
  | .scheduleAdd subject =>
      let outcome := Scheduler.add state.scheduler subject
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .scheduleRemove subject =>
      let outcome := ResumablePreemption.remove state.resumable subject
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installSchedulerRemoval state outcome.state
  | .scheduleNext =>
      let outcome := Scheduler.selectNext state.scheduler
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .scheduleYield =>
      let outcome := Scheduler.yield state.scheduler
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .scheduleTick =>
      let outcome := Scheduler.tick state.scheduler
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .terminateCurrent =>
      let outcome := Scheduler.terminateCurrent state.scheduler
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .restart => state

/-- Exact typed observation of the subsystem transition selected by an
operation.  Unlike the former generic `accepted`, this cannot erase an
operation-specific rejection. -/
def operationReply (state : CompositeState) : Operation → OperationReply
  | .interrupt frame => .interrupt (dispatchHardware state.execution frame).action
  | .selectUserReturn purpose =>
      .returnSelection (selectLiveReturnAuthority state purpose).execution.returnAuthorityArmed
  | .userReturn request =>
      let execution :=
        if state.ReturnPlanLive then state.execution
        else { state.execution with returnAuthorityArmed := false }
      match (completeUserReturn execution request).action with
      | .accepted _ => .userReturn .accepted
      | .fatal record => .userReturn (.fatal record)
      | .alreadyHalted record => .userReturn (.alreadyHalted record)
  | .syscall call => .syscall (Syscall.dispatch state.virtualMemory state.syscallContext call).reply
  | .preempt frame => .preempt (dispatchHardware state.execution frame).action
  | .ipc call => .ipc (dispatchIPC state call).reply
  | .resumePreempt frame registers =>
      let outcome := ResumablePreemption.switch state.resumable state.execution.core
        frame registers
      .resume outcome.restored outcome.error
  | .transferOffer endpointWord sourceWord sourceKind payload rights =>
      .transferOffer
        (CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
          payload rights).result
  | .transferAccept endpointWord destinationSlot =>
      let outcome := CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot
      .transferAccept outcome.result outcome.deliveredWord
  | .capabilityCopy source destination destinationSlot rights =>
      .capability
        (Capability.copy state.capabilities state.execution.core.context.currentSubject
          source destination destinationSlot rights).result
  | .capabilityRevoke authoritySlot victim victimSlot =>
      .capability
        (Capability.revoke state.capabilities state.execution.core.context.currentSubject
          authoritySlot victim victimSlot).result
  | .capabilityRevokeSubtree authoritySlot victim victimSlot =>
      .capability
        (Capability.revokeSubtree state.capabilities state.execution.core.context.currentSubject
          authoritySlot victim victimSlot).result
  | .map slot page permissions =>
      .map (VirtualMapping.map state.virtualMemory state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions).result
  | .unmap page =>
      .unmap (VirtualMapping.unmap state.virtualMemory state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page).result
  | .createSubject subject => .createSubject (SubjectLifecycle.create state.lifecycle subject).result
  | .terminateSubject subject =>
      .terminateSubject (SubjectLifecycle.terminate state.lifecycle subject).result
  | .scheduleAdd subject => .scheduler (Scheduler.add state.scheduler subject).result
  | .scheduleRemove subject =>
      .scheduleRemove (ResumablePreemption.remove state.resumable subject).result
  | .scheduleNext => .scheduler (Scheduler.selectNext state.scheduler).result
  | .scheduleYield => .scheduler (Scheduler.yield state.scheduler).result
  | .scheduleTick => .scheduler (Scheduler.tick state.scheduler).result
  | .terminateCurrent => .scheduler (Scheduler.terminateCurrent state.scheduler).result
  | .restart => .restarted

/-- Evidence that one operation produced one of the finite, ordinary typed
subsystem rejections.  Fatal entry/return results and busy/terminal gate
rejections are deliberately separate. -/
inductive SubsystemRejection (state : CompositeState) : Operation → OperationReply → Prop
  | syscall call reason
      (h : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply = .rejected reason) :
      SubsystemRejection state (.syscall call) (.syscall (.rejected reason))
  | ipcSendHandle call reason
      (h : (dispatchIPC state call).reply = .syscall (.sendHandleRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.sendHandleRejected reason)))
  | ipcSend call reason
      (h : (dispatchIPC state call).reply = .syscall (.sendRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.sendRejected reason)))
  | ipcReceiveHandle call reason
      (h : (dispatchIPC state call).reply = .syscall (.receiveHandleRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.receiveHandleRejected reason)))
  | ipcReceive call reason
      (h : (dispatchIPC state call).reply = .syscall (.receiveRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.receiveRejected reason)))
  | ipcSealed call (h : (dispatchIPC state call).reply = .sealedTransferPending) :
      SubsystemRejection state (.ipc call) (.ipc .sealedTransferPending)
  | transferOffer endpointWord sourceWord sourceKind payload rights reason
      (h : (CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights).result =
          .rejected reason) :
      SubsystemRejection state (.transferOffer endpointWord sourceWord sourceKind payload rights)
        (.transferOffer (.rejected reason))
  | transferAccept endpointWord destinationSlot reason deliveredWord
      (hresult : (CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot).result = .rejected reason)
      (hword : (CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot).deliveredWord = deliveredWord) :
      SubsystemRejection state (.transferAccept endpointWord destinationSlot)
        (.transferAccept (.rejected reason) deliveredWord)
  | capabilityCopy source destination destinationSlot rights reason
      (h : (Capability.copy state.capabilities state.execution.core.context.currentSubject
        source destination destinationSlot rights).result = .rejected reason) :
      SubsystemRejection state (.capabilityCopy source destination destinationSlot rights)
        (.capability (.rejected reason))
  | capabilityRevoke authoritySlot victim victimSlot reason
      (h : (Capability.revoke state.capabilities state.execution.core.context.currentSubject
        authoritySlot victim victimSlot).result = .rejected reason) :
      SubsystemRejection state (.capabilityRevoke authoritySlot victim victimSlot)
        (.capability (.rejected reason))
  | capabilityRevokeSubtree authoritySlot victim victimSlot reason
      (h : (Capability.revokeSubtree state.capabilities state.execution.core.context.currentSubject
        authoritySlot victim victimSlot).result = .rejected reason) :
      SubsystemRejection state (.capabilityRevokeSubtree authoritySlot victim victimSlot)
        (.capability (.rejected reason))
  | map slot page permissions reason
      (h : (VirtualMapping.map state.virtualMemory state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions).result = .rejected reason) :
      SubsystemRejection state (.map slot page permissions) (.map (.rejected reason))
  | unmap page reason
      (h : (VirtualMapping.unmap state.virtualMemory state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page).result = .rejected reason) :
      SubsystemRejection state (.unmap page) (.unmap (.rejected reason))
  | createSubject subject reason
      (h : (SubjectLifecycle.create state.lifecycle subject).result = .rejected reason) :
      SubsystemRejection state (.createSubject subject) (.createSubject (.rejected reason))
  | terminateSubject subject reason
      (h : (SubjectLifecycle.terminate state.lifecycle subject).result = .rejected reason) :
      SubsystemRejection state (.terminateSubject subject) (.terminateSubject (.rejected reason))
  | scheduleAdd subject reason (h : (Scheduler.add state.scheduler subject).result = .rejected reason) :
      SubsystemRejection state (.scheduleAdd subject) (.scheduler (.rejected reason))
  | scheduleRemove subject reason
      (h : (ResumablePreemption.remove state.resumable subject).result = .rejected reason) :
      SubsystemRejection state (.scheduleRemove subject) (.scheduleRemove (.rejected reason))
  | scheduleNext reason (h : (Scheduler.selectNext state.scheduler).result = .rejected reason) :
      SubsystemRejection state .scheduleNext (.scheduler (.rejected reason))
  | scheduleYield reason (h : (Scheduler.yield state.scheduler).result = .rejected reason) :
      SubsystemRejection state .scheduleYield (.scheduler (.rejected reason))
  | scheduleTick reason (h : (Scheduler.tick state.scheduler).result = .rejected reason) :
      SubsystemRejection state .scheduleTick (.scheduler (.rejected reason))
  | terminateCurrent reason (h : (Scheduler.terminateCurrent state.scheduler).result = .rejected reason) :
      SubsystemRejection state .terminateCurrent (.scheduler (.rejected reason))

/-- A contained user fault is published to both scheduler views in the same
composite step, so neither can select from the pre-termination lifecycle. -/
theorem interrupt_synchronizes_lifecycle state frame :
    let next := applyOperation state (.interrupt frame)
    next.scheduler.lifecycle = next.execution.core.lifecycle ∧
      next.preemption.scheduler.lifecycle = next.execution.core.lifecycle := by
  simp only [applyOperation]
  generalize hentry : dispatchHardware state.execution frame = entry
  cases entry.action <;> simp [installLifecycle]

/-- Preemption cannot reinterpret a fatal hardware frame as an accepted
scheduler no-op: the authoritative entry path latches the same terminal mode. -/
theorem preempt_fatal_latches state frame reason
    (hfatal : (dispatchHardware state.execution frame).action = .fatal reason) :
    (applyOperation state (.preempt frame)).execution.mode =
      (dispatchHardware state.execution frame).state.mode := by
  simp [applyOperation, hfatal, installLifecycle]

/-- A data-only receive cannot consume the envelope paired with a sealed
descendant.  The composite reply identifies the required transfer operation,
and every authoritative projection remains byte-for-byte unchanged. -/
theorem ipc_receive_preserves_sealed_transfer state handleWord endpoint transfer
    (hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok endpoint)
    (hpending : state.transfers.pending endpoint.capability.object = some transfer) :
    dispatchIPC state (.receive handleWord) =
      { state, reply := .sealedTransferPending } := by
  simp [dispatchIPC, hresolve, hpending]

/-- Fatal resumable entry latches both the exact #74 state and the composite
execution mode in one transition.  It can therefore no longer leave the
runtime apparently running with a terminal context bank. -/
theorem resumePreempt_halted_latches state frame registers
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    let next := applyOperation state (.resumePreempt frame registers)
    next.resumable.halted = true ∧
      next.execution.mode = (dispatchHardware state.execution frame).state.mode := by
  simp [applyOperation, hhalted, installResumable, installLifecycle]

/-- The sole composite step computes the post-state by invoking the typed
subsystem transition internally. -/
def gate (state : CompositeState) (operation : Operation) : GateOutcome :=
  match state.execution.mode with
  | .running =>
      { state := applyOperation state operation, result := .completed (operationReply state operation) }
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }

/-- A running gate exposes the exact typed subsystem observation paired with
the exact composite post-state computed from the same pre-state and operation.
This is the generic soundness law used by operation-specific acceptance proofs;
`completed` does not erase a typed rejection carried by `OperationReply`. -/
theorem gate_running_exact state operation
    (hmode : state.execution.mode = .running) :
    gate state operation =
      { state := applyOperation state operation
        result := .completed (operationReply state operation) } := by
  simp [gate, hmode]

/-- Both public gate rejection classes are atomic for every operation.  Busy
and halted results retain the identical composite state, including the exact
#71 transfer trace and #74 context bank. -/
theorem gate_mode_rejection_atomicity state operation
    (hrejected : (gate state operation).result = .rejectedBusy ∨
      ∃ record, (gate state operation).result = .rejectedHalted record) :
    (gate state operation).state = state := by
  cases hmode : state.execution.mode with
  | running => simp [gate, hmode] at hrejected
  | handling active => simp [gate, hmode]
  | halted record => simp [gate, hmode]

/-- Any completed result proves that the latch was running and identifies both
the exact typed reply and exact post-state.  Thus a subsystem rejection cannot
be mistaken for a different operation's success, and no caller-selected state
can be paired with an authoritative reply. -/
theorem gate_completed_sound state operation reply
    (hcompleted : (gate state operation).result = .completed reply) :
    state.execution.mode = .running ∧
      reply = operationReply state operation ∧
      (gate state operation).state = applyOperation state operation := by
  cases hmode : state.execution.mode with
  | running => simp [gate, hmode] at hcompleted ⊢; simp [gate, hmode, hcompleted]
  | handling active => simp [gate, hmode] at hcompleted
  | halted record => simp [gate, hmode] at hcompleted

/-- Every typed nonfatal subsystem rejection is globally atomic.  The theorem
is intentionally quantified over the finite composite reply classification:
adding a new rejection constructor does not gain this claim until its
`applyOperation` branch explicitly returns the identical pre-state. -/
theorem gate_subsystem_rejection_atomicity state operation reply
    (hresult : (gate state operation).result = .completed reply)
    (hrejected : SubsystemRejection state operation reply) :
    (gate state operation).state = state := by
  have hmode := (gate_completed_sound state operation reply hresult).1
  cases hrejected <;> simp_all [gate, applyOperation]

/-- Every finite nonfatal subsystem rejection preserves the complete runtime
invariant because the composite gate publishes the literal pre-state.  This
lifts rejection atomicity to the global preservation boundary uniformly over
syscall, IPC, transfer, capability, mapping, lifecycle, and scheduler errors. -/
theorem gate_subsystem_rejection_preserves_runtimeWellFormed state operation reply
    (hstate : RuntimeWellFormed state)
    (hresult : (gate state operation).result = .completed reply)
    (hrejected : SubsystemRejection state operation reply) :
    RuntimeWellFormed (gate state operation).state ∧
      (gate state operation).state = state := by
  have hatomic := gate_subsystem_rejection_atomicity state operation reply
    hresult hrejected
  exact ⟨by simpa [hatomic] using hstate, hatomic⟩

/-- Return-authority selection is a complete operation-family preservation
slice.  In running mode it changes only the execution projection and arms
authority only after the live-plan check; busy and halted modes retain the
exact authoritative #71/#74 states without invoking the selector. -/
theorem gate_selectUserReturn_preserves_runtimeWellFormed state purpose
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state (.selectUserReturn purpose)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      rcases hstate with
        ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
          hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
      have hselected := selectLiveReturnAuthority_execution_wellFormed state purpose hexecution
      have harmed := selectLiveReturnAuthority_armed_implies_live state purpose
      simp only [gate, hmode, applyOperation]
      rw [selectLiveReturnAuthority_eq_execution_update]
      refine ⟨?_, hselected, hlifecycle, hcapabilities, hvirtual, hipc,
        hscheduler, hpreemption, hresumable, htransfers, ?_, ?_⟩
      · simpa [CompositeState.Coherent] using hcoherent
      · simpa using hhalted
      · intro harmedSelected
        have hliveSelected := harmed (by simpa using harmedSelected)
        simpa [CompositeState.ReturnPlanLive] using hliveSelected

/-- An accepted outgoing user return is a complete accepted-operation slice:
the runtime invariant forces its armed authority to refer to the live mapping
plan, and successful attestation leaves the entire composite state unchanged. -/
theorem gate_userReturn_accepted_preserves_runtimeWellFormed state request attested
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (completeUserReturn state.execution request).action = .accepted attested) :
    RuntimeWellFormed (gate state (.userReturn request)).state ∧
      (gate state (.userReturn request)).state = state ∧
      (gate state (.userReturn request)).result = .completed (.userReturn .accepted) := by
  have harmed : state.execution.returnAuthorityArmed = true := by
    cases hvalue : state.execution.returnAuthorityArmed with
    | false => simp [completeUserReturn, hmode, hvalue, latchInvalidUserReturn] at haccepted
    | true => rfl
  have hplan : state.ReturnPlanLive = true := hstate.2.2.2.2.2.2.2.2.2.2.2 harmed
  have hunchanged := accepted_user_return_state_unchanged state.execution request attested haccepted
  have hoperation : applyOperation state (.userReturn request) = state := by
    simp [applyOperation, hplan, hunchanged, haccepted]
  refine ⟨?_, ?_, ?_⟩
  · simpa [gate, hmode, hoperation] using hstate
  · simp [gate, hmode, hoperation]
  · simp [gate, hmode, operationReply, hplan, haccepted]

/-- The complete outgoing-return operation preserves the global invariant.
Successful attestation is atomic; every malformed or unselected proposal
publishes the terminal execution latch together with the resumable latch, so
the two fail-stop projections cannot disagree after rejection. -/
theorem gate_userReturn_preserves_runtimeWellFormed state request
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state (.userReturn request)).state := by
  by_cases hmode : state.execution.mode = .running
  · by_cases hlive : state.ReturnPlanLive = true
    · cases harmed : state.execution.returnAuthorityArmed with
      | false =>
          rcases hstate with
            ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
              hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority⟩
          have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
          have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
            state.execution request .unselectedAuthority none hexecution
          have hresumableHalted : ResumablePreemption.WellFormed
              { state.resumable with halted := true } :=
            (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
          simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
            RuntimeWellFormed, CompositeState.Coherent,
            ResumablePreemption.wellFormed_set_halted]
          exact hliveMailbox
      | true =>
          cases hvalidation : Interrupt.validateUserReturn
              (authoritativeReturnRequest state.execution request) with
          | accepted attested =>
              have haccepted : (completeUserReturn state.execution request).action =
                  .accepted attested := by
                simp [completeUserReturn, hmode, harmed, hvalidation]
              exact (gate_userReturn_accepted_preserves_runtimeWellFormed state request
                attested hstate hmode haccepted).1
          | rejected reason =>
              rcases hstate with
                ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
                  hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority⟩
              have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
              have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
                state.execution (authoritativeReturnRequest state.execution request)
                reason none hexecution
              have hresumableHalted : ResumablePreemption.WellFormed
                  { state.resumable with halted := true } :=
                (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
              have hliveFatal :
                  ({ state with
                    execution := (latchInvalidUserReturn state.execution
                      (authoritativeReturnRequest state.execution request) reason none).state
                    resumable := { state.resumable with halted := true } }).ReturnPlanLive = true := by
                simpa [CompositeState.ReturnPlanLive, latchInvalidUserReturn] using hlive
              simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
                RuntimeWellFormed, CompositeState.Coherent,
                ResumablePreemption.wellFormed_set_halted]
              exact hliveMailbox
    · rcases hstate with
        ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
          hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority⟩
      have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
      rcases hexecution with ⟨hcore, _hbound, hexecutionMode⟩
      have hexecutionPrepared : WellFormed
          { state.execution with returnAuthorityArmed := false } :=
        ⟨hcore, by simp, hexecutionMode⟩
      have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
        { state.execution with returnAuthorityArmed := false }
        request .unselectedAuthority none hexecutionPrepared
      have hresumableHalted : ResumablePreemption.WellFormed
          { state.resumable with halted := true } :=
        (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
      simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
        RuntimeWellFormed, CompositeState.Coherent,
        ResumablePreemption.wellFormed_set_halted]
      exact hliveMailbox
  · cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => simpa [gate, hactual] using hstate
    | halted record => simpa [gate, hactual] using hstate

/-- Restart is the identity running operation and therefore preserves the full
runtime invariant without touching any authoritative subsystem state. -/
theorem gate_restart_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state .restart).state := by
  cases hmode : state.execution.mode with
  | running => simpa [gate, hmode, applyOperation] using hstate
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate

/-- An accepted access-only syscall leaves virtual memory unchanged and only
reselects return authority through the live-plan boundary.  Consequently the
complete runtime invariant, not merely virtual-memory well-formedness, survives
the accepted public operation and its reply is the exact typed success. -/
theorem gate_syscall_access_accepted_preserves_runtimeWellFormed state call page access
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdecode : Syscall.decode call = .ok (.access page access))
    (haccepted : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply =
      .accepted) :
    RuntimeWellFormed (gate state (.syscall call)).state ∧
      (gate state (.syscall call)).result = .completed (.syscall .accepted) := by
  have hselected := gate_selectUserReturn_preserves_runtimeWellFormed
    state .syscallResume hstate
  have hselected' :
      RuntimeWellFormed (selectLiveReturnAuthority state .syscallResume) := by
    simpa [gate, hmode, applyOperation] using hselected
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, hdecode] using hselected'
  · simp [gate, hmode, operationReply, haccepted]

/-- The guarded sealed-mailbox rejection is a genuine composite gate
preservation step: it retains the full global runtime invariant, rather than
repairing one projection after consuming the envelope. -/
theorem gate_sealed_receive_preserves_runtimeWellFormed state handleWord endpoint transfer
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok endpoint)
    (hpending : state.transfers.pending endpoint.capability.object = some transfer) :
    RuntimeWellFormed (gate state (.ipc (.receive handleWord))).state ∧
      (gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc .sealedTransferPending) := by
  have hguard := ipc_receive_preserves_sealed_transfer state handleWord endpoint transfer
    hresolve hpending
  simp [gate, hmode, applyOperation, operationReply, hguard, hstate]

private theorem endpointSend_capabilities_unchanged state caller slot payload :
    (EndpointIPC.send state caller slot payload).state.capabilities = state.capabilities := by
  simp only [EndpointIPC.send]
  split <;> try rfl
  next cap => split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> rfl

private theorem endpointSend_preserves_occupied_mailbox state caller slot payload
    endpoint envelope (hmail : state.mailbox endpoint = some envelope) :
    (EndpointIPC.send state caller slot payload).state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.send]
  split <;> try simpa [EndpointIPC.reject] using hmail
  next cap hlookup =>
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    next hfree =>
      have hne : endpoint ≠ cap.object := by
        intro heq
        subst endpoint
        simp [hmail] at hfree
      simpa [EndpointIPC.setOption, hne] using hmail

private theorem endpointSend_preserves_live_senders state caller slot payload
    (hwellFormed : Capability.WellFormed state.capabilities)
    (hlive : ∀ object envelope, state.mailbox object = some envelope →
      state.capabilities.subjects envelope.sender = true) :
    ∀ object envelope,
      (EndpointIPC.send state caller slot payload).state.mailbox object = some envelope →
        (EndpointIPC.send state caller slot payload).state.capabilities.subjects
          envelope.sender = true := by
  simp only [EndpointIPC.send]
  split <;> try simpa [EndpointIPC.reject] using hlive
  next cap hlookup =>
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    next hfree =>
      intro object envelope hmail
      by_cases heq : object = cap.object
      · subst object
        have henvelope : envelope = { endpoint := cap.object, sender := caller, payload } := by
          simpa [EndpointIPC.setOption] using hmail.symm
        subst envelope
        exact (hwellFormed.1 caller slot cap
          (Capability.lookup_found_slot state.capabilities caller slot cap hlookup)).1
      · exact hlive object envelope (by simpa [EndpointIPC.setOption, heq] using hmail)

private theorem endpointReceive_capabilities_unchanged state caller slot :
    (EndpointIPC.receive state caller slot).state.capabilities = state.capabilities := by
  simp only [EndpointIPC.receive]
  split <;> try rfl
  next cap => split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> rfl

private theorem endpointReceive_preserves_other_mailbox state caller slot selected
    endpoint envelope
    (hlookup : Capability.lookup state.capabilities caller slot = .found selected)
    (hne : endpoint ≠ selected.object)
    (hmail : state.mailbox endpoint = some envelope) :
    (EndpointIPC.receive state caller slot).state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.receive, hlookup]
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  next queued hqueued => simpa [EndpointIPC.setOption, hne] using hmail

private theorem endpointReceive_mailbox_provenance state caller slot endpoint envelope
    (hmail : (EndpointIPC.receive state caller slot).state.mailbox endpoint = some envelope) :
    state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.receive] at hmail
  split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
  next cap hlookup =>
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    next queued hqueued =>
      by_cases heq : endpoint = cap.object
      · subst endpoint
        simp [EndpointIPC.setOption] at hmail
      · simpa [EndpointIPC.setOption, heq] using hmail

/-- A successful data send is one complete global-invariant mutation.  The
endpoint post-state is published to both the IPC and sealed-transfer views,
while the latter's pending attachment map is retained exactly. -/
theorem gate_ipc_send_accepted_preserves_runtimeWellFormed state handleWord word0 word1
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hsent : (dispatchIPC state (.send handleWord word0 word1)).reply =
      .syscall .sent) :
    RuntimeWellFormed (gate state (.ipc (.send handleWord word0 word1))).state ∧
      (gate state (.ipc (.send handleWord word0 word1))).result =
        .completed (.ipc (.syscall .sent)) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
      hmemoryCaps, hipcVirtual, hipcCaps, hresumableScheduler,
      htranslationVirtual, htransferEndpoints, hcontext, hdead, hsender⟩
  cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | error reason => simp [dispatchIPC, IPCSyscall.dispatch, hresolve] at hsent
  | ok resolution =>
      cases hsend : EndpointIPC.send state.ipc.endpoints
          state.execution.core.context.currentSubject resolution.handle.slot
          { word0, word1 } with
      | mk endpoints result =>
          cases result with
          | rejected reason =>
              simp [dispatchIPC, IPCSyscall.dispatch, hresolve, hsend] at hsent
          | accepted =>
              have hdispatch :
                  IPCSyscall.dispatch state.ipc state.ipcContext
                    (.send handleWord word0 word1) =
                    { state := { state.ipc with endpoints }
                      reply := .sent } := by
                simp [IPCSyscall.dispatch, hresolve, hsend]
              have hcapEq : endpoints.capabilities = state.ipc.endpoints.capabilities := by
                simpa [hsend] using endpointSend_capabilities_unchanged
                  state.ipc.endpoints state.execution.core.context.currentSubject
                  resolution.handle.slot { word0, word1 }
              have hipc' : IPCSyscall.WellFormed
                  (IPCSyscall.dispatch state.ipc state.ipcContext
                    (.send handleWord word0 word1)).state :=
                IPCSyscall.dispatch_preserves_wellFormed state.ipc state.ipcContext
                  (.send handleWord word0 word1) hipc
              have hendpoint : EndpointIPC.WellFormed endpoints := by
                have preserved := EndpointIPC.send_preserves_wellFormed state.ipc.endpoints
                  state.execution.core.context.currentSubject resolution.handle.slot
                  { word0, word1 } hipc.2
                simpa [hsend] using preserved
              have htransfers' : CapabilityTransfer.WellFormed
                  { state.transfers with toEndpointState := endpoints } := by
                refine ⟨hendpoint, ?_⟩
                intro endpoint transfer hpending
                have hold := htransfers.2 endpoint transfer hpending
                rcases hold with ⟨⟨envelope, hmailbox, henvelope⟩, hrest⟩
                rw [htransferEndpoints] at hmailbox
                refine ⟨⟨envelope, ?_, henvelope⟩, ?_⟩
                · simpa [hsend] using
                    endpointSend_preserves_occupied_mailbox
                      state.ipc.endpoints
                      state.execution.core.context.currentSubject
                      resolution.handle.slot { word0, word1 } endpoint envelope hmailbox
                · simpa [htransferEndpoints, hcapEq] using hrest
              have hcoherent' :
                  (installIPC state
                    (IPCSyscall.dispatch state.ipc state.ipcContext
                      (.send handleWord word0 word1)).state).Coherent := by
                simp only [CompositeState.Coherent, installIPC]
                refine ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
                  hmemoryCaps, ?_, ?_, hresumableScheduler, htranslationVirtual, ?_,
                  hcontext, ?_, ?_⟩
                · simpa [IPCSyscall.dispatch, hresolve, hsend] using hipcVirtual
                · simpa [hdispatch, hcapEq] using hipcCaps
                · simp [IPCSyscall.dispatch, hresolve, hsend]
                · intro object hnotLive
                  simpa [hdispatch] using
                    hendpoint.2.2.2.1 object (by simpa [hcapEq, hipcCaps] using hnotLive)
                · intro object envelope hmail
                  have hliveSender := endpointSend_preserves_live_senders state.ipc.endpoints
                    state.execution.core.context.currentSubject resolution.handle.slot
                    { word0, word1 } hipc.2.1 (by
                      intro priorObject priorEnvelope hprior
                      simpa [hipcCaps] using hsender priorObject priorEnvelope hprior)
                    object envelope (by simpa [hdispatch, hsend] using hmail)
                  simpa [hsend, hcapEq, hipcCaps] using hliveSender
              constructor
              · rw [hdispatch] at hipc' hcoherent'
                simpa [gate, hmode, applyOperation, dispatchIPC, IPCSyscall.dispatch,
                  hresolve, hsend, installIPC, hdispatch] using
                  ⟨hcoherent', hexecution, hlifecycle, hcapabilities, hvirtual, hipc',
                    hscheduler, hpreemption, hresumable, htransfers', hhalted, hlive⟩
              · simp [gate, hmode, operationReply, dispatchIPC, IPCSyscall.dispatch,
                  hresolve, hsend]

/-- A successful data-only receive consumes exactly the selected untagged
mailbox while retaining every sealed attachment at every other endpoint.  The
updated endpoint state is published to both IPC views and preserves the full
runtime invariant together with the exact provenance-bearing delivery reply. -/
theorem gate_ipc_receive_accepted_preserves_runtimeWellFormed state handleWord sender word0 word1
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (dispatchIPC state (.receive handleWord)).reply =
      .syscall (.delivered sender word0 word1)) :
    RuntimeWellFormed (gate state (.ipc (.receive handleWord))).state ∧
      (gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc (.syscall (.delivered sender word0 word1))) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
      hmemoryCaps, hipcVirtual, hipcCaps, hresumableScheduler,
      htranslationVirtual, htransferEndpoints, hcontext, hdead, hsender⟩
  have htransferCaps : state.transfers.capabilities = state.ipc.endpoints.capabilities := by
    simp [htransferEndpoints]
  cases hguard : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | error guardReason =>
      have hguard' : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint = .error guardReason := by
        simpa [htransferCaps] using hguard
      simp [dispatchIPC, IPCSyscall.dispatch, hguard, hguard'] at hdelivered
  | ok guarded =>
      cases hpending : state.transfers.pending guarded.capability.object with
      | some transfer =>
          simp [dispatchIPC, hguard, hpending] at hdelivered
      | none =>
          have hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
              { caller := state.execution.core.context.currentSubject }
              handleWord .endpoint = .ok guarded := by
            simpa [htransferCaps] using hguard
          have hsound := CapabilityHandle.resolveCurrent_sound
            state.ipc.endpoints.capabilities
            { caller := state.execution.core.context.currentSubject }
            handleWord .endpoint guarded hresolve
          have hlookup : Capability.lookup state.ipc.endpoints.capabilities
              state.execution.core.context.currentSubject guarded.handle.slot =
              .found guarded.capability := by
            rcases hsound with ⟨_, hsubject, hrange, hslot, _⟩
            simp [Capability.lookup, hsubject, hrange, hslot]
          cases hreceive : EndpointIPC.receive state.ipc.endpoints
              state.execution.core.context.currentSubject guarded.handle.slot with
          | mk endpoints result =>
              cases result with
              | rejected reason =>
                  simp [dispatchIPC, IPCSyscall.dispatch, hguard, hpending,
                    hresolve, hreceive] at hdelivered
              | delivered envelope =>
                  have henvelope : envelope.sender = sender ∧
                      envelope.payload.word0 = word0 ∧ envelope.payload.word1 = word1 := by
                    simpa [dispatchIPC, IPCSyscall.dispatch, hguard, hpending,
                      hresolve, hreceive] using hdelivered
                  have hdispatch :
                      IPCSyscall.dispatch state.ipc state.ipcContext (.receive handleWord) =
                        { state := { state.ipc with endpoints }
                          reply := .delivered sender word0 word1 } := by
                    rcases henvelope with ⟨rfl, rfl, rfl⟩
                    simp [IPCSyscall.dispatch, hresolve, hreceive]
                  have hcapEq : endpoints.capabilities = state.ipc.endpoints.capabilities := by
                    simpa [hreceive] using endpointReceive_capabilities_unchanged
                      state.ipc.endpoints state.execution.core.context.currentSubject
                      guarded.handle.slot
                  have hipc' : IPCSyscall.WellFormed
                      (IPCSyscall.dispatch state.ipc state.ipcContext
                        (.receive handleWord)).state :=
                    IPCSyscall.dispatch_preserves_wellFormed state.ipc state.ipcContext
                      (.receive handleWord) hipc
                  have hendpoint : EndpointIPC.WellFormed endpoints := by
                    have preserved := EndpointIPC.receive_preserves_wellFormed
                      state.ipc.endpoints state.execution.core.context.currentSubject
                      guarded.handle.slot hipc.2
                    simpa [hreceive] using preserved
                  have htransfers' : CapabilityTransfer.WellFormed
                      { state.transfers with toEndpointState := endpoints } := by
                    refine ⟨hendpoint, ?_⟩
                    intro endpoint transfer hotherPending
                    have hold := htransfers.2 endpoint transfer hotherPending
                    rcases hold with ⟨⟨priorEnvelope, hmailbox, henvelope'⟩, hrest⟩
                    have hne : endpoint ≠ guarded.capability.object := by
                      intro heq
                      subst endpoint
                      rw [hpending] at hotherPending
                      contradiction
                    rw [htransferEndpoints] at hmailbox
                    refine ⟨⟨priorEnvelope, ?_, henvelope'⟩, ?_⟩
                    · simpa [hreceive] using endpointReceive_preserves_other_mailbox
                        state.ipc.endpoints state.execution.core.context.currentSubject
                        guarded.handle.slot guarded.capability endpoint priorEnvelope
                        hlookup hne hmailbox
                    · simpa [htransferEndpoints, hcapEq] using hrest
                  have hcoherent' :
                      (installIPC state
                        (IPCSyscall.dispatch state.ipc state.ipcContext
                          (.receive handleWord)).state).Coherent := by
                    simp only [CompositeState.Coherent, installIPC]
                    refine ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
                      hmemoryCaps, ?_, ?_, hresumableScheduler, htranslationVirtual, ?_,
                      hcontext, ?_, ?_⟩
                    · simpa [IPCSyscall.dispatch, hresolve, hreceive] using hipcVirtual
                    · simpa [hdispatch, hcapEq] using hipcCaps
                    · simp [IPCSyscall.dispatch, hresolve, hreceive]
                    · intro object hnotLive
                      simpa [hdispatch] using
                        hendpoint.2.2.2.1 object (by simpa [hcapEq, hipcCaps] using hnotLive)
                    · intro object found hmail
                      have hnext : endpoints.mailbox object = some found := by
                        simpa [hdispatch] using hmail
                      have hprior := endpointReceive_mailbox_provenance
                        state.ipc.endpoints state.execution.core.context.currentSubject
                        guarded.handle.slot object found (by simpa [hreceive] using hnext)
                      exact hsender object found hprior
                  constructor
                  · rw [hdispatch] at hipc' hcoherent'
                    simpa [gate, hmode, applyOperation, dispatchIPC, hguard, hpending,
                      IPCSyscall.dispatch, hresolve, hreceive, installIPC, hdispatch] using
                      ⟨hcoherent', hexecution, hlifecycle, hcapabilities, hvirtual, hipc',
                        hscheduler, hpreemption, hresumable, htransfers', hhalted, hlive⟩
                  · simpa [gate, hmode, operationReply, dispatchIPC, hguard, hpending,
                      IPCSyscall.dispatch, hresolve, hreceive, hdispatch] using henvelope

/-- An accepted public transfer offer is backed by a whole-invariant
preserving sealed-transfer mutation and is reported as that exact typed
success by the composite gate.  The remaining global lift is isolated to the
publication laws of `installTransfers`, rather than the authority transition. -/
theorem gate_transferOffer_accepted_preserves_transferWellFormed state endpointWord sourceWord
    sourceKind payload rights
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (CapabilityTransfer.offerWords state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
      payload rights).result = .accepted) :
    CapabilityTransfer.WellFormed
        (CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
          payload rights).state ∧
      (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer .accepted) := by
  constructor
  · exact CapabilityTransfer.offerWords_accepted_preserves_wellFormed
      state.transfers state.execution.core.context.currentSubject endpointWord sourceWord
      sourceKind payload rights hstate.2.2.2.2.2.2.2.2.2.1 haccepted
  · simp [gate, hmode, operationReply, applyOperation, haccepted]

/-- An accepted public transfer receipt preserves the authoritative capability
invariant and reports the exact provenance-bearing envelope and installed
generation word.  This closes the capability-store slice needed before the
stronger whole-runtime publication theorem for `installTransfers`. -/
theorem gate_transferAccept_delivered_preserves_capabilityWellFormed state endpointWord
    destinationSlot envelope
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (CapabilityTransfer.acceptWord state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot).result =
        .delivered envelope) :
    Capability.WellFormed
        (CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot).state.capabilities ∧
      (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept (.delivered envelope)
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord
            destinationSlot).deliveredWord) := by
  have htransfer := hstate.2.2.2.2.2.2.2.2.2.1
  cases hendpoint : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      endpointWord .endpoint with
  | error reason =>
      cases reason with
      | malformed decodeReason =>
          simp [CapabilityTransfer.acceptWord, hendpoint,
            CapabilityTransfer.rejectAccept] at hdelivered
      | denied resolveReason =>
          cases resolveReason <;>
            simp [CapabilityTransfer.acceptWord, hendpoint,
              CapabilityTransfer.rejectAccept] at hdelivered
  | ok endpoint =>
      cases hpending : state.transfers.pending endpoint.capability.object with
      | none =>
          have hpreserved := CapabilityTransfer.accept_preserves_capabilityWellFormed
            state.transfers state.execution.core.context.currentSubject endpoint.handle.slot
            destinationSlot htransfer
          constructor
          · simpa [CapabilityTransfer.acceptWord, hendpoint, hpending] using hpreserved
          · simp [gate, hmode, operationReply, applyOperation, hdelivered]
      | some transfer =>
          by_cases hslot : CapabilityHandle.slotReserved ≤ destinationSlot
          · simp [CapabilityTransfer.acceptWord, hendpoint, hpending, hslot,
              CapabilityTransfer.rejectAccept] at hdelivered
          · by_cases hexhausted : transfer.identity = 0 ∨
                CapabilityHandle.generationReserved ≤ transfer.identity
            · simp [CapabilityTransfer.acceptWord, hendpoint, hpending, hslot, hexhausted,
                CapabilityTransfer.rejectAccept] at hdelivered
            · have hpreserved := CapabilityTransfer.accept_preserves_capabilityWellFormed
                  state.transfers state.execution.core.context.currentSubject endpoint.handle.slot
                  destinationSlot htransfer
              constructor
              · simpa [CapabilityTransfer.acceptWord, hendpoint, hpending, hslot, hexhausted]
                  using hpreserved
              · simp [gate, hmode, operationReply, applyOperation, hdelivered]

/-- The complete sealed-transfer invariant, not only its embedded capability
store, survives every delivered public receipt.  The composite reply remains
paired with the exact state and generation word that produced it. -/
theorem gate_transferAccept_delivered_preserves_transferWellFormed state endpointWord
    destinationSlot envelope
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (CapabilityTransfer.acceptWord state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot).result =
        .delivered envelope) :
    CapabilityTransfer.WellFormed
        (CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot).state ∧
      (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept (.delivered envelope)
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord
            destinationSlot).deliveredWord) := by
  constructor
  · exact CapabilityTransfer.acceptWord_preserves_wellFormed state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot
      hstate.2.2.2.2.2.2.2.2.2.1
  · simp [gate, hmode, operationReply, applyOperation, hdelivered]

/-- Busy and terminal rejection are invariant-preserving for every operation;
neither path invokes a synchronization helper or a subsystem transition. -/
theorem gate_rejected_mode_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state)
    (hnotRunning : state.execution.mode ≠ .running) :
    RuntimeWellFormed (gate state operation).state := by
  cases hmode : state.execution.mode with
  | running => exact False.elim (hnotRunning hmode)
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate

/-- An accepted queue insertion is a sound composite mutation: its public
reply is the scheduler's accepted reply, its scheduler projection is the exact
subsystem post-state, and that projection remains well formed. -/
theorem gate_scheduleAdd_accepted_sound state subject context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state (.scheduleAdd subject)).state.scheduler = next ∧
      Scheduler.WellFormed (gate state (.scheduleAdd subject)).state.scheduler := by
  have hpreserved := Scheduler.add_preserves_wellFormed state.scheduler subject hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted, hpreserved]

/-- An accepted dispatch likewise cannot be paired with a repaired or
caller-selected scheduler: the composite projection is exactly the state that
produced the typed dispatch context, and its invariant is preserved. -/
theorem gate_scheduleNext_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.selectNext state.scheduler =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleNext).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleNext).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleNext).state.scheduler := by
  have hpreserved := Scheduler.selectNext_preserves_wellFormed state.scheduler hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted, hpreserved]

/-- Accepted queue removal publishes the exact resumable-aware cleanup result,
including saved-context consumption and active-translation invalidation. -/
theorem gate_scheduleRemove_accepted_sound state subject context next
    (hmode : state.execution.mode = .running)
    (haccepted : ResumablePreemption.remove state.resumable subject =
      { state := next, result := .accepted context })
    (hwellFormed : ResumablePreemption.WellFormed state.resumable) :
    (gate state (.scheduleRemove subject)).result =
        .completed (.scheduleRemove (.accepted context)) ∧
      (gate state (.scheduleRemove subject)).state.resumable = next ∧
      ResumablePreemption.WellFormed
        (gate state (.scheduleRemove subject)).state.resumable := by
  have hpreserved := ResumablePreemption.remove_preserves_wellFormed
    state.resumable subject hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted,
    installSchedulerRemoval, hpreserved]

/-- An accepted voluntary yield retains the exact round-robin post-state;
composite synchronization cannot repair or replace the scheduler result. -/
theorem gate_scheduleYield_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.yield state.scheduler =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleYield).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleYield).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleYield).state.scheduler := by
  have hpreserved := Scheduler.yield_preserves_wellFormed state.scheduler hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted, hpreserved]

/-- A successful timer scheduling step is the exact accepted tick transition
and retains the scheduler invariant after all shared projections are updated. -/
theorem gate_scheduleTick_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.tick state.scheduler =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleTick).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleTick).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleTick).state.scheduler := by
  have hpreserved := Scheduler.tick_preserves_wellFormed state.scheduler hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted, hpreserved]

/-- Accepted current-subject termination exposes the exact scheduler cleanup
state, including its filtered queue and terminated lifecycle, and proves that
the scheduler invariant survives the composite publication step. -/
theorem gate_terminateCurrent_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.terminateCurrent state.scheduler =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .terminateCurrent).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .terminateCurrent).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .terminateCurrent).state.scheduler := by
  have hpreserved := Scheduler.terminateCurrent_preserves_wellFormed
    state.scheduler hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted, hpreserved]

/-- Accepted capability copying publishes the exact fresh capability state to
every consumer.  The composite reply cannot report success while lifecycle,
IPC, scheduler, mapping, or saved-context projections retain the old registry. -/
theorem gate_capabilityCopy_accepted_synchronizes state source destination destinationSlot
    rights next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.copy state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights =
        { state := next, result := .accepted })
    (hwellFormed : Capability.WellFormed state.capabilities) :
    (gate state (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability .accepted) ∧
      let published :=
        (gate state (.capabilityCopy source destination destinationSlot rights)).state
      published.Coherent ∧
        published.capabilities = next ∧
        published.lifecycle.capabilities = next ∧
        published.execution.core.lifecycle.capabilities = next ∧
        published.virtualMemory.memory.capabilities = next ∧
        published.ipc.endpoints.capabilities = next ∧
        published.scheduler.lifecycle.capabilities = next ∧
        published.preemption.scheduler.lifecycle.capabilities = next ∧
        published.resumable.scheduler.lifecycle.capabilities = next ∧
        published.transfers.capabilities = next ∧
        Capability.WellFormed published.capabilities := by
  have hpreserved := Capability.copy_preserves_wellFormed state.capabilities
    state.execution.core.context.currentSubject source destination destinationSlot rights hwellFormed
  rw [haccepted] at hpreserved
  have hcoherent : (installCapabilities state next).Coherent := by
    simpa [installCapabilities] using installLifecycle_coherent state
      { state.lifecycle with capabilities := next }
  rcases installCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed (installCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                        (And.intro htransfers hpublished)))))))))

/-- Creating a fresh subject publishes the exact accepted lifecycle through
every lifecycle and capability consumer in one coherent gate step.  The
lifecycle invariant is proved for the published state, rather than merely for
the private `SubjectLifecycle.create` result. -/
theorem gate_createSubject_accepted_synchronizes state subject next
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.create state.lifecycle subject =
      { state := next, result := .accepted })
    (hcoherent : state.Coherent)
    (hwellFormed : SubjectLifecycle.WellFormed state.lifecycle) :
    (gate state (.createSubject subject)).result =
        .completed (.createSubject .accepted) ∧
      let published := (gate state (.createSubject subject)).state
      published.Coherent ∧
        published.lifecycle = next ∧
        published.execution.core.lifecycle = next ∧
        published.scheduler.lifecycle = next ∧
        published.preemption.scheduler.lifecycle = next ∧
        published.resumable.scheduler.lifecycle = next ∧
        published.capabilities = next.capabilities ∧
        published.virtualMemory.memory.capabilities = next.capabilities ∧
        published.ipc.endpoints.capabilities = next.capabilities ∧
        published.transfers.capabilities = next.capabilities ∧
        SubjectLifecycle.WellFormed published.lifecycle := by
  have hpreserved := SubjectLifecycle.create_preserves_wellFormed
    state.lifecycle subject hwellFormed
  rw [haccepted] at hpreserved
  have hpublishedCoherent : (installCreatedSubject state subject).Coherent :=
    installCreatedSubject_coherent state subject hcoherent
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted, installCreatedSubject] using
      And.intro hpublishedCoherent hpreserved

/-- Accepted single-slot revocation is synchronized with every capability
consumer and retains the exact well-formed subsystem post-state. -/
theorem gate_capabilityRevoke_accepted_synchronizes state authoritySlot victim victimSlot next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revoke state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hwellFormed : Capability.WellFormed state.capabilities) :
    (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) ∧
      let published :=
        (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state
      published.Coherent ∧
        published.capabilities = next ∧
        published.lifecycle.capabilities = next ∧
        published.execution.core.lifecycle.capabilities = next ∧
        published.virtualMemory.memory.capabilities = next ∧
        published.ipc.endpoints.capabilities = next ∧
        published.scheduler.lifecycle.capabilities = next ∧
        published.preemption.scheduler.lifecycle.capabilities = next ∧
        published.resumable.scheduler.lifecycle.capabilities = next ∧
        published.transfers.capabilities = next ∧
        Capability.WellFormed published.capabilities := by
  have hpreserved := Capability.revoke_preserves_wellFormed state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot hwellFormed
  rw [haccepted] at hpreserved
  have hcoherent : (installCapabilities state next).Coherent := by
    simpa [installCapabilities] using installLifecycle_coherent state
      { state.lifecycle with capabilities := next }
  rcases installCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed (installCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                        (And.intro htransfers hpublished)))))))))

/-- Accepted subtree revocation is published atomically across every
capability consumer.  The exact authoritative post-state remains well formed,
and the synchronization step establishes the composite coherence equalities
instead of leaving scheduler, IPC, or saved-context views stale. -/
theorem gate_capabilityRevokeSubtree_accepted_synchronizes state authoritySlot victim victimSlot
    next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtree state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hwellFormed : Capability.WellFormed state.capabilities) :
    (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) ∧
      let published :=
        (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state
      published.Coherent ∧
        published.capabilities = next ∧
        published.lifecycle.capabilities = next ∧
        published.execution.core.lifecycle.capabilities = next ∧
        published.virtualMemory.memory.capabilities = next ∧
        published.ipc.endpoints.capabilities = next ∧
        published.scheduler.lifecycle.capabilities = next ∧
        published.preemption.scheduler.lifecycle.capabilities = next ∧
        published.resumable.scheduler.lifecycle.capabilities = next ∧
        published.transfers.capabilities = next ∧
        Capability.WellFormed published.capabilities := by
  have hpreserved := Capability.revokeSubtree_preserves_wellFormed
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim victimSlot
    hwellFormed
  rw [haccepted] at hpreserved
  have hcoherent : (installCapabilities state next).Coherent := by
    simpa [installCapabilities] using installLifecycle_coherent state
      { state.lifecycle with capabilities := next }
  rcases installCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed (installCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                        (And.intro htransfers hpublished)))))))))

/-- A completed syscall exposes exactly the reply produced under the
kernel-selected caller and address space. -/
theorem syscall_result_sound state call
    (hmode : state.execution.mode = .running) :
    (gate state (.syscall call)).result =
      .completed (.syscall (Syscall.dispatch state.virtualMemory state.syscallContext call).reply) :=
  by simp [gate, hmode, operationReply]

/-- A completed IPC call likewise uses only the execution latch's identity;
there is no public constructor capable of supplying another trusted context. -/
theorem ipc_result_sound state call
    (hmode : state.execution.mode = .running) :
    (gate state (.ipc call)).result =
      .completed (.ipc (dispatchIPC state call).reply) :=
  by simp [gate, hmode, operationReply]

/-- Capability authority is always evaluated for the live subject selected by
the execution latch; the public operation has no actor field to vary. -/
theorem capability_copy_result_sound state source destination destinationSlot rights
    (hmode : state.execution.mode = .running) :
    (gate state (.capabilityCopy source destination destinationSlot rights)).result =
      .completed (.capability
        (Capability.copy state.capabilities state.execution.core.context.currentSubject
          source destination destinationSlot rights).result) := by
  simp [gate, hmode, operationReply]

/-- Mapping authority and the target address space are both projected from the
live execution context rather than accepted as public scalar arguments. -/
theorem map_result_sound state slot page permissions
    (hmode : state.execution.mode = .running) :
    (gate state (.map slot page permissions)).result =
      .completed (.map
        (VirtualMapping.map state.virtualMemory state.execution.core.context.currentSubject slot
          state.execution.core.context.activeAddressSpace page permissions).result) := by
  simp [gate, hmode, operationReply]

/-- Accepted mapping publishes only the changed mapping projection.  Memory,
address-space ownership, endpoint state, and every unrelated runtime resource
remain the authoritative pre-state, while all mapping consumers observe the
exact subsystem post-state. -/
theorem gate_map_accepted_preserves_runtimeWellFormed state slot page permissions next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : VirtualMapping.map state.virtualMemory
      state.execution.core.context.currentSubject slot
      state.execution.core.context.activeAddressSpace page permissions =
        { state := next, result := .accepted }) :
    RuntimeWellFormed (gate state (.map slot page permissions)).state ∧
      (gate state (.map slot page permissions)).result = .completed (.map .accepted) := by
  have hmemory := VirtualMapping.map_memory state.virtualMemory
    state.execution.core.context.currentSubject slot
    state.execution.core.context.activeAddressSpace page permissions
  have howner := VirtualMapping.map_owner state.virtualMemory
    state.execution.core.context.currentSubject slot
    state.execution.core.context.activeAddressSpace page permissions
  have hvirtual := VirtualMapping.map_preserves_lifecycleWellFormed
    state.virtualMemory state.execution.core.context.currentSubject slot
    state.execution.core.context.activeAddressSpace page permissions hstate.2.2.2.2.1
  rw [haccepted] at hmemory howner hvirtual
  let translations : TLB.State := { state.resumable.translations with virtual := next }
  have htlb : TLB.Coherent translations := by
    simpa [translations, TLB.Coherent] using
      hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
  have hpreserved := installVirtualMemory_preserves_runtimeWellFormed
    state next translations hstate hmemory howner hvirtual htlb rfl
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, translations] using hpreserved
  · simp [gate, hmode, operationReply, haccepted]

/-- An accepted unmap updates the authoritative virtual-memory projection and
invalidates the matching entry in the owned resumable-context TLB before the
new lifecycle is published.  The composite synchronization step cannot retain
a cached translation for the removed page, and the bounded-cache invariant is
preserved. -/
theorem gate_unmap_accepted_invalidates_tlb state page next
    (hmode : state.execution.mode = .running)
    (haccepted : VirtualMapping.unmap state.virtualMemory
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page =
        { state := next, result := .accepted })
    (hstate : RuntimeWellFormed state) :
    (gate state (.unmap page)).result = .completed (.unmap .accepted) ∧
      RuntimeWellFormed (gate state (.unmap page)).state ∧
      (gate state (.unmap page)).state.Coherent ∧
      TLB.Coherent (gate state (.unmap page)).state.resumable.translations ∧
      ∀ context, TLB.lookup
        (gate state (.unmap page)).state.resumable.translations.entries
        { addressSpace := state.execution.core.context.activeAddressSpace, page }
        context = none := by
  have hmemory : next.memory = state.virtualMemory.memory := by
    have h := VirtualMapping.unmap_memory state.virtualMemory
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page
    rw [haccepted] at h
    exact h
  have howner : next.owner = state.virtualMemory.owner := by
    have h := VirtualMapping.unmap_owner state.virtualMemory
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page
    rw [haccepted] at h
    exact h
  have hvirtual := VirtualMapping.unmap_preserves_lifecycleWellFormed
    state.virtualMemory state.execution.core.context.currentSubject
    state.execution.core.context.activeAddressSpace page hstate.2.2.2.2.1
  rw [haccepted] at hvirtual
  let translations := TLB.invalidatePage
    { state.resumable.translations with virtual := next }
    state.execution.core.context.activeAddressSpace page
  have htlb : TLB.Coherent translations := by
    exact TLB.invalidate_page_preserves_coherent
      { state.resumable.translations with virtual := next }
      state.execution.core.context.activeAddressSpace page hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
  have hpreserved := installVirtualMemory_preserves_runtimeWellFormed
    state next translations hstate hmemory howner hvirtual htlb rfl
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, translations] using hpreserved
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, translations] using hpreserved.1
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, installVirtualMemory,
      translations, TLB.Coherent] using htlb
  · intro context
    simpa [gate, hmode, applyOperation, haccepted, installVirtualMemory,
      translations, TLB.invalidatePage] using
      (TLB.invalidate_page_absent state.resumable.translations.entries
        { addressSpace := state.execution.core.context.activeAddressSpace, page } context)

/-- Initial dispatch is also represented by a typed composite step; syscall
and timer paths reselect only after their final context update. -/
theorem select_user_return_is_reachable state purpose
    (hmode : state.execution.mode = .running) :
    (gate state (.selectUserReturn purpose)).state =
      selectLiveReturnAuthority state purpose := by
  simp [gate, hmode, applyOperation]

theorem syscall_entry_leaves_return_unarmed state frame
    (hmode : state.execution.mode = .running) :
    (gate state (.interrupt frame)).state.execution.returnAuthorityArmed = false := by
  simp [gate, hmode, applyOperation, installLifecycle]

def runOperations (state : CompositeState) : List Operation → CompositeState
  | [] => state
  | operation :: rest => runOperations (gate state operation).state rest

/-- The local proof obligation contributed by one public operation to the
universal runtime-preservation theorem.  Keeping this predicate independent of
a particular pre-state lets operation-family proofs be registered once and
then composed over arbitrary mixed traces. -/
def OperationPreservesRuntimeWellFormed (operation : Operation) : Prop :=
  ∀ state, RuntimeWellFormed state →
    RuntimeWellFormed (gate state operation).state

/-- Per-operation preservation composes over the actual sequential gate.  This
is the reusable induction boundary for the universal theorem: after every
`Operation` constructor satisfies `OperationPreservesRuntimeWellFormed`, every
finite mixed runtime trace preserves the global invariant without unfolding
`runOperations` in each operation-family proof. -/
theorem runOperations_preserves_runtimeWellFormed state operations
    (hstate : RuntimeWellFormed state)
    (hoperations : ∀ operation, operation ∈ operations →
      OperationPreservesRuntimeWellFormed operation) :
    RuntimeWellFormed (runOperations state operations) := by
  induction operations generalizing state with
  | nil => simpa [runOperations] using hstate
  | cons operation rest ih =>
      simp only [runOperations]
      apply ih
      · exact hoperations operation (by simp)
          state hstate
      · intro candidate hmember
        exact hoperations candidate (by simp [hmember])

/-- The two fully covered control constructors discharge the new reusable
operation obligation directly. -/
theorem selectUserReturn_operationPreservesRuntimeWellFormed purpose :
    OperationPreservesRuntimeWellFormed (.selectUserReturn purpose) := by
  intro state hstate
  exact gate_selectUserReturn_preserves_runtimeWellFormed state purpose hstate

/-- Outgoing return is now a complete operation-family instance: successful
attestation is atomic and every terminal rejection synchronizes both fail-stop
projections before the trace continues. -/
theorem userReturn_operationPreservesRuntimeWellFormed request :
    OperationPreservesRuntimeWellFormed (.userReturn request) := by
  intro state hstate
  exact gate_userReturn_preserves_runtimeWellFormed state request hstate

theorem restart_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .restart := by
  intro state hstate
  exact gate_restart_preserves_runtimeWellFormed state hstate

/-- Every raw call that decodes to an access check contributes one complete
operation-family obligation: successful translation is the accepted
non-mutating slice above, while every translation failure is an ordinary
state-preserving subsystem rejection. -/
theorem syscallAccess_operationPreservesRuntimeWellFormed call page access
    (hdecode : Syscall.decode call = .ok (.access page access)) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
    | accepted =>
        exact (gate_syscall_access_accepted_preserves_runtimeWellFormed state call page access
          hstate hmode hdecode hreply).1
    | rejected reason =>
        exact (gate_subsystem_rejection_preserves_runtimeWellFormed state (.syscall call)
          (.syscall (.rejected reason)) hstate
          (by simp [gate, hmode, operationReply, hreply])
          (.syscall call reason hreply)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

/-- Every call rejected by the fixed-width decoder is a complete preservation
family, independently of the attacker-controlled words that failed decoding.
The decoder error is surfaced as the exact typed syscall reply and the
composite gate publishes the literal pre-state.  This closes malformed and
unknown syscall numbers at the reusable operation-registration boundary rather
than requiring mixed-trace proofs to reason about them individually. -/
theorem syscallDecodeRejected_operationPreservesRuntimeWellFormed call reason
    (hdecode : Syscall.decode call = .error reason) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · have hreply :
        (Syscall.dispatch state.virtualMemory state.syscallContext call).reply =
          .rejected (.decode reason) := by
      simp [Syscall.dispatch, hdecode]
    exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
      (.syscall call) (.syscall (.rejected (.decode reason))) hstate
      (by simp [gate, hmode, operationReply, hreply])
      (.syscall call (.decode reason) hreply)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

theorem map_operationPreservesRuntimeWellFormed slot page permissions :
    OperationPreservesRuntimeWellFormed (.map slot page permissions) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hmap : VirtualMapping.map state.virtualMemory
        state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_map_accepted_preserves_runtimeWellFormed state slot page permissions
              next hstate hmode hmap).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.map slot page permissions) (.map (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hmap])
              (.map slot page permissions reason (by simp [hmap]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.map slot page permissions) hstate hmode

theorem unmap_operationPreservesRuntimeWellFormed page :
    OperationPreservesRuntimeWellFormed (.unmap page) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hunmap : VirtualMapping.unmap state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_unmap_accepted_invalidates_tlb state page next hmode hunmap hstate).2.1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.unmap page) (.unmap (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hunmap])
              (.unmap page reason (by simp [hunmap]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.unmap page) hstate hmode

/-- Accepted userspace mapping reuses the raw mapping publication proof after
the generation-bound handle resolves.  The only additional mutation is live
return-authority selection on the already well-formed composite state. -/
theorem syscallMap_operationPreservesRuntimeWellFormed call handleWord page permissions
    (hdecode : Syscall.decode call = .ok (.map handleWord page permissions)) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
    | rejected reason =>
        exact (gate_subsystem_rejection_preserves_runtimeWellFormed state (.syscall call)
          (.syscall (.rejected reason)) hstate
          (by simp [gate, hmode, operationReply, hreply])
          (.syscall call reason hreply)).1
    | accepted =>
        cases hresolve : CapabilityHandle.resolveCurrent state.virtualMemory.memory.capabilities
            { caller := state.syscallContext.caller } handleWord .memory with
        | error denial =>
            simp only [CompositeState.syscallContext] at hresolve
            simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve,
              CompositeState.syscallContext] at hreply
        | ok resolution =>
            simp only [CompositeState.syscallContext] at hresolve
            cases hmap : (VirtualMapping.map state.virtualMemory state.syscallContext.caller
                resolution.handle.slot state.syscallContext.activeAddressSpace page permissions).result with
            | rejected reason =>
                simp only [CompositeState.syscallContext] at hmap
                simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve, hmap,
                  CompositeState.syscallContext] at hreply
            | accepted =>
                simp only [CompositeState.syscallContext] at hmap
                let next := (VirtualMapping.map state.virtualMemory state.syscallContext.caller
                  resolution.handle.slot state.syscallContext.activeAddressSpace page permissions).state
                have hmemory : next.memory = state.virtualMemory.memory := by
                  exact VirtualMapping.map_memory _ _ _ _ _ _
                have howner : next.owner = state.virtualMemory.owner := by
                  exact VirtualMapping.map_owner _ _ _ _ _ _
                have hvirtual : VirtualMapping.LifecycleWellFormed next :=
                  VirtualMapping.map_preserves_lifecycleWellFormed _ _ _ _ _ _
                    hstate.2.2.2.2.1
                let translations : TLB.State :=
                  { state.resumable.translations with virtual := next }
                have htlb : TLB.Coherent translations := by
                  simpa [translations, TLB.Coherent] using
                    hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
                have hinstalled := installVirtualMemory_preserves_runtimeWellFormed
                  state next translations hstate hmemory howner hvirtual htlb rfl
                have hselectedGate := gate_selectUserReturn_preserves_runtimeWellFormed
                  (installVirtualMemory state next translations) .syscallResume hinstalled
                have hselected : RuntimeWellFormed
                    (selectLiveReturnAuthority (installVirtualMemory state next translations)
                      .syscallResume) := by
                  simpa [gate, applyOperation, installVirtualMemory, hmode] using hselectedGate
                have houtcome : Syscall.dispatch state.virtualMemory state.syscallContext call =
                    { state := next, reply := .accepted } := by
                  simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve, hmap,
                    CompositeState.syscallContext, next]
                simpa [gate, hmode, applyOperation, houtcome, hdecode,
                  next, translations] using hselected
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

theorem syscallUnmap_operationPreservesRuntimeWellFormed call page
    (hdecode : Syscall.decode call = .ok (.unmap page)) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
    | rejected reason =>
        exact (gate_subsystem_rejection_preserves_runtimeWellFormed state (.syscall call)
          (.syscall (.rejected reason)) hstate
          (by simp [gate, hmode, operationReply, hreply])
          (.syscall call reason hreply)).1
    | accepted =>
        cases hunmap : (VirtualMapping.unmap state.virtualMemory state.syscallContext.caller
            state.syscallContext.activeAddressSpace page).result with
        | rejected reason =>
            simp only [CompositeState.syscallContext] at hunmap
            simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hunmap,
              CompositeState.syscallContext] at hreply
        | accepted =>
            simp only [CompositeState.syscallContext] at hunmap
            let next := (VirtualMapping.unmap state.virtualMemory state.syscallContext.caller
              state.syscallContext.activeAddressSpace page).state
            have hmemory : next.memory = state.virtualMemory.memory :=
              VirtualMapping.unmap_memory _ _ _ _
            have howner : next.owner = state.virtualMemory.owner :=
              VirtualMapping.unmap_owner _ _ _ _
            have hvirtual : VirtualMapping.LifecycleWellFormed next :=
              VirtualMapping.unmap_preserves_lifecycleWellFormed _ _ _ _ hstate.2.2.2.2.1
            let translations := TLB.invalidatePage
              { state.resumable.translations with virtual := next }
              state.syscallContext.activeAddressSpace page
            have htlb : TLB.Coherent translations := by
              exact TLB.invalidate_page_preserves_coherent _ _ _
                hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
            have hinstalled := installVirtualMemory_preserves_runtimeWellFormed
              state next translations hstate hmemory howner hvirtual htlb rfl
            have hselectedGate := gate_selectUserReturn_preserves_runtimeWellFormed
              (installVirtualMemory state next translations) .syscallResume hinstalled
            have hselected : RuntimeWellFormed
                (selectLiveReturnAuthority (installVirtualMemory state next translations)
                  .syscallResume) := by
              simpa [gate, applyOperation, installVirtualMemory, hmode] using hselectedGate
            have houtcome : Syscall.dispatch state.virtualMemory state.syscallContext call =
                { state := next, reply := .accepted } := by
              simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hunmap,
                CompositeState.syscallContext, next]
            simpa [gate, hmode, applyOperation, houtcome, hdecode,
              next, translations] using hselected
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

/-- Every raw syscall word tuple now satisfies the universal composite
preservation obligation: decoder denial, map, unmap, and access exhaust the
finite decoded vocabulary. -/
theorem syscall_operationPreservesRuntimeWellFormed call :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  cases hdecode : Syscall.decode call with
  | error reason => exact syscallDecodeRejected_operationPreservesRuntimeWellFormed call reason hdecode
  | ok operation =>
      cases operation with
      | map handleWord page permissions =>
          exact syscallMap_operationPreservesRuntimeWellFormed call handleWord page permissions hdecode
      | unmap page => exact syscallUnmap_operationPreservesRuntimeWellFormed call page hdecode
      | access page access => exact syscallAccess_operationPreservesRuntimeWellFormed call page access hdecode

/-- Arbitrary finite mixtures of accepted and rejected raw syscalls preserve
the global runtime invariant through the actual sequential composite gate. -/
theorem runSyscalls_preserves_runtimeWellFormed state (calls : List Syscall.UntrustedCall)
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (runOperations state (calls.map Operation.syscall)) := by
  apply runOperations_preserves_runtimeWellFormed state _ hstate
  intro operation hmember
  obtain ⟨call, _hcall, rfl⟩ := List.mem_map.mp hmember
  exact syscall_operationPreservesRuntimeWellFormed call

private theorem dispatchIPC_send_classifies state handleWord word0 word1 :
    (dispatchIPC state (.send handleWord word0 word1)).reply = .syscall .sent ∨
      (∃ reason, (dispatchIPC state (.send handleWord word0 word1)).reply =
        .syscall (.sendHandleRejected reason)) ∨
      ∃ reason, (dispatchIPC state (.send handleWord word0 word1)).reply =
        .syscall (.sendRejected reason) := by
  cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | error reason =>
      exact Or.inr (Or.inl ⟨reason, by simp [dispatchIPC, IPCSyscall.dispatch, hresolve]⟩)
  | ok resolution =>
      cases hsend : EndpointIPC.send state.ipc.endpoints
          state.execution.core.context.currentSubject resolution.handle.slot
          { word0, word1 } with
      | mk next result =>
          cases result with
          | accepted =>
              exact Or.inl (by simp [dispatchIPC, IPCSyscall.dispatch, hresolve, hsend])
          | rejected reason =>
              exact Or.inr (Or.inr
                ⟨reason, by simp [dispatchIPC, IPCSyscall.dispatch, hresolve, hsend]⟩)

/-- The complete data-send constructor discharges the reusable operation
obligation.  Its unique success reply uses the accepted-send preservation
theorem; every other finite reply is a state-preserving typed rejection. -/
theorem ipcSend_operationPreservesRuntimeWellFormed handleWord word0 word1 :
    OperationPreservesRuntimeWellFormed (.ipc (.send handleWord word0 word1)) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · rcases dispatchIPC_send_classifies state handleWord word0 word1 with
      hsent | ⟨reason, hrejected⟩ | ⟨reason, hrejected⟩
    · exact (gate_ipc_send_accepted_preserves_runtimeWellFormed state
        handleWord word0 word1 hstate hmode hsent).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.send handleWord word0 word1))
        (.ipc (.syscall (.sendHandleRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcSendHandle (.send handleWord word0 word1) reason hrejected)).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.send handleWord word0 word1))
        (.ipc (.syscall (.sendRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcSend (.send handleWord word0 word1) reason hrejected)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.ipc (.send handleWord word0 word1)) hstate hmode

private theorem dispatchIPC_receive_classifies state handleWord :
    (dispatchIPC state (.receive handleWord)).reply = .sealedTransferPending ∨
      (∃ sender word0 word1, (dispatchIPC state (.receive handleWord)).reply =
        .syscall (.delivered sender word0 word1)) ∨
      (∃ reason, (dispatchIPC state (.receive handleWord)).reply =
        .syscall (.receiveHandleRejected reason)) ∨
      ∃ reason, (dispatchIPC state (.receive handleWord)).reply =
        .syscall (.receiveRejected reason) := by
  cases hguard : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | ok endpoint =>
      cases hpending : state.transfers.pending endpoint.capability.object with
      | some transfer =>
          exact Or.inl (by simp [dispatchIPC, hguard, hpending])
      | none =>
          cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
              { caller := state.execution.core.context.currentSubject }
              handleWord .endpoint with
          | error reason =>
              exact Or.inr (Or.inr (Or.inl
                ⟨reason, by simp [dispatchIPC, hguard, hpending,
                  IPCSyscall.dispatch, hresolve]⟩))
          | ok resolution =>
              cases hreceive : EndpointIPC.receive state.ipc.endpoints
                  state.execution.core.context.currentSubject resolution.handle.slot with
              | mk next result =>
                  cases result with
                  | delivered envelope =>
                      exact Or.inr (Or.inl
                        ⟨envelope.sender, envelope.payload.word0, envelope.payload.word1,
                          by simp [dispatchIPC, hguard, hpending,
                            IPCSyscall.dispatch, hresolve, hreceive]⟩)
                  | rejected reason =>
                      exact Or.inr (Or.inr (Or.inr
                        ⟨reason, by simp [dispatchIPC, hguard, hpending,
                          IPCSyscall.dispatch, hresolve, hreceive]⟩))
  | error guardReason =>
      cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint with
      | error reason =>
          exact Or.inr (Or.inr (Or.inl
            ⟨reason, by simp [dispatchIPC, hguard, IPCSyscall.dispatch, hresolve]⟩))
      | ok resolution =>
          cases hreceive : EndpointIPC.receive state.ipc.endpoints
              state.execution.core.context.currentSubject resolution.handle.slot with
          | mk next result =>
              cases result with
              | delivered envelope =>
                  exact Or.inr (Or.inl
                    ⟨envelope.sender, envelope.payload.word0, envelope.payload.word1,
                      by simp [dispatchIPC, hguard, IPCSyscall.dispatch, hresolve, hreceive]⟩)
              | rejected reason =>
                  exact Or.inr (Or.inr (Or.inr
                    ⟨reason, by simp [dispatchIPC, hguard,
                      IPCSyscall.dispatch, hresolve, hreceive]⟩))

/-- The complete data-receive constructor likewise composes accepted delivery,
sealed-mailbox protection, ordinary endpoint rejection, and outer latch
rejection into one operation-family preservation theorem. -/
theorem ipcReceive_operationPreservesRuntimeWellFormed handleWord :
    OperationPreservesRuntimeWellFormed (.ipc (.receive handleWord)) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · rcases dispatchIPC_receive_classifies state handleWord with
      hsealed | ⟨sender, word0, word1, hdelivered⟩ |
        ⟨reason, hrejected⟩ | ⟨reason, hrejected⟩
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.receive handleWord)) (.ipc .sealedTransferPending) hstate
        (by simp [gate, hmode, operationReply, hsealed])
        (.ipcSealed (.receive handleWord) hsealed)).1
    · exact (gate_ipc_receive_accepted_preserves_runtimeWellFormed state
        handleWord sender word0 word1 hstate hmode hdelivered).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.receive handleWord))
        (.ipc (.syscall (.receiveHandleRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcReceiveHandle (.receive handleWord) reason hrejected)).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.receive handleWord))
        (.ipc (.syscall (.receiveRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcReceive (.receive handleWord) reason hrejected)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.ipc (.receive handleWord)) hstate hmode

/-- The public IPC constructor is now one complete universal-preservation
family.  Call-shape case analysis is confined to this registration boundary;
mixed traces can quantify over an arbitrary untrusted IPC call and reuse the
generic `OperationPreservesRuntimeWellFormed` induction contract directly. -/
theorem ipc_operationPreservesRuntimeWellFormed call :
    OperationPreservesRuntimeWellFormed (.ipc call) := by
  cases call with
  | send handleWord word0 word1 =>
      exact ipcSend_operationPreservesRuntimeWellFormed handleWord word0 word1
  | receive handleWord =>
      exact ipcReceive_operationPreservesRuntimeWellFormed handleWord

/-- Resumable-aware scheduler removal closes the cleanup obligation exposed by
the raw scheduler transition.  Saved context and active translation cleanup
are published with the scheduler post-state, while the no-peer case is a typed,
state-preserving rejection. -/
theorem scheduleRemove_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.scheduleRemove subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hremove : ResumablePreemption.remove state.resumable subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.scheduleRemove subject) (.scheduleRemove (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hremove])
              (.scheduleRemove subject reason (by simp [hremove]))).1
        | accepted context =>
            rcases hstate with
              ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
                hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
            rcases hcoherent with
              ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
                hcapabilitiesCoherent, hvirtualCapabilitiesCoherent,
                hipcVirtualCoherent, hipcCapabilitiesCoherent,
                hresumableSchedulerCoherent, hresumableVirtualCoherent,
                htransfersCoherent, hauthorityCoherent, hdeadMailbox, hliveSender⟩
            have hresumable' := ResumablePreemption.remove_preserves_wellFormed
              state.resumable subject hresumable
            rw [hremove] at hresumable'
            rcases ResumablePreemption.remove_accepted_exact state.resumable subject context
                (by simp [hremove]) with
              ⟨scheduler, hschedulerRemove, hnext, hpeer⟩
            rw [hremove] at hnext
            change next = ResumablePreemption.removeState
              state.resumable subject scheduler at hnext
            subst next
            have hschedulerRemove' : Scheduler.remove state.scheduler subject =
                { state := scheduler, result := .accepted context } := by
              rw [← hresumableSchedulerCoherent]
              exact hschedulerRemove
            have hschedulerCapabilities :
                scheduler.lifecycle.capabilities = state.lifecycle.capabilities := by
              simp only [Scheduler.remove] at hschedulerRemove'
              split at hschedulerRemove'
              · rcases hschedulerRemove' with ⟨rfl, rfl⟩
                exact hschedulerCoherent ▸ rfl
              · simp_all [Scheduler.reject]
            have hvirtualProjection :
                (ResumablePreemption.removeState state.resumable subject scheduler).translations.virtual =
                  state.virtualMemory := by
              simpa [ResumablePreemption.removeState] using hresumableVirtualCoherent
            have hcoherent' :
                (installSchedulerRemoval state
                  (ResumablePreemption.removeState state.resumable subject scheduler)).Coherent := by
              refine ⟨rfl, rfl, rfl, ?_, ?_, hipcVirtualCoherent, ?_, rfl,
                hvirtualProjection, htransfersCoherent, ?_, ?_, ?_⟩
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hcapabilitiesCoherent, hschedulerCapabilities]
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hvirtualCapabilitiesCoherent, hschedulerCapabilities]
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hipcCapabilitiesCoherent, hschedulerCapabilities]
              · intro current hcurrent
                simp only [installSchedulerRemoval, ResumablePreemption.removeState] at hcurrent ⊢
                cases hschedulerCurrent : scheduler.lifecycle.current with
                | none => simp [hschedulerCurrent] at hcurrent
                | some actual =>
                    simp [hschedulerCurrent] at hcurrent
                    subst current
                    simp [hschedulerCurrent]
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hschedulerCapabilities]
                exact hdeadMailbox
              · simp only [installSchedulerRemoval, ResumablePreemption.removeState]
                rw [hschedulerCapabilities]
                exact hliveSender
            simp only [gate, hmode, applyOperation, hremove]
            refine ⟨hcoherent', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hresumable', ?_, ?_, ?_⟩
            · rcases hexecution with ⟨hexecutionCore, _hbound, hmodeWellFormed⟩
              refine ⟨?_, by simp [installSchedulerRemoval], ?_⟩
              · simpa [Interrupt.WellFormed, installSchedulerRemoval] using
                  hresumable'.1.1
              · cases hschedulerCurrent : scheduler.lifecycle.current <;>
                  simpa [installSchedulerRemoval, ResumablePreemption.removeState,
                    hschedulerCurrent] using hmodeWellFormed
            · exact hresumable'.1.1
            · exact hcapabilities
            · exact hvirtual
            · exact hipc
            · exact hresumable'.1
            · rcases hpreemption with ⟨_, hticks⟩
              exact ⟨hresumable'.1, hticks⟩
            · exact htransfers
            · simpa [installSchedulerRemoval, ResumablePreemption.removeState] using hhalted
            · simp [installSchedulerRemoval]
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.scheduleRemove subject) hstate hmode

/-- Creating a fresh subject only promotes its monotonic lifecycle identity;
all existing resource, scheduler, context-bank, mailbox, and translation
facts remain valid when the new lifecycle is published to their projections. -/
theorem createSubject_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.createSubject subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hcreate : SubjectLifecycle.create state.lifecycle subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.createSubject subject) (.createSubject (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hcreate])
              (.createSubject subject reason (by simp [hcreate]))).1
        | accepted =>
            have hcreateDef := hcreate
            simp only [SubjectLifecycle.create] at hcreateDef
            split at hcreateDef <;> try simp_all [SubjectLifecycle.reject]
            split at hcreateDef <;> try simp_all [SubjectLifecycle.reject]
            next hlive hissued =>
              rcases hcreateDef with ⟨rfl, rfl⟩
              simp only [gate, hmode, applyOperation, hcreate]
              rcases hstate with
                ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
                  hscheduler, hpreemption, hresumable, htransfers, hhalted, hlivePlan⟩
              have hlifecycle' := SubjectLifecycle.create_preserves_wellFormed
                state.lifecycle subject hlifecycle
              rw [hcreate] at hlifecycle'
              have hcapabilitiesLifecycle :
                  Capability.WellFormed state.lifecycle.capabilities := by
                rw [← hcoherent.2.2.2.1]
                exact hcapabilities
              have hvirtualCapabilitiesCoherent :
                  state.virtualMemory.memory.capabilities =
                    state.lifecycle.capabilities := hcoherent.2.2.2.2.1
              have hipcCapabilitiesCoherent :
                  state.ipc.endpoints.capabilities =
                    state.lifecycle.capabilities := hcoherent.2.2.2.2.2.2.1
              have hcapabilities' : Capability.WellFormed
                  (SubjectLifecycle.create state.lifecycle subject).state.capabilities := by
                rw [hcreate]
                rcases hcapabilitiesLifecycle with
                  ⟨hslots, hderivations, hunique, hspaces⟩
                refine ⟨?_, hderivations, hunique, hspaces⟩
                intro holder slot capability hslot
                have hold := hslots holder slot capability hslot
                refine ⟨?_, hold.2⟩
                simp only [SubjectLifecycle.setBool]
                split <;> simp_all
              have hvirtual' : VirtualMapping.LifecycleWellFormed
                  (installCreatedSubject state subject).virtualMemory := by
                rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hvirtualCaps,
                  haddressSpaces, hownedSpaces⟩
                refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
                · intro addressSpace owner howner
                  have hold := hownerLive addressSpace owner (by
                    simpa [installCreatedSubject] using howner)
                  rw [hvirtualCapabilitiesCoherent] at hold
                  simpa [installCreatedSubject] using
                    createSubject_preserves_live state.lifecycle subject owner hold
                · intro addressSpace page mapping hmapping
                  obtain ⟨owner, frame, howner, hpermissions, hbinding, hframe,
                    hread, hwrite⟩ := hmappings addressSpace page mapping (by
                      simpa [installCreatedSubject] using hmapping)
                  refine ⟨owner, frame, ?_, hpermissions, ?_, hframe, ?_, ?_⟩
                  · simpa [installCreatedSubject] using howner
                  · simpa [installCreatedSubject] using hbinding
                  · intro hpermission
                    have hold := hread hpermission
                    rw [hvirtualCapabilitiesCoherent] at hold
                    simpa [installCreatedSubject, hcreate, Capability.HasAuthority] using hold
                  · intro hpermission
                    have hold := hwrite hpermission
                    rw [hvirtualCapabilitiesCoherent] at hold
                    simpa [installCreatedSubject, hcreate, Capability.HasAuthority] using hold
                · simpa [installCreatedSubject, hcreate] using hcapabilities'
                · intro addressSpace owner howner
                  have hold := haddressSpaces addressSpace owner (by
                    simpa [installCreatedSubject] using howner)
                  rw [hvirtualCapabilitiesCoherent] at hold
                  simpa [installCreatedSubject, hcreate, Capability.HasAuthority] using hold
                · intro addressSpace hlive hkind
                  have hliveOld :
                      state.virtualMemory.memory.capabilities.objects addressSpace = true := by
                    rw [hvirtualCapabilitiesCoherent]
                    simpa [installCreatedSubject, hcreate] using hlive
                  have hkindOld :
                      state.virtualMemory.memory.capabilities.kinds addressSpace =
                        some .addressSpace := by
                    rw [hvirtualCapabilitiesCoherent]
                    simpa [installCreatedSubject, hcreate] using hkind
                  obtain ⟨owner, howner⟩ := hownedSpaces addressSpace
                    hliveOld hkindOld
                  exact ⟨owner, by simpa [installCreatedSubject] using howner⟩
              have hipc' : IPCSyscall.WellFormed
                  (installCreatedSubject state subject).ipc := by
                rcases hipc with ⟨_virtual, hendpoints⟩
                rcases hendpoints with
                  ⟨_hendpointCaps, hissuedEndpoint, hmailbox, hdead, hhistory⟩
                rw [hipcCapabilitiesCoherent] at hissuedEndpoint hmailbox hdead
                refine ⟨hvirtual', ?_⟩
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simpa [installCreatedSubject, hcreate] using hcapabilities'
                · simpa [installCreatedSubject, hcreate] using hissuedEndpoint
                · simpa [installCreatedSubject, hcreate] using hmailbox
                · simpa [installCreatedSubject, hcreate] using hdead
                · simpa [installCreatedSubject] using hhistory
              have hscheduler' : Scheduler.WellFormed
                  (installCreatedSubject state subject).scheduler := by
                rcases hscheduler with
                  ⟨_hschedulerLifecycle, hreadyNodup, hreadyCapacity,
                    hreadyValid, hcurrentValid⟩
                simp only [Scheduler.ownsAddressSpace] at hreadyValid hcurrentValid
                rw [hcoherent.2.1] at hreadyValid hcurrentValid
                refine ⟨?_, hreadyNodup, hreadyCapacity, ?_, ?_⟩
                · simpa [installCreatedSubject, hcreate] using hlifecycle'
                · intro candidate hmember
                  obtain ⟨hliveCandidate, hrunnable, howner⟩ :=
                    hreadyValid candidate hmember
                  refine ⟨?_, ?_, ?_⟩
                  · exact createSubject_preserves_live state.lifecycle subject candidate
                      hliveCandidate
                  · simpa [installCreatedSubject, hcreate] using hrunnable
                  · simpa [Scheduler.ownsAddressSpace, installCreatedSubject,
                      hcreate] using howner
                · intro candidate hcurrent
                  obtain ⟨hliveCandidate, hrunnable, howner⟩ :=
                    hcurrentValid candidate (by
                      simpa [installCreatedSubject] using hcurrent)
                  refine ⟨?_, ?_, ?_⟩
                  · exact createSubject_preserves_live state.lifecycle subject candidate
                      hliveCandidate
                  · simpa [installCreatedSubject, hcreate] using hrunnable
                  · simpa [Scheduler.ownsAddressSpace, installCreatedSubject,
                      hcreate] using howner
              have hpreemption' : Preemption.WellFormed
                  (installCreatedSubject state subject).preemption := by
                rcases hpreemption with ⟨_hscheduler, hticks⟩
                refine ⟨hscheduler', ?_⟩
                change state.preemption.acceptedTicks =
                  if state.preemption.timerArmed then 0 else 1
                exact hticks
              have hresumableLifecycle :
                  state.resumable.scheduler.lifecycle = state.lifecycle := by
                rw [hcoherent.2.2.2.2.2.2.2.1, hcoherent.2.1]
              have hresumable' : ResumablePreemption.WellFormed
                  (installCreatedSubject state subject).resumable := by
                rcases hresumable with
                  ⟨_hscheduler, hcapacity, hunique, hvalid, habsent, hready,
                    htranslation, _hvirtualAgreement, hkinds, htlb⟩
                simp only [ResumablePreemption.ReadyContextAgreement] at hready
                simp only [ResumablePreemption.TranslationAgreement] at htranslation
                simp only [ResumablePreemption.ResourceKindAgreement] at hkinds
                rw [hcoherent.2.2.2.2.2.2.2.1] at habsent hready htranslation hkinds
                rw [hcoherent.2.2.2.2.2.2.2.2.1] at htranslation
                rw [hcoherent.2.1] at habsent hready htranslation hkinds
                refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro context hcontext
                  rcases hvalid context hcontext with
                    ⟨hframe, hspace, hliveOwner, hrunnable, howner⟩
                  rw [hresumableLifecycle] at hliveOwner hrunnable howner
                  refine ⟨hframe, hspace, ?_, ?_, ?_⟩
                  · exact createSubject_preserves_live state.lifecycle subject context.owner
                      hliveOwner
                  · simpa [installCreatedSubject, hcreate] using hrunnable
                  · simpa [installCreatedSubject, hcreate] using howner
                · simpa [installCreatedSubject] using habsent
                · simpa [ResumablePreemption.ReadyContextAgreement,
                    installCreatedSubject] using hready
                · simpa [ResumablePreemption.TranslationAgreement,
                    installCreatedSubject, hcreate] using htranslation
                · exact ⟨rfl, hvirtual'⟩
                · simpa [ResumablePreemption.ResourceKindAgreement,
                    installCreatedSubject, hcreate] using hkinds
                · simpa [TLB.Coherent, installCreatedSubject] using htlb
              have htransfers' : CapabilityTransfer.WellFormed
                  (installCreatedSubject state subject).transfers := by
                rcases htransfers with ⟨_hendpoints, hpending⟩
                refine ⟨hipc'.2, ?_⟩
                intro endpoint transfer hpendingNew
                have hpendingOld : state.transfers.pending endpoint = some transfer := by
                  simpa [installCreatedSubject] using hpendingNew
                have hold := hpending endpoint transfer hpendingOld
                rw [hcoherent.2.2.2.2.2.2.2.2.2.1] at hold
                rw [hipcCapabilitiesCoherent] at hold
                simpa [installCreatedSubject, hcreate] using hold
              refine ⟨installCreatedSubject_coherent _ _ hcoherent, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_⟩
              · rcases hexecution with ⟨_hexecutionCore, _hbound, hmodeWellFormed⟩
                refine ⟨?_, by simp [installCreatedSubject], ?_⟩
                · simpa [Interrupt.WellFormed, installCreatedSubject, hcreate] using hlifecycle'
                · simpa [installCreatedSubject, hmode] using hmodeWellFormed
              · simpa [installCreatedSubject, hcreate] using hlifecycle'
              · simpa [installCreatedSubject, hcreate] using hcapabilities'
              · exact hvirtual'
              · exact hipc'
              · exact hscheduler'
              · exact hpreemption'
              · exact hresumable'
              · exact htransfers'
              · simpa [installCreatedSubject] using hhalted
              · simp [installCreatedSubject]
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.createSubject subject) hstate hmode

/-- A raw scheduler insertion cannot establish the resumable-context side of
the composite invariant by itself.  If its published post-state is globally
well formed, the inserted subject's saved context must already have been
staged in the pre-state.  This is the precise integration obligation for the
future complete `scheduleAdd` operation-family proof: admission must either
require such a context or atomically construct one. -/
theorem gate_scheduleAdd_accepted_runtimeWellFormed_requires_staged_context
    state subject context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context }) :
    RuntimeWellFormed (gate state (.scheduleAdd subject)).state →
      ∃ saved, saved ∈ state.resumable.contexts ∧ saved.owner = subject := by
  intro hpost
  have hready : subject ∈ next.ready := by
    simp only [Scheduler.add] at haccepted
    split at haccepted <;> try simp_all [Scheduler.reject]
    split at haccepted <;> try simp_all [Scheduler.reject]
    split at haccepted <;> try simp_all [Scheduler.reject]
    next addressSpace haddressSpace =>
      split at haccepted <;> try simp_all [Scheduler.reject]
      split at haccepted <;> try simp_all [Scheduler.reject]
      rcases haccepted with ⟨rfl, rfl⟩
      simp
  have hreadyPublished :
      subject ∈ (gate state (.scheduleAdd subject)).state.resumable.scheduler.ready := by
    simpa [gate, hmode, applyOperation, haccepted, installScheduler,
      installLifecycle] using hready
  rcases hpost with
    ⟨_, _, _, _, _, _, _, _, hresumable, _, _, _⟩
  have hagreement := hresumable.2.2.2.2.2.1.1 subject hreadyPublished
  simpa [gate, hmode, applyOperation, haccepted, installScheduler,
    installLifecycle] using hagreement

theorem dispatchHardware_deterministic state frame first second
    (hfirst : dispatchHardware state frame = first)
    (hsecond : dispatchHardware state frame = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem dispatchHardware_preserves_wellFormed state frame (hstate : WellFormed state) :
    WellFormed (dispatchHardware state frame).state := by
  rcases hstate with ⟨hlifecycle, hbound, hmodeWellFormed⟩
  change SubjectLifecycle.WellFormed state.core.lifecycle at hlifecycle
  cases hmode : state.mode with
  | handling active =>
      simp only [hmode] at hmodeWellFormed
      simpa [dispatchHardware, hmode, halt, WellFormed, Interrupt.WellFormed] using
        And.intro hlifecycle hmodeWellFormed.2
  | halted record =>
      simpa [dispatchHardware, hmode, WellFormed, Interrupt.WellFormed] using
        And.intro hlifecycle (And.intro hbound hmodeWellFormed)
  | running =>
      simp only [hmode] at hmodeWellFormed
      simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
      unfold Interrupt.dispatchHardware
      cases hvector : Interrupt.decodeVector frame.vector with
      | none => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
      | some vector =>
          cases vector with
          | pageFault =>
              cases frame.savedPrivilege with
              | kernel => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
              | user =>
                  simpa [hvector, WellFormed, Interrupt.WellFormed] using
                    SubjectLifecycle.terminateState_preserves_wellFormed
                      state.core.lifecycle state.core.context.currentSubject hlifecycle
          | timer => simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
          | syscall =>
              cases frame.savedPrivilege <;>
                simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle

theorem attacker_registers_cannot_change_dispatch state frame first second :
    dispatch state { hardware := frame, registers := first } =
      dispatch state { hardware := frame, registers := second } := by
  rfl

theorem halted_entry_absorbing state record frame
    (hmode : state.mode = .halted record) :
    dispatchHardware state frame = { state, action := .alreadyHalted record } := by
  simp [dispatchHardware, hmode]

theorem halted_gate_absorbing state record operation
    (hmode : state.execution.mode = .halted record) :
    gate state operation = { state, result := .rejectedHalted record } := by
  simp [gate, hmode]

theorem halted_suffix_absorbing state record proposals
    (hmode : state.execution.mode = .halted record) :
    runOperations state proposals = state := by
  induction proposals generalizing state with
  | nil => rfl
  | cons proposal rest ih =>
      simp only [runOperations]
      rw [halted_gate_absorbing state record proposal hmode]
      exact ih state hmode

/-- Outgoing-return rejection is one atomic composite step: it records the
typed terminal reason, changes no lifecycle/authority/scheduler/resource view,
and absorbs every later typed operation. -/
theorem rejected_user_return_composite_atomicity state request reason proposals
    (hmode : state.execution.mode = .running)
    (harmed : state.execution.returnAuthorityArmed = true)
    (hlive : state.ReturnPlanLive = true)
    (hrejected : Interrupt.validateUserReturn
      (authoritativeReturnRequest state.execution request) = .rejected reason) :
    let record : HaltRecord :=
      { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
        active := none
        incomingVector := request.hardware.vector
        incomingOrigin := request.hardware.savedPrivilege }
    let next := (gate state (.userReturn request)).state
    next.execution.mode = .halted record ∧
      next.execution.core.lifecycle = state.execution.core.lifecycle ∧
      next.scheduler = state.scheduler ∧
      next.preemption = state.preemption ∧
      next.virtualMemory = state.virtualMemory ∧
      next.ipc = state.ipc ∧
      next.capabilities = state.capabilities ∧
      next.lifecycle = state.lifecycle ∧
      runOperations next proposals = next := by
  dsimp only
  have hfatal : (completeUserReturn state.execution request).action =
      .fatal
        { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
          active := none
          incomingVector := request.hardware.vector
          incomingOrigin := request.hardware.savedPrivilege } := by
    simp only [completeUserReturn, hmode, harmed]
    rw [hrejected]
    rfl
  have hterminal :
      ((gate state (.userReturn request)).state.execution.mode =
        .halted
          { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
            active := none
            incomingVector := request.hardware.vector
            incomingOrigin := request.hardware.savedPrivilege }) := by
    simp only [gate, hmode, applyOperation, hlive, if_true, completeUserReturn, harmed]
    rw [hrejected]
    simp [latchInvalidUserReturn, authoritativeReturnRequest]
  refine ⟨hterminal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gate, hmode, applyOperation, hlive, if_true, completeUserReturn, harmed]
    rw [hrejected]
    simp [latchInvalidUserReturn, authoritativeReturnRequest]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · exact halted_suffix_absorbing _ _ proposals hterminal

theorem halted_never_accepts state record operation
    (hmode : state.execution.mode = .halted record) :
    ∀ reply, (gate state operation).result ≠ .completed reply := by
  simp [gate, hmode]

/-- Terminal non-resumption over the complete typed composite step: no
subsystem transition is accepted and no component of the terminal state can
change. -/
theorem halted_terminal_non_resumption state record operation
    (hmode : state.execution.mode = .halted record) :
    (gate state operation).state = state ∧
      ∀ reply, (gate state operation).result ≠ .completed reply := by
  simp [gate, hmode]

theorem fatal_atomicity state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    (dispatchHardware state frame).state.core.lifecycle = state.core.lifecycle := by
  cases hmode : state.mode with
  | handling active => simp [dispatchHardware, hmode, halt]
  | halted record => simp [dispatchHardware, hmode] at hfatal
  | running =>
    simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hfatal ⊢
    generalize hd : Interrupt.dispatchHardware
      { state.core with context := { state.core.context with entryActive := false } }
      frame = outcome at hfatal ⊢
    cases outcome with
    | mk next action => cases action <;> simp_all [activeEntry, hd, halt]

theorem fatal_clears_copy_override state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    (dispatchHardware state frame).state.copyOverride = false := by
  cases hmode : state.mode with
  | handling active => simp [dispatchHardware, hmode, halt]
  | halted record => simp [dispatchHardware, hmode] at hfatal
  | running =>
      simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hfatal ⊢
      generalize hd : Interrupt.dispatchHardware
        { state.core with context := { state.core.context with entryActive := false } }
        frame = outcome at hfatal ⊢
      cases outcome with
      | mk next action => cases action <;> simp_all [activeEntry, hd, halt]

private theorem interrupt_contained_requires_user core frame subject
    (h : (Interrupt.dispatchHardware core frame).action = .contained subject) :
    frame.savedPrivilege = .user := by
  unfold Interrupt.dispatchHardware at h
  split at h <;> simp_all
  cases hv : Interrupt.decodeVector frame.vector with
  | none => simp [hv] at h
  | some vector =>
      cases vector with
      | pageFault => cases hp : frame.savedPrivilege <;> simp_all
      | timer => simp [hv] at h
      | syscall => cases hp : frame.savedPrivilege <;> simp_all

theorem contained_requires_user_origin state frame subject
    (hcontained : (dispatchHardware state frame).action = .contained subject) :
    frame.savedPrivilege = .user := by
  cases hmode : state.mode with
  | handling active => simp [dispatchHardware, hmode, halt] at hcontained
  | halted record => simp [dispatchHardware, hmode] at hcontained
  | running =>
    simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hcontained
    generalize hd : Interrupt.dispatchHardware
      { state.core with context := { state.core.context with entryActive := false } }
      frame = outcome at hcontained
    cases outcome with
    | mk next action =>
      cases action with
      | contained actual =>
          have hh : (Interrupt.dispatchHardware
              { state.core with context := { state.core.context with entryActive := false } }
              frame).action = .contained actual := by rw [hd]
          exact interrupt_contained_requires_user _ _ _ hh
      | fatal reason => simp [activeEntry, hd, halt] at hcontained
      | timer => simp [activeEntry, hd] at hcontained
      | syscall => simp [activeEntry, hd] at hcontained
      | rejected reason => simp [activeEntry, hd] at hcontained

theorem double_fault_escalation state active frame
    (hmode : state.mode = .handling active)
    (hactive : active.vector = 14) (hincoming : frame.vector = 14) :
    (dispatchHardware state frame).action = .fatal .doubleFault := by
  simp [dispatchHardware, hmode, escalation, hactive, hincoming, halt]

theorem kernel_fault_never_contained state frame
    (horigin : frame.savedPrivilege = .kernel) :
    ¬ ∃ subject, (dispatchHardware state frame).action = .contained subject := by
  intro h
  rcases h with ⟨subject, hsubject⟩
  have := contained_requires_user_origin state frame subject hsubject
  simp [horigin] at this

/-- Negative regression: the legacy action-only model leaves the state usable. -/
theorem legacy_fatal_not_absorbing (core : Interrupt.State)
    (hidle : core.context.entryActive = false) (kernelFault syscall : Interrupt.HardwareFrame)
    (hkvector : kernelFault.vector = 14)
    (hkorigin : kernelFault.savedPrivilege = .kernel)
    (hsvector : syscall.vector = 128)
    (_hsvalid : Interrupt.validSavedUserFrame syscall = true) :
    (Interrupt.dispatchHardware core kernelFault).action = .fatal .kernelFault ∧
      (Interrupt.dispatchHardware core syscall).action = .syscall := by
  constructor
  · exact Interrupt.kernel_page_fault_is_fatal core kernelFault hidle hkvector hkorigin
  · have horigin : syscall.savedPrivilege = .user := by
      have hsvalid := _hsvalid
      simp [Interrupt.validSavedUserFrame] at hsvalid
      exact hsvalid.1.1.1.1.1
    simp [Interrupt.dispatchHardware, hidle, hsvector, Interrupt.decodeVector, horigin]

private def demoFrame (vector : Nat) (origin : Interrupt.Privilege) : Interrupt.HardwareFrame :=
  { vector, errorCode := 0, savedPrivilege := origin, instructionPointer := 0x400000,
    stackPointer := 0x500000, codeSelector := 0x23, stackSelector := 0x1b,
    flags := 2, canonicalInstructionPointer := true,
    canonicalStackPointer := true, flagsAllowed := true }

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 14 .kernel)).action =
      .fatal .kernelFault := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector, mapFatal, halt]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 32 .user)).action = .timer := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 14 .user)).action =
      .contained core.context.currentSubject := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 128 .user)).action =
      .syscall := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 77 .user)).action =
      .fatal .unsupportedVector := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector, mapFatal, halt]

example (core : Interrupt.State) :
    let active := activeEntry (demoFrame 14 .kernel)
    (dispatchHardware { core, mode := .handling active } (demoFrame 14 .kernel)).action =
      .fatal .doubleFault := by
  simp [dispatchHardware, activeEntry, demoFrame, escalation, halt]

example (core : Interrupt.State) :
    let active := activeEntry (demoFrame 32 .user)
    (dispatchHardware { core, mode := .handling active } (demoFrame 14 .user)).action =
      .fatal .nestedEntry := by
  simp [dispatchHardware, activeEntry, demoFrame, escalation, halt]

example (state : CompositeState) (record : HaltRecord)
    (hhalted : state.execution.mode = .halted record) :
    (gate state .restart).state = state := by
  simp [gate, hhalted]

example (state : CompositeState) (record : HaltRecord)
    (hhalted : state.execution.mode = .halted record)
    (syscall : Syscall.UntrustedCall) (ipc : IPCSyscall.Call)
    (frame : Interrupt.HardwareFrame) :
    runOperations state [
      .syscall syscall, .preempt frame, .ipc ipc,
      .capabilityRevoke 0 1 0, .unmap 0, .terminateSubject 0] = state := by
  simp [runOperations, gate, hhalted]

end LeanOS.FailStop
