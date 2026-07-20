import LeanOS.Interrupt
import LeanOS.BootPageTablePlan
import LeanOS.IPCSyscall
import LeanOS.BlockingIPC
import LeanOS.BlockingIPCContext
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
  /-- Authoritative blocking endpoint state.  Its scheduler is published back
  to every composite scheduler projection by `publishBlockingIPC`. -/
  blockingIPC : BlockingIPC.State
  /-- Exact suspended contexts paired with the authoritative waiter index.
  This bank is mutated only together with `blockingIPC` through the typed
  `BlockingIPCContext` transition. -/
  blockingContexts : BlockingIPC.SubjectId → Option ResumableContext.Context

/-- The blocking store and all composite scheduler views name one scheduler. -/
def CompositeState.BlockingIPCCoherent (state : CompositeState) : Prop :=
  state.blockingIPC.scheduler = state.scheduler ∧
  state.blockingIPC.scheduler.lifecycle = state.lifecycle

/-- The authoritative typed blocking state assembled from its two stored
projections. -/
def CompositeState.blockingIPCContext (state : CompositeState) :
    BlockingIPCContext.State :=
  { ipc := state.blockingIPC, blocked := state.blockingContexts }

/-- Replacing the scheduler projection preserves a blocking store when every
field observed by waiter validation is unchanged and the replacement scheduler
is itself well formed. -/
private theorem blockingIPC_wellFormed_replaceScheduler
    (ipc : BlockingIPC.State) (scheduler : Scheduler.State)
    (hstate : BlockingIPC.WellFormed ipc)
    (hscheduler : Scheduler.WellFormed scheduler)
    (hcapabilities : scheduler.lifecycle.capabilities =
      ipc.scheduler.lifecycle.capabilities)
    (hrunnable : scheduler.lifecycle.runnable = ipc.scheduler.lifecycle.runnable)
    (hcurrent : scheduler.lifecycle.current = ipc.scheduler.lifecycle.current)
    (howner : scheduler.lifecycle.addressOwner = ipc.scheduler.lifecycle.addressOwner)
    (hready : scheduler.ready = ipc.scheduler.ready) :
    BlockingIPC.WellFormed { ipc with scheduler } := by
  rcases hstate with
    ⟨_hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcapability⟩
  refine ⟨hscheduler, hqueues, ?_, hunique, hindex, ?_, ?_⟩
  · simpa [BlockingIPC.authorizedReceive, Scheduler.ownsAddressSpace,
      hcapabilities, hrunnable, hcurrent, howner, hready] using hwaiters
  · simpa [hcapabilities] using hmailbox
  · simpa [hcapabilities] using hcapability

private theorem blockingIPCContext_wellFormed_replaceScheduler
    (state : CompositeState) (scheduler : Scheduler.State)
    (hstate : BlockingIPCContext.WellFormed state.blockingIPCContext)
    (hscheduler : Scheduler.WellFormed scheduler)
    (hcapabilities : scheduler.lifecycle.capabilities =
      state.blockingIPC.scheduler.lifecycle.capabilities)
    (hrunnable : scheduler.lifecycle.runnable =
      state.blockingIPC.scheduler.lifecycle.runnable)
    (hcurrent : scheduler.lifecycle.current =
      state.blockingIPC.scheduler.lifecycle.current)
    (howner : scheduler.lifecycle.addressOwner =
      state.blockingIPC.scheduler.lifecycle.addressOwner)
    (hready : scheduler.ready = state.blockingIPC.scheduler.ready) :
    BlockingIPCContext.WellFormed
      { ipc := { state.blockingIPC with scheduler }, blocked := state.blockingContexts } := by
  exact ⟨blockingIPC_wellFormed_replaceScheduler state.blockingIPC scheduler hstate.1
    hscheduler hcapabilities hrunnable hcurrent howner hready, hstate.2⟩


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
  (state.execution.returnAuthorityArmed = true → state.ReturnPlanLive = true) ∧
  state.BlockingIPCCoherent

/-- The blocking store observes the same authoritative lifecycle as every
other runtime projection. -/
theorem RuntimeWellFormed.blockingLifecycle {state : CompositeState}
    (hstate : RuntimeWellFormed state) :
    state.blockingIPC.scheduler.lifecycle = state.lifecycle := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
  exact hblocking.2

/-! ## Boot-produced initial runtime -/

private def bootCapabilities : Capability.State :=
  { subjects := fun _ => false
    objects := fun _ => false
    kinds := fun _ => none
    slots := fun _ _ => none }

private def bootLifecycle : SubjectLifecycle.State :=
  { capabilities := bootCapabilities
    issuedSubjects := fun _ => false
    ownedMemory := fun _ => none
    addressOwner := fun _ => none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => false
    runnable := fun _ => false
    current := none }

private def bootMemory : MemoryLifecycle.State :=
  { capabilities := bootCapabilities
    allocator := { frames := [], status := fun _ => .reserved }
    binding := fun _ => none
    issued := fun _ => false }

private def bootVirtualMemory : VirtualMapping.State :=
  { memory := bootMemory
    owner := fun _ => none
    mappings := fun _ _ => none
    issuedAddressSpace := fun _ => false }

private def bootEndpoints : EndpointIPC.State :=
  { capabilities := bootCapabilities
    allocator := bootMemory.allocator
    binding := bootMemory.binding
    issued := bootMemory.issued
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

/-- The bounded state published after the boot page-table compiler succeeds,
before any subject is admitted.  The compiled plan is retained as evidence for
later return selection, but cannot arm a return until authoritative lifecycle,
mapping, scheduler, and resumable-context state has been installed. -/
def bootRuntime (plan : BootPageTablePlan.Plan) : CompositeState :=
  let scheduler : Scheduler.State :=
    { lifecycle := bootLifecycle, ready := [], capacity := 0 }
  let resumable : ResumablePreemption.State :=
    { scheduler
      contexts := []
      capacity := 0
      translations := { virtual := bootVirtualMemory, active := none, entries := [] } }
  { execution :=
      { core :=
          { lifecycle := bootLifecycle
            context :=
              { currentSubject := 0
                activeAddressSpace := 0
                kernelStack := 0
                entryActive := false } }
        mode := .running
        returnPlan := some plan }
    scheduler
    preemption := { scheduler, timerArmed := false, acceptedTicks := 1 }
    virtualMemory := bootVirtualMemory
    ipc := { virtualMemory := bootVirtualMemory, endpoints := bootEndpoints }
    capabilities := bootCapabilities
    lifecycle := bootLifecycle
    resumable
    transfers := { toEndpointState := bootEndpoints, pending := fun _ => none }
    blockingIPC :=
      { scheduler
        mailbox := fun _ => none
        waiters := fun _ => []
        waiterEndpoint := fun _ => none
        waiterCapacity := 0
        completion := fun _ => none }
    blockingContexts := fun _ => none }

/-- A successfully compiled bounded boot plan produces a concrete global
invariant witness.  Boot does not synthesize a live subject or trusted return
identity: those remain disabled until later checked runtime admission. -/
theorem bootRuntime_runtimeWellFormed input plan
    (_hcompiled : BootPageTablePlan.compile input = .ok plan) :
    RuntimeWellFormed (bootRuntime plan) := by
  simp [RuntimeWellFormed, bootRuntime, CompositeState.Coherent, WellFormed,
    Interrupt.WellFormed, SubjectLifecycle.WellFormed, Capability.WellFormed,
    Capability.SlotsWellFormed, Capability.DerivationsWellFormed,
    Capability.LiveIdentitiesUnique, Capability.SlotSpacesWellFormed,
    VirtualMapping.LifecycleWellFormed, VirtualMapping.WellFormed,
    MemoryLifecycle.WellFormed, IPCSyscall.WellFormed, EndpointIPC.WellFormed,
    Scheduler.WellFormed, Preemption.WellFormed, ResumablePreemption.WellFormed,
    ResumablePreemption.ReadyContextAgreement,
    ResumablePreemption.TranslationAgreement, ResumablePreemption.VirtualAgreement,
    ResumablePreemption.ResourceKindAgreement, CapabilityTransfer.WellFormed,
    TLB.Coherent, CompositeState.ReturnPlanLive, bootCapabilities, bootLifecycle,
    bootMemory, bootVirtualMemory, bootEndpoints,
    CompositeState.blockingIPCContext, CompositeState.BlockingIPCCoherent,
    BlockingIPCContext.WellFormed, BlockingIPCContext.ContextAgreement,
    BlockingIPC.WellFormed, BlockingIPC.authorizedReceive]

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
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

private def installCapabilities (state : CompositeState)
    (capabilities : Capability.State) : CompositeState :=
  installLifecycle state { state.lifecycle with capabilities }

/-- Publish monotonic capability delegation without invoking lifecycle cleanup.
Copy preserves every live registry and only adds one slot/derivation, so memory
bindings, mappings, mailboxes, contexts, and translations remain authoritative
and need only observe the new capability store. -/
private def installCopiedCapabilities (state : CompositeState)
    (capabilities : Capability.State) : CompositeState :=
  let lifecycle := { state.lifecycle with capabilities }
  let scheduler := { state.scheduler with lifecycle }
  let virtualMemory := { state.virtualMemory with
    memory := { state.virtualMemory.memory with capabilities } }
  let endpoints := { state.ipc.endpoints with capabilities }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

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
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

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

theorem installCopiedCapabilities_synchronizes_consumers state capabilities :
    let next := installCopiedCapabilities state capabilities
    next.capabilities = capabilities ∧
      next.lifecycle.capabilities = capabilities ∧
      next.execution.core.lifecycle.capabilities = capabilities ∧
      next.virtualMemory.memory.capabilities = capabilities ∧
      next.ipc.endpoints.capabilities = capabilities ∧
      next.scheduler.lifecycle.capabilities = capabilities ∧
      next.preemption.scheduler.lifecycle.capabilities = capabilities ∧
      next.resumable.scheduler.lifecycle.capabilities = capabilities ∧
      next.transfers.capabilities = capabilities := by
  simp [installCopiedCapabilities]

private def installScheduler (state : CompositeState)
    (scheduler : Scheduler.State) : CompositeState :=
  installLifecycle { state with scheduler, preemption := { state.preemption with scheduler } }
    scheduler.lifecycle

/-! ## Authoritative blocking-IPC publication

`BlockingIPC.State` owns the waiter queues, completion reservations, and the
scheduler transition that blocks or wakes a subject.  The older data-only IPC
projection remains present while sealed-transfer composition is migrated, but
it is not used to decide blocking behavior. -/

/-- Strengthened runtime predicate for the authoritative blocking-IPC slice. -/
def BlockingRuntimeWellFormed (state : CompositeState) : Prop :=
  RuntimeWellFormed state ∧
  BlockingIPCContext.WellFormed state.blockingIPCContext

/-- The boot-produced runtime also initializes the authoritative blocking
store with empty waiter/completion indexes over the same scheduler. -/
theorem bootRuntime_blockingRuntimeWellFormed input plan
    (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    BlockingRuntimeWellFormed (bootRuntime plan) := by
  refine ⟨bootRuntime_runtimeWellFormed input plan hcompiled, ?_⟩
  simp [CompositeState.blockingIPCContext, bootRuntime,
    BlockingIPCContext.WellFormed, BlockingIPCContext.ContextAgreement,
    BlockingIPC.WellFormed, Scheduler.WellFormed,
    SubjectLifecycle.WellFormed, Capability.WellFormed,
    Capability.SlotsWellFormed, Capability.DerivationsWellFormed,
    Capability.LiveIdentitiesUnique, Capability.SlotSpacesWellFormed,
    BlockingIPC.authorizedReceive, bootLifecycle, bootCapabilities]

/-- Publish the complete blocking store first, then synchronize its scheduler
and lifecycle to every overlapping composite projection.  Waiters and reserved
completions are copied literally; they are never reconstructed by filtering. -/
def publishBlockingIPC (state : CompositeState)
    (blockingIPC : BlockingIPC.State) : CompositeState :=
  installScheduler { state with blockingIPC } blockingIPC.scheduler

/-- Publish the raw blocking store and its exact saved-context bank in the
same composite mutation.  Scheduler synchronization is deliberately shared
with the established raw publication path. -/
def publishBlockingIPCContext (state : CompositeState)
    (blocking : BlockingIPCContext.State) : CompositeState :=
  let scheduler := blocking.ipc.scheduler
  let lifecycle := scheduler.lifecycle
  let translations :=
    if lifecycle.current.isSome then state.resumable.translations
    else { state.resumable.translations with active := none, entries := [] }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false
      copyOverride := false }
    scheduler
    preemption := { state.preemption with scheduler }
    lifecycle
    resumable := { state.resumable with scheduler, translations }
    blockingIPC := blocking.ipc
    blockingContexts := blocking.blocked }

/-- Publish the blocking half of subject termination without reconstructing
either waiter or saved-context state.  The dependency transition removes the
subject from both projections, and the established publisher synchronizes its
post-termination scheduler through every overlapping composite view. -/
def publishTerminatedBlockingSubject (state : CompositeState)
    (subject : BlockingIPC.SubjectId) : CompositeState :=
  match (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result with
  | .rejected _ => state
  | .accepted =>
      publishBlockingIPCContext state
        (BlockingIPCContext.terminate state.blockingIPCContext subject)

/-- A lifecycle rejection reaches no scheduler, waiter, or context publisher. -/
theorem publishTerminatedBlockingSubject_rejected_unchanged state subject reason
    (hrejected :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .rejected reason) :
    publishTerminatedBlockingSubject state subject = state := by
  simp [publishTerminatedBlockingSubject, hrejected]

/-- Accepted lifecycle termination cannot be published with a stale waiter or
blocked context for the dead identity.  Both absences belong to the same
composite post-state. -/
theorem publishTerminatedBlockingSubject_cleans_self state subject
    (haccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted) :
    (publishTerminatedBlockingSubject state subject).blockingIPC.waiterEndpoint subject = none ∧
      (publishTerminatedBlockingSubject state subject).blockingContexts subject = none := by
  simp only [publishTerminatedBlockingSubject, haccepted]
  change
    (BlockingIPCContext.terminate state.blockingIPCContext subject).ipc.waiterEndpoint subject =
        none ∧
      (BlockingIPCContext.terminate state.blockingIPCContext subject).blocked subject = none
  exact BlockingIPCContext.terminate_accepted_cleans_self
    state.blockingIPCContext subject haccepted

@[simp] theorem publishBlockingIPCContext_context state blocking :
    (publishBlockingIPCContext state blocking).blockingIPCContext = blocking := by
  rfl

@[simp] theorem publishBlockingIPCContext_scheduler state blocking :
    (publishBlockingIPCContext state blocking).scheduler = blocking.ipc.scheduler := by
  rfl

@[simp] theorem publishBlockingIPC_blockingIPC state blockingIPC :
    (publishBlockingIPC state blockingIPC).blockingIPC = blockingIPC := by
  rfl

@[simp] theorem publishBlockingIPC_scheduler state blockingIPC :
    (publishBlockingIPC state blockingIPC).scheduler = blockingIPC.scheduler := by
  rfl

@[simp] theorem publishBlockingIPC_waiters state blockingIPC endpoint :
    (publishBlockingIPC state blockingIPC).blockingIPC.waiters endpoint =
      blockingIPC.waiters endpoint := by
  rfl

@[simp] theorem publishBlockingIPC_waiterEndpoint state blockingIPC subject :
    (publishBlockingIPC state blockingIPC).blockingIPC.waiterEndpoint subject =
      blockingIPC.waiterEndpoint subject := by
  rfl

@[simp] theorem publishBlockingIPC_completion state blockingIPC subject :
    (publishBlockingIPC state blockingIPC).blockingIPC.completion subject =
      blockingIPC.completion subject := by
  rfl

theorem publishBlockingIPC_coherent state blockingIPC :
    (publishBlockingIPC state blockingIPC).BlockingIPCCoherent := by
  simp [CompositeState.BlockingIPCCoherent, publishBlockingIPC,
    installScheduler, installLifecycle]

theorem publishBlockingIPCContext_coherent state blocking :
    (publishBlockingIPCContext state blocking).BlockingIPCCoherent := by
  simp [CompositeState.BlockingIPCCoherent, publishBlockingIPCContext,
    publishBlockingIPC, installScheduler, installLifecycle]

/-- Restore a released blocking context into the authoritative resumable bank
before making its owner visible as ready.  Every check is finite and mirrors
the corresponding `ResumablePreemption.WellFormed` obligation. -/
def publishReleasedBlockingContext (state : CompositeState)
    (blocking : BlockingIPCContext.State) (saved : ResumableContext.Context) :
    Except ResumablePreemption.Error CompositeState :=
  if !Interrupt.validSavedUserFrame saved.frame || saved.addressSpace != saved.owner ||
      saved.kind != .suspended then
    .error .staleDestination
  else if blocking.ipc.scheduler.lifecycle.capabilities.subjects saved.owner != true ||
      blocking.ipc.scheduler.lifecycle.runnable saved.owner != true ||
      blocking.ipc.scheduler.lifecycle.addressOwner saved.addressSpace != some saved.owner ||
      !(saved.owner ∈ blocking.ipc.scheduler.ready) then
    .error .staleDestination
  else if (ResumablePreemption.contextFor state.resumable.contexts saved.owner).isSome then
    .error .duplicateSave
  else if state.resumable.capacity ≤ state.resumable.contexts.length then
    .error .bankFull
  else
    let published := publishBlockingIPCContext state blocking
    .ok { published with resumable := { published.resumable with
      contexts := saved :: state.resumable.contexts } }

theorem publishReleasedBlockingContext_restores_exact state blocking saved next
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    ResumablePreemption.contextFor next.resumable.contexts saved.owner = some saved ∧
      next.blockingIPCContext = blocking := by
  unfold publishReleasedBlockingContext at hpublished
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  simp only [Except.ok.injEq] at hpublished
  subst next
  constructor
  · simp [ResumablePreemption.contextFor]
  · rfl

theorem publishReleasedBlockingContext_blockingCoherent state blocking saved next
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    next.BlockingIPCCoherent := by
  rw [show next.BlockingIPCCoherent =
      (publishBlockingIPCContext state blocking).BlockingIPCCoherent by
    simp only [CompositeState.BlockingIPCCoherent]
    unfold publishReleasedBlockingContext at hpublished
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    simp only [Except.ok.injEq] at hpublished
    subst next
    rfl]
  exact publishBlockingIPCContext_coherent state blocking

/-- A published wake retains the exact reserved envelope and makes the same
receiver runnable in the scheduler observed by the rest of the composite. -/
theorem publishBlockingIPC_wake_coherent state blockingIPC endpoint receiver envelope :
    let next := publishBlockingIPC state
      (BlockingIPC.wakeState blockingIPC endpoint receiver envelope)
    next.blockingIPC.completion receiver = some (.delivered envelope) ∧
      next.scheduler.lifecycle.runnable receiver = true ∧
      next.blockingIPC.scheduler = next.scheduler := by
  simp [BlockingIPC.wake_reserves_exact_envelope,
    BlockingIPC.wake_marks_receiver_runnable]

inductive BlockingIPCCall where
  | receive (handleWord : UInt64)
  | send (handleWord word0 word1 : UInt64)
  deriving DecidableEq, Repr

/-- Finite public observation of a blocking transition.  Receive retains the
dependency's typed `delivered`/`blocked`/rejected result; send distinguishes a
mailbox enqueue from the successful wake of one FIFO receiver. -/
inductive CompositeBlockingIPCReply where
  | receive (result : BlockingIPC.WordReceiveResult)
  | sendHandleRejected (reason : CapabilityHandle.WordResolveDenial)
  | sendRejected (reason : BlockingIPC.Error)
  | sent
  | woke (receiver : BlockingIPC.SubjectId)
  deriving DecidableEq, Repr

structure CompositeBlockingIPCOutcome where
  state : CompositeState
  reply : CompositeBlockingIPCReply

/-- The finite blocking-IPC replies that denote an ordinary, nonfatal
rejection.  Keeping this classifier separate from successful delivery,
blocking, enqueue, and wake replies prevents a generic wrapper from treating a
state-changing success as a rejection (or vice versa). -/
inductive CompositeBlockingIPCRejection : CompositeBlockingIPCReply → Prop
  | receiveHandle reason :
      CompositeBlockingIPCRejection (.receive (.handleRejected reason))
  | receive reason :
      CompositeBlockingIPCRejection (.receive (.completed (.rejected reason)))
  | sendHandle reason :
      CompositeBlockingIPCRejection (.sendHandleRejected reason)
  | send reason :
      CompositeBlockingIPCRejection (.sendRejected reason)

/-- Total authoritative blocking dispatcher.  Caller identity is projected
from the execution latch.  On success the dependency's scheduler is published
atomically with its waiter/completion state; every typed rejection returns the
identical composite state. -/
def dispatchBlockingIPC (state : CompositeState)
    (call : BlockingIPCCall) : CompositeBlockingIPCOutcome :=
  let caller := state.execution.core.context.currentSubject
  match call with
  | .receive handleWord =>
      let outcome := BlockingIPC.receiveOrBlockWord state.blockingIPC caller handleWord
      match outcome.result with
      | .handleRejected reason => { state, reply := .receive (.handleRejected reason) }
      | .completed (.rejected reason) =>
          { state, reply := .receive (.completed (.rejected reason)) }
      | .completed result =>
          { state := publishBlockingIPC state outcome.state
            reply := .receive (.completed result) }
  | .send handleWord word0 word1 =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      let outcome := BlockingIPC.sendWord state.blockingIPC caller handleWord payload
      match outcome.result with
      | .handleRejected reason => { state, reply := .sendHandleRejected reason }
      | .completed (.rejected reason) => { state, reply := .sendRejected reason }
      | .completed .accepted =>
          let reply :=
            match CapabilityHandle.resolveCurrent
                state.blockingIPC.scheduler.lifecycle.capabilities
                { caller } handleWord .endpoint with
            | .error _ => CompositeBlockingIPCReply.sent
            | .ok resolution =>
                match state.blockingIPC.waiters resolution.capability.object with
                | [] => .sent
                | receiver :: _ => .woke receiver
          { state := publishBlockingIPC state outcome.state, reply }

/-- Every ordinary blocking-IPC rejection is globally atomic.  In particular,
the composite boundary does not publish dependency-local cleanup performed
while observing a cancelled completion; callers see the exact pre-state until
a successful operation consumes or replaces that authoritative completion. -/
theorem dispatchBlockingIPC_rejection_atomic state call reply
    (hrejected : CompositeBlockingIPCRejection reply)
    (hreply : (dispatchBlockingIPC state call).reply = reply) :
    (dispatchBlockingIPC state call).state = state := by
  cases call with
  | receive handleWord =>
      cases hresult : (BlockingIPC.receiveOrBlockWord state.blockingIPC
          state.execution.core.context.currentSubject handleWord).result with
      | handleRejected reason => simp [dispatchBlockingIPC, hresult]
      | completed result =>
          cases result with
          | rejected reason => simp [dispatchBlockingIPC, hresult]
          | delivered envelope =>
              cases hrejected <;> simp [dispatchBlockingIPC, hresult] at hreply
          | blocked =>
              cases hrejected <;> simp [dispatchBlockingIPC, hresult] at hreply
  | send handleWord word0 word1 =>
      cases hresult : (BlockingIPC.sendWord state.blockingIPC
          state.execution.core.context.currentSubject handleWord { word0, word1 }).result with
      | handleRejected reason => simp [dispatchBlockingIPC, hresult]
      | completed result =>
          cases result with
          | rejected reason => simp [dispatchBlockingIPC, hresult]
          | accepted =>
              cases hresolve : CapabilityHandle.resolveCurrent
                  state.blockingIPC.scheduler.lifecycle.capabilities
                  { caller := state.execution.core.context.currentSubject }
                  handleWord .endpoint with
              | error reason =>
                  cases hrejected <;>
                    simp [dispatchBlockingIPC, hresult, hresolve] at hreply
              | ok resolution =>
                  cases hwaiters : state.blockingIPC.waiters
                      resolution.capability.object with
                  | nil =>
                      cases hrejected <;>
                        simp [dispatchBlockingIPC, hresult, hresolve, hwaiters] at hreply
                  | cons receiver rest =>
                      cases hrejected <;>
                        simp [dispatchBlockingIPC, hresult, hresolve, hwaiters] at hreply

/-- A dependency-level block is surfaced as `blocked`, and the exact state
containing the waiter registration and scheduler selection is published. -/
theorem dispatchBlockingIPC_blocked_exact state handleWord
    (hblocked : (BlockingIPC.receiveOrBlockWord state.blockingIPC
      state.execution.core.context.currentSubject handleWord).result =
        .completed .blocked) :
    dispatchBlockingIPC state (.receive handleWord) =
      { state := publishBlockingIPC state
          (BlockingIPC.receiveOrBlockWord state.blockingIPC
            state.execution.core.context.currentSubject handleWord).state
        reply := .receive (.completed .blocked) } := by
  simp [dispatchBlockingIPC, hblocked]

/-- An accepted send to a nonempty FIFO queue reports the exact receiver that
the dependency wakes and publishes the matching completion/scheduler state. -/
theorem dispatchBlockingIPC_woke_exact state handleWord word0 word1 resolution receiver rest
    (hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok resolution)
    (hwaiters : state.blockingIPC.waiters resolution.capability.object =
      receiver :: rest)
    (haccepted : (BlockingIPC.sendWord state.blockingIPC
      state.execution.core.context.currentSubject handleWord { word0, word1 }).result =
        .completed .accepted) :
    dispatchBlockingIPC state (.send handleWord word0 word1) =
      { state := publishBlockingIPC state
          (BlockingIPC.sendWord state.blockingIPC
            state.execution.core.context.currentSubject handleWord { word0, word1 }).state
        reply := .woke receiver } := by
  simp [dispatchBlockingIPC, haccepted, hresolve, hwaiters]

/-- Every authoritative blocking transition leaves the blocking scheduler and
the composite scheduler equal, including all typed rejection paths. -/
theorem dispatchBlockingIPC_scheduler_coherent state call
    (hcoherent : state.BlockingIPCCoherent) :
    (dispatchBlockingIPC state call).state.BlockingIPCCoherent := by
  rcases hcoherent with ⟨hscheduler, hlifecycle⟩
  cases call with
  | receive handleWord =>
      cases hresult : (BlockingIPC.receiveOrBlockWord state.blockingIPC
        state.execution.core.context.currentSubject handleWord).result with
      | handleRejected reason =>
          simpa [dispatchBlockingIPC, hresult] using
            (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
      | completed result =>
          cases result with
          | rejected reason =>
              simpa [dispatchBlockingIPC, hresult] using
                (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
          | delivered envelope =>
              simpa [dispatchBlockingIPC, hresult] using
                publishBlockingIPC_coherent state
                  (BlockingIPC.receiveOrBlockWord state.blockingIPC
                    state.execution.core.context.currentSubject handleWord).state
          | blocked =>
              simpa [dispatchBlockingIPC, hresult] using
                publishBlockingIPC_coherent state
                  (BlockingIPC.receiveOrBlockWord state.blockingIPC
                    state.execution.core.context.currentSubject handleWord).state
  | send handleWord word0 word1 =>
      cases hresult : (BlockingIPC.sendWord state.blockingIPC
        state.execution.core.context.currentSubject handleWord { word0, word1 }).result with
      | handleRejected reason =>
          simpa [dispatchBlockingIPC, hresult] using
            (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
      | completed result =>
          cases result with
          | rejected reason =>
              simpa [dispatchBlockingIPC, hresult] using
                (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
          | accepted =>
              simpa [dispatchBlockingIPC, hresult] using
                publishBlockingIPC_coherent state
                  (BlockingIPC.sendWord state.blockingIPC
                    state.execution.core.context.currentSubject handleWord
                    { word0, word1 }).state

/-! ## Context-owning public blocking receive

The legacy dispatcher above records the raw blocking state used by the finite
evidence traces.  The public composite operation below instead crosses the
typed successor: it constructs saved-context identity from the execution
latch, publishes the waiter store and context bank together, and returns a
finite typed reply. -/

inductive CompositeBlockingReceiveReply where
  | handleRejected (reason : CapabilityHandle.WordResolveDenial)
  | contextRejected (reason : BlockingIPCContext.ContextError)
  | rejected (reason : BlockingIPC.Error)
  | switchRequired
  | delivered (envelope : BlockingIPC.Envelope)
  | blocked
  deriving DecidableEq, Repr

structure CompositeBlockingReceiveOutcome where
  state : CompositeState
  reply : CompositeBlockingReceiveReply

/-- General-purpose registers and the hardware frame may carry user data, but
the subject, address-space identity, and context kind are selected solely from
the authoritative execution state. -/
def CompositeState.blockingSavedContext (state : CompositeState)
    (frame : Interrupt.HardwareFrame) (registers : ResumableContext.Registers) :
    ResumableContext.Context :=
  { owner := state.execution.core.context.currentSubject
    addressSpace := state.execution.core.context.activeAddressSpace
    frame
    registers
    kind := .suspended }

@[simp] theorem blockingSavedContext_owner (state : CompositeState) frame registers :
    (state.blockingSavedContext frame registers).owner =
      state.execution.core.context.currentSubject := rfl

@[simp] theorem blockingSavedContext_addressSpace (state : CompositeState) frame registers :
    (state.blockingSavedContext frame registers).addressSpace =
      state.execution.core.context.activeAddressSpace := rfl

/-- Complete a blocking scheduler handoff by consuming the context owned by
the scheduler-selected peer and switching the modeled CR3/TLB projection to
that peer's address space.  The selected identity is read only from the
post-block scheduler; neither the handle word nor the saved registers can
choose it. -/
def restoreBlockingPeer (state : CompositeState)
    (blocking : BlockingIPCContext.State) : Except ResumablePreemption.Error CompositeState :=
  match blocking.ipc.scheduler.lifecycle.current with
  | none => .error .noDestination
  | some selected =>
      match ResumablePreemption.contextFor state.resumable.contexts selected with
      | none => .error .noDestination
      | some destination =>
          if destination.owner != selected || destination.addressSpace != selected ||
              Interrupt.validSavedUserFrame destination.frame != true ||
              blocking.ipc.scheduler.lifecycle.capabilities.subjects destination.owner != true ||
              blocking.ipc.scheduler.lifecycle.runnable destination.owner != true ||
              blocking.ipc.scheduler.lifecycle.addressOwner destination.addressSpace !=
                some destination.owner ||
              state.resumable.translations.virtual.owner destination.addressSpace !=
                some destination.owner then
            .error .staleDestination
          else
            let published := publishBlockingIPCContext state blocking
            .ok { published with
              execution := { published.execution with
                core := { published.execution.core with
                  context := { published.execution.core.context with
                    currentSubject := destination.owner
                    activeAddressSpace := destination.addressSpace } }
                returnAuthorityArmed := false }
              resumable := { published.resumable with
                contexts := ResumablePreemption.eraseContext
                  state.resumable.contexts destination.owner
                translations := TLB.switch state.resumable.translations
                  destination.addressSpace } }

/-- A completed block handoff restores exactly the scheduler-selected peer,
consumes its saved bank entry, and models the required CR3 reload. -/
theorem restoreBlockingPeer_exact state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    ∃ selected destination,
      blocking.ipc.scheduler.lifecycle.current = some selected ∧
      ResumablePreemption.contextFor state.resumable.contexts selected = some destination ∧
      next.execution.core.context.currentSubject = selected ∧
      next.execution.core.context.activeAddressSpace = destination.addressSpace ∧
      next.resumable.translations.active = some destination.addressSpace ∧
      next.resumable.translations.entries = [] ∧
      ResumablePreemption.contextFor next.resumable.contexts selected = none ∧
      next.blockingIPCContext = blocking := by
  simp only [restoreBlockingPeer] at hrestore
  split at hrestore <;> try contradiction
  next selected hselected =>
    split at hrestore <;> try contradiction
    next destination hdestination =>
      split at hrestore <;> try contradiction
      simp only [Except.ok.injEq] at hrestore
      subst next
      have howner : destination.owner = selected := by simp_all
      refine ⟨selected, destination, hselected, hdestination, howner, rfl, ?_, ?_, ?_, rfl⟩
      · simp [TLB.switch]
      · simp [TLB.switch]
      · rw [howner]
        exact ResumablePreemption.contextFor_erase_self _ _

theorem restoreBlockingPeer_context_exact state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    next.blockingIPCContext = blocking := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcontext⟩ :=
    restoreBlockingPeer_exact state blocking next hrestore
  exact hcontext

theorem restoreBlockingPeer_blockingCoherent state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    next.BlockingIPCCoherent := by
  have hcontext := restoreBlockingPeer_context_exact state blocking next hrestore
  rw [show next.BlockingIPCCoherent =
      (publishBlockingIPCContext state blocking).BlockingIPCCoherent by
    simp only [CompositeState.BlockingIPCCoherent]
    unfold restoreBlockingPeer at hrestore
    split at hrestore <;> try contradiction
    split at hrestore <;> try contradiction
    split at hrestore <;> try contradiction
    simp only [Except.ok.injEq] at hrestore
    subst next
    rfl]
  exact publishBlockingIPCContext_coherent state blocking

def dispatchBlockingReceive (state : CompositeState) (handleWord : UInt64)
    (frame : Interrupt.HardwareFrame) (registers : ResumableContext.Registers) :
    CompositeBlockingReceiveOutcome :=
  let caller := state.execution.core.context.currentSubject
  match CapabilityHandle.resolveCurrent state.blockingIPC.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | .error reason => { state, reply := .handleRejected reason }
  | .ok resolution =>
      let outcome := BlockingIPCContext.receiveOrBlock state.blockingIPCContext caller
        resolution.handle.slot (state.blockingSavedContext frame registers)
      match outcome.result with
      | .contextRejected reason => { state, reply := .contextRejected reason }
      | .completed (.rejected reason) => { state, reply := .rejected reason }
      | .completed (.delivered envelope) =>
          { state := publishBlockingIPCContext state outcome.state
            reply := .delivered envelope }
      | .completed .blocked =>
          if outcome.state.ipc.scheduler.lifecycle.current.isSome then
            match restoreBlockingPeer state outcome.state with
            | .error _ => { state, reply := .switchRequired }
            | .ok next => { state := next, reply := .blocked }
          else
            { state := publishBlockingIPCContext state outcome.state
              reply := .blocked }

inductive CompositeBlockingReceiveRejection : CompositeBlockingReceiveReply → Prop
  | handle reason : CompositeBlockingReceiveRejection (.handleRejected reason)
  | context reason : CompositeBlockingReceiveRejection (.contextRejected reason)
  | ipc reason : CompositeBlockingReceiveRejection (.rejected reason)
  | switchRequired : CompositeBlockingReceiveRejection .switchRequired

theorem dispatchBlockingReceive_rejected_atomic state handleWord frame registers reply
    (hrejected : CompositeBlockingReceiveRejection reply)
    (hreply : (dispatchBlockingReceive state handleWord frame registers).reply = reply) :
    (dispatchBlockingReceive state handleWord frame registers).state = state := by
  cases hrejected
  all_goals
    simp only [dispatchBlockingReceive] at hreply ⊢
    split <;> simp_all
    generalize houtcome : BlockingIPCContext.receiveOrBlock _ _ _ _ = outcome at hreply ⊢
    cases outcome with
    | mk next result =>
        cases result with
        | contextRejected reason => simp_all
        | completed result =>
            cases result with
            | delivered envelope => simp_all
            | rejected reason => simp_all
            | blocked =>
                by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                · cases hrestore : restoreBlockingPeer state next <;>
                    simp [hsome, hrestore] at hreply ⊢
                · simp [hsome] at hreply ⊢

theorem dispatchBlockingReceive_preserves_blockingWellFormed state handleWord frame registers
    (hstate : BlockingIPCContext.WellFormed state.blockingIPCContext) :
    BlockingIPCContext.WellFormed
      (dispatchBlockingReceive state handleWord frame registers).state.blockingIPCContext := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simpa [dispatchBlockingReceive, hresolve] using hstate
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      have hpreserved := BlockingIPCContext.receive_preserves_wellFormed
        state.blockingIPCContext state.execution.core.context.currentSubject
        resolution.handle.slot saved hstate
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          have hnext : BlockingIPCContext.WellFormed next := by
            simpa [houtcome] using hpreserved
          cases result with
          | contextRejected reason =>
              simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
          | completed result =>
              cases result with
              | rejected reason =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
              | delivered envelope =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hnext
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using hstate
                    | ok published =>
                        have hcontext := restoreBlockingPeer_context_exact
                          state next published hrestore
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore, hcontext] using hnext
                  · simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome] using hnext

theorem dispatchBlockingReceive_preserves_coherent state handleWord frame registers
    (hstate : state.BlockingIPCCoherent) :
    (dispatchBlockingReceive state handleWord frame registers).state.BlockingIPCCoherent := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simpa [dispatchBlockingReceive, hresolve] using hstate
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
          | completed result =>
              cases result with
              | rejected reason =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
              | delivered envelope =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using
                    publishBlockingIPCContext_coherent state next
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using hstate
                    | ok published =>
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using restoreBlockingPeer_blockingCoherent
                            state next published hrestore
                  · simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome] using
                      publishBlockingIPCContext_coherent state next

/-- Bounded invariant owned by the typed blocking-receive boundary.  Successful
blocking now consumes the selected peer's resumable context atomically; folding
this predicate into `RuntimeWellFormed` still requires every non-IPC lifecycle
and capability publisher to synchronize the blocking projections as well. -/
def BlockingReceiveWellFormed (state : CompositeState) : Prop :=
  BlockingIPCContext.WellFormed state.blockingIPCContext ∧
    state.BlockingIPCCoherent

theorem dispatchBlockingReceive_preserves_wellFormed state handleWord frame registers
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed
      (dispatchBlockingReceive state handleWord frame registers).state := by
  exact ⟨dispatchBlockingReceive_preserves_blockingWellFormed
      state handleWord frame registers hstate.1,
    dispatchBlockingReceive_preserves_coherent
      state handleWord frame registers hstate.2⟩

/-- A published block stores the exact frame/register payload under identities
chosen by the execution latch; no handle word can select another owner or
address space. -/
theorem dispatchBlockingReceive_blocked_uses_kernel_context state handleWord frame registers
    (hblocked : (dispatchBlockingReceive state handleWord frame registers).reply = .blocked) :
    let caller := state.execution.core.context.currentSubject
    let saved := state.blockingSavedContext frame registers
    (dispatchBlockingReceive state handleWord frame registers).state.blockingContexts caller =
        some saved ∧
      saved.owner = caller ∧
      saved.addressSpace = state.execution.core.context.activeAddressSpace := by
  dsimp only
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hblocked
                    | ok published =>
                        have hexact := BlockingIPCContext.receive_blocked_exact
                          state.blockingIPCContext state.execution.core.context.currentSubject
                          resolution.handle.slot saved (by simp [houtcome])
                        have hcontext := restoreBlockingPeer_context_exact
                          state next published hrestore
                        simp only [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore, if_true]
                        refine ⟨?_, rfl, rfl⟩
                        change published.blockingIPCContext.blocked
                          state.execution.core.context.currentSubject = some saved
                        rw [hcontext]
                        simpa [houtcome] using hexact.2
                  · have hexact := BlockingIPCContext.receive_blocked_exact
                      state.blockingIPCContext state.execution.core.context.currentSubject
                      resolution.handle.slot saved (by simp [houtcome])
                    simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                      publishBlockingIPCContext] using hexact.2

/-! ## Context-owning wake and cancellation

The matching send and cancellation boundaries consume the saved context in
the same typed transition that removes the waiter.  Publication therefore
cannot expose a runnable receiver while retaining its blocked-context entry.
-/

inductive CompositeBlockingSendReply where
  | handleRejected (reason : CapabilityHandle.WordResolveDenial)
  | contextRejected (reason : BlockingIPCContext.ContextError)
  | restoreRejected (reason : ResumablePreemption.Error)
  | rejected (reason : BlockingIPC.Error)
  | sent
  | woke (context : ResumableContext.Context)
  deriving DecidableEq, Repr

structure CompositeBlockingSendOutcome where
  state : CompositeState
  reply : CompositeBlockingSendReply

def dispatchBlockingSend (state : CompositeState) (handleWord word0 word1 : UInt64) :
    CompositeBlockingSendOutcome :=
  let caller := state.execution.core.context.currentSubject
  match CapabilityHandle.resolveCurrent state.blockingIPC.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | .error reason => { state, reply := .handleRejected reason }
  | .ok resolution =>
      let outcome := BlockingIPCContext.send state.blockingIPCContext caller
        resolution.handle.slot { word0, word1 }
      match outcome.result with
      | .ipcRejected reason => { state, reply := .rejected reason }
      | .contextRejected reason => { state, reply := .contextRejected reason }
      | .accepted =>
          match outcome.released with
          | none => { state := publishBlockingIPCContext state outcome.state, reply := .sent }
          | some saved =>
              match publishReleasedBlockingContext state outcome.state saved with
              | .error reason => { state, reply := .restoreRejected reason }
              | .ok next => { state := next, reply := .woke saved }

inductive CompositeBlockingSendRejection : CompositeBlockingSendReply -> Prop
  | handle reason : CompositeBlockingSendRejection (.handleRejected reason)
  | context reason : CompositeBlockingSendRejection (.contextRejected reason)
  | restore reason : CompositeBlockingSendRejection (.restoreRejected reason)
  | ipc reason : CompositeBlockingSendRejection (.rejected reason)

theorem dispatchBlockingSend_rejected_atomic state handleWord word0 word1 reply
    (hrejected : CompositeBlockingSendRejection reply)
    (hreply : (dispatchBlockingSend state handleWord word0 word1).reply = reply) :
    (dispatchBlockingSend state handleWord word0 word1).state = state := by
  cases hrejected
  all_goals
    simp only [dispatchBlockingSend] at hreply ⊢
    split <;> simp_all
    generalize houtcome : BlockingIPCContext.send _ _ _ _ = outcome at hreply ⊢
    cases outcome with
    | mk next result released =>
        cases result <;> simp_all
        cases released <;> simp_all
        split <;> simp_all

theorem dispatchBlockingSend_preserves_wellFormed state handleWord word0 word1
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed
      (dispatchBlockingSend state handleWord word0 word1).state := by
  rcases hstate with ⟨hblocking, hcoherent⟩
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason =>
      simpa [dispatchBlockingSend, hresolve] using
        (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      have hpreserved := BlockingIPCContext.send_preserves_wellFormed
        state.blockingIPCContext state.execution.core.context.currentSubject
        resolution.handle.slot payload hblocking
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk next result released =>
          have hnext : BlockingIPCContext.WellFormed next := by
            simpa [houtcome] using hpreserved
          cases result with
          | ipcRejected reason =>
              simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
          | contextRejected reason =>
              simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
          | accepted =>
              cases released with
              | none =>
                  exact ⟨by simpa [dispatchBlockingSend, hresolve, payload, houtcome] using hnext,
                    by simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                      publishBlockingIPCContext_coherent state next⟩
              | some saved =>
                  cases hrestore : publishReleasedBlockingContext state next saved with
                  | error reason =>
                      simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] using
                        (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
                  | ok published =>
                      exact ⟨by
                          have hcontext :=
                            (publishReleasedBlockingContext_restores_exact state next saved
                              published hrestore).2
                          simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore,
                            hcontext] using hnext,
                        by simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] using
                          publishReleasedBlockingContext_blockingCoherent
                            state next saved published hrestore⟩

/-- A composite wake publishes the exact context consumed from the blocked
bank and clears that receiver's entry atomically. -/
theorem dispatchBlockingSend_woke_exact state handleWord word0 word1 saved
    (hstate : BlockingReceiveWellFormed state)
    (hwoke : (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved) :
    ∃ receiver,
      state.blockingContexts receiver = some saved ∧
      (dispatchBlockingSend state handleWord word0 word1).state.blockingContexts receiver = none ∧
      ResumablePreemption.contextFor
        (dispatchBlockingSend state handleWord word0 word1).state.resumable.contexts receiver =
          some saved := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hwoke
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk next result released =>
          cases result with
          | ipcRejected reason => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | accepted =>
              cases released with
              | none => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
              | some actual =>
                  cases hrestore : publishReleasedBlockingContext state next actual with
                  | error reason =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                  | ok published =>
                    simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                    subst actual
                    obtain ⟨endpoint, receiver, rest, _, _, hstored, _, hcleared⟩ :=
                      BlockingIPCContext.send_released_exact state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot payload saved
                        (by simp [houtcome])
                    have hcontext :=
                      (publishReleasedBlockingContext_restores_exact state next saved
                        published hrestore)
                    refine ⟨receiver, hstored, ?_, ?_⟩
                    · simp only [dispatchBlockingSend, hresolve, payload, houtcome, hrestore]
                      change published.blockingIPCContext.blocked receiver = none
                      rw [hcontext.2]
                      simpa [houtcome] using hcleared
                    · have howner : saved.owner = receiver := by
                        exact BlockingIPCContext.validSaved_owner receiver saved
                          (hstate.1.2.2 receiver saved hstored)
                      simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore,
                        howner] using hcontext.1

inductive CompositeBlockingCancelReply where
  | notWaiting
  | contextRejected (reason : BlockingIPCContext.ContextError)
  | restoreRejected (reason : ResumablePreemption.Error)
  | rejected (reason : BlockingIPC.Error)
  | cancelled (context : ResumableContext.Context)
  deriving DecidableEq, Repr

structure CompositeBlockingCancelOutcome where
  state : CompositeState
  reply : CompositeBlockingCancelReply

def dispatchBlockingCancel (state : CompositeState) (subject : BlockingIPC.SubjectId) :
    CompositeBlockingCancelOutcome :=
  let outcome := BlockingIPCContext.cancel state.blockingIPCContext subject
  match outcome.result with
  | .notWaiting => { state, reply := .notWaiting }
  | .ipcRejected reason => { state, reply := .rejected reason }
  | .contextRejected reason => { state, reply := .contextRejected reason }
  | .cancelled =>
      match outcome.released with
      | none => { state, reply := .contextRejected .missingSaved }
      | some saved =>
          match publishReleasedBlockingContext state outcome.state saved with
          | .error reason => { state, reply := .restoreRejected reason }
          | .ok next => { state := next, reply := .cancelled saved }

inductive CompositeBlockingCancelRejection : CompositeBlockingCancelReply -> Prop
  | notWaiting : CompositeBlockingCancelRejection .notWaiting
  | context reason : CompositeBlockingCancelRejection (.contextRejected reason)
  | restore reason : CompositeBlockingCancelRejection (.restoreRejected reason)
  | ipc reason : CompositeBlockingCancelRejection (.rejected reason)

theorem dispatchBlockingCancel_rejected_atomic state subject reply
    (hrejected : CompositeBlockingCancelRejection reply)
    (hreply : (dispatchBlockingCancel state subject).reply = reply) :
    (dispatchBlockingCancel state subject).state = state := by
  cases hrejected
  all_goals
    simp only [dispatchBlockingCancel] at hreply ⊢
    generalize houtcome : BlockingIPCContext.cancel _ _ = outcome at hreply ⊢
    cases outcome with
    | mk next result released =>
        cases result <;> simp_all
        cases released <;> simp_all
        split <;> simp_all

theorem dispatchBlockingCancel_preserves_wellFormed state subject
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed (dispatchBlockingCancel state subject).state := by
  rcases hstate with ⟨hblocking, hcoherent⟩
  have hpreserved := BlockingIPCContext.cancel_preserves_wellFormed
    state.blockingIPCContext subject hblocking
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk next result released =>
      have hnext : BlockingIPCContext.WellFormed next := by simpa [houtcome] using hpreserved
      cases result with
      | notWaiting =>
          simpa [dispatchBlockingCancel, houtcome] using
            (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
      | ipcRejected reason =>
          simpa [dispatchBlockingCancel, houtcome] using
            (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
      | contextRejected reason =>
          simpa [dispatchBlockingCancel, houtcome] using
            (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
      | cancelled =>
          cases released with
          | none =>
              simpa [dispatchBlockingCancel, houtcome] using
                (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
          | some saved =>
              cases hrestore : publishReleasedBlockingContext state next saved with
              | error reason =>
                  simpa [dispatchBlockingCancel, houtcome, hrestore] using
                    (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
              | ok published =>
                  have hcontext :=
                    (publishReleasedBlockingContext_restores_exact state next saved
                      published hrestore).2
                  exact ⟨by simpa [dispatchBlockingCancel, houtcome, hrestore, hcontext] using hnext,
                    by simpa [dispatchBlockingCancel, houtcome, hrestore] using
                      publishReleasedBlockingContext_blockingCoherent
                        state next saved published hrestore⟩

theorem dispatchBlockingCancel_cancelled_exact state subject saved
    (hstate : BlockingReceiveWellFormed state)
    (hcancelled : (dispatchBlockingCancel state subject).reply = .cancelled saved) :
    state.blockingContexts subject = some saved ∧
      (dispatchBlockingCancel state subject).state.blockingContexts subject = none ∧
      ResumablePreemption.contextFor
        (dispatchBlockingCancel state subject).state.resumable.contexts subject = some saved := by
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk next result released =>
      cases result with
      | notWaiting => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | ipcRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | contextRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | cancelled =>
          cases released with
          | none => simp [dispatchBlockingCancel, houtcome] at hcancelled
          | some actual =>
              cases hrestore : publishReleasedBlockingContext state next actual with
              | error reason =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
              | ok published =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
                  subst actual
                  have hexact := BlockingIPCContext.cancel_cancelled_exact
                    state.blockingIPCContext subject saved (by simp [houtcome]) (by simp [houtcome])
                  have hcontext := publishReleasedBlockingContext_restores_exact
                    state next saved published hrestore
                  have howner : saved.owner = subject := by
                    exact BlockingIPCContext.validSaved_owner subject saved
                      (hstate.1.2.2 subject saved hexact.1)
                  refine ⟨hexact.1, ?_, ?_⟩
                  · simp only [dispatchBlockingCancel, houtcome, hrestore]
                    change published.blockingIPCContext.blocked subject = none
                    rw [hcontext.2]
                    simpa [houtcome] using hexact.2
                  · simpa [dispatchBlockingCancel, houtcome, hrestore, howner] using hcontext.1

/-! ## Execution-latched typed blocking gate -/

inductive CompositeBlockingOperation where
  | receive (handleWord : UInt64) (frame : Interrupt.HardwareFrame)
      (registers : ResumableContext.Registers)
  | send (handleWord word0 word1 : UInt64)
  | cancel (subject : BlockingIPC.SubjectId)
  deriving DecidableEq, Repr

inductive CompositeBlockingOperationReply where
  | receive (reply : CompositeBlockingReceiveReply)
  | send (reply : CompositeBlockingSendReply)
  | cancel (reply : CompositeBlockingCancelReply)
  deriving DecidableEq, Repr

inductive CompositeBlockingGateResult where
  | completed (reply : CompositeBlockingOperationReply)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure CompositeBlockingGateOutcome where
  state : CompositeState
  result : CompositeBlockingGateResult

/-- The finite blocking-gate results that denote an ordinary nonfatal denial.
Fatal absorption remains a distinct terminal result; successful delivery,
blocking, enqueue, wake, and cancellation are intentionally not classified as
rejections. -/
inductive CompositeBlockingGateRejection : CompositeBlockingGateResult → Prop where
  | busy : CompositeBlockingGateRejection .rejectedBusy
  | receive {reply} (hrejected : CompositeBlockingReceiveRejection reply) :
      CompositeBlockingGateRejection (.completed (.receive reply))
  | send {reply} (hrejected : CompositeBlockingSendRejection reply) :
      CompositeBlockingGateRejection (.completed (.send reply))
  | cancel {reply} (hrejected : CompositeBlockingCancelRejection reply) :
      CompositeBlockingGateRejection (.completed (.cancel reply))

/-- Exact composite post-state selected by one typed blocking operation.  This
is public so a refinement layer cannot pair a successful blocking reply with a
caller-selected or dependency-local post-state. -/
def applyBlockingOperation (state : CompositeState) : CompositeBlockingOperation → CompositeState
  | .receive handleWord frame registers =>
      (dispatchBlockingReceive state handleWord frame registers).state
  | .send handleWord word0 word1 =>
      (dispatchBlockingSend state handleWord word0 word1).state
  | .cancel subject =>
      (dispatchBlockingCancel state subject).state

/-- Exact typed observation selected by one blocking operation.  Successful
delivery, blocking, enqueue, wake, and cancellation remain distinguishable
from every finite dependency-local rejection. -/
def blockingOperationReply (state : CompositeState) :
    CompositeBlockingOperation → CompositeBlockingOperationReply
  | .receive handleWord frame registers =>
      .receive (dispatchBlockingReceive state handleWord frame registers).reply
  | .send handleWord word0 word1 =>
      .send (dispatchBlockingSend state handleWord word0 word1).reply
  | .cancel subject =>
      .cancel (dispatchBlockingCancel state subject).reply

/-- Total typed blocking gate under the same irreversible execution latch as
the ordinary composite gate.  No operation input carries caller identity,
address-space identity, or a saved-context owner. -/
def blockingGate (state : CompositeState) (operation : CompositeBlockingOperation) :
    CompositeBlockingGateOutcome :=
  match state.execution.mode with
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }
  | .running =>
      { state := applyBlockingOperation state operation
        result := .completed (blockingOperationReply state operation) }

theorem blockingGate_running_exact state operation
    (hmode : state.execution.mode = .running) :
    blockingGate state operation =
      { state := applyBlockingOperation state operation
        result := .completed (blockingOperationReply state operation) } := by
  simp [blockingGate, hmode]

/-- A completed blocking result proves that the execution latch was running
and fixes both the exact typed dependency reply and exact composite post-state.
Thus an IPC/context/scheduler rejection cannot be relabeled as a successful
block, delivery, wake, or cancellation. -/
theorem blockingGate_completed_sound state operation reply
    (hcompleted : (blockingGate state operation).result = .completed reply) :
    state.execution.mode = .running ∧
      reply = blockingOperationReply state operation ∧
      (blockingGate state operation).state = applyBlockingOperation state operation := by
  cases hmode : state.execution.mode with
  | running => simp [blockingGate, hmode] at hcompleted ⊢; simp [blockingGate, hmode, hcompleted]
  | handling active => simp [blockingGate, hmode] at hcompleted
  | halted record => simp [blockingGate, hmode] at hcompleted

theorem blockingGate_mode_rejection_atomic state operation
    (hrejected : (blockingGate state operation).result = .rejectedBusy ∨
      ∃ record, (blockingGate state operation).result = .rejectedHalted record) :
    (blockingGate state operation).state = state := by
  cases hmode : state.execution.mode with
  | running =>
      cases operation <;> simp [blockingGate, hmode] at hrejected
  | handling entry => simp [blockingGate, hmode]
  | halted record => simp [blockingGate, hmode]

/-- Every ordinary blocking-gate rejection is globally atomic.  This theorem
classifies denial at the outer typed gate rather than relying on a caller to
recognize dependency-local replies; consequently a stale handle, invalid
saved-context transition, unavailable peer switch, restore failure, IPC
denial, empty cancellation, or busy latch all return the identical composite
state. -/
theorem blockingGate_rejection_atomic state operation
    (hrejected : CompositeBlockingGateRejection (blockingGate state operation).result) :
    (blockingGate state operation).state = state := by
  cases hmode : state.execution.mode with
  | handling entry => simp [blockingGate, hmode]
  | halted record =>
      simp only [blockingGate, hmode] at hrejected
      cases hrejected
  | running =>
      cases operation with
      | receive handleWord frame registers =>
          cases houtcome : dispatchBlockingReceive state handleWord frame registers with
          | mk next reply =>
              simp only [blockingGate, hmode, applyBlockingOperation,
                blockingOperationReply, houtcome] at hrejected ⊢
              cases hrejected with
              | receive hreply =>
                  have hatomic := dispatchBlockingReceive_rejected_atomic
                    state handleWord frame registers reply hreply (by simp [houtcome])
                  simpa [houtcome] using hatomic
      | send handleWord word0 word1 =>
          cases houtcome : dispatchBlockingSend state handleWord word0 word1 with
          | mk next reply =>
              simp only [blockingGate, hmode, applyBlockingOperation,
                blockingOperationReply, houtcome] at hrejected ⊢
              cases hrejected with
              | send hreply =>
                  have hatomic := dispatchBlockingSend_rejected_atomic
                    state handleWord word0 word1 reply hreply (by simp [houtcome])
                  simpa [houtcome] using hatomic
      | cancel subject =>
          cases houtcome : dispatchBlockingCancel state subject with
          | mk next reply =>
              simp only [blockingGate, hmode, applyBlockingOperation,
                blockingOperationReply, houtcome] at hrejected ⊢
              cases hrejected with
              | cancel hreply =>
                  have hatomic := dispatchBlockingCancel_rejected_atomic
                    state subject reply hreply (by simp [houtcome])
                  simpa [houtcome] using hatomic

/-- Every block, wake, cancel, typed rejection, and latch rejection preserves
the authoritative waiter/context agreement and its scheduler projection. -/
theorem blockingGate_preserves_wellFormed state operation
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed (blockingGate state operation).state := by
  cases hmode : state.execution.mode with
  | handling entry => simpa [blockingGate, hmode] using hstate
  | halted record => simpa [blockingGate, hmode] using hstate
  | running =>
      cases operation with
      | receive handleWord frame registers =>
          simpa [blockingGate, hmode, applyBlockingOperation] using
            dispatchBlockingReceive_preserves_wellFormed
              state handleWord frame registers hstate
      | send handleWord word0 word1 =>
          simpa [blockingGate, hmode, applyBlockingOperation] using
            dispatchBlockingSend_preserves_wellFormed
              state handleWord word0 word1 hstate
      | cancel subject =>
          simpa [blockingGate, hmode, applyBlockingOperation] using
            dispatchBlockingCancel_preserves_wellFormed state subject hstate

/-- Publish a queue-only admission without invoking lifecycle cleanup.  An
accepted `Scheduler.add` retains the lifecycle exactly, so the only consumers
that must observe the new ready queue are the scheduler, legacy preemption,
and authoritative resumable-context bank. -/
private def installSchedulerAdmission (state : CompositeState)
    (scheduler : Scheduler.State) : CompositeState :=
  { state with
    scheduler
    preemption := { state.preemption with scheduler }
    resumable := { state.resumable with scheduler }
    blockingIPC := { state.blockingIPC with scheduler } }

/-- Admit a runnable subject only when its kernel-owned initial context is
already staged.  The raw scheduler owns queue policy; this composite wrapper
owns the additional context-bank obligation needed by `RuntimeWellFormed`. -/
private def schedulerAdmission (state : CompositeState)
    (subject : Scheduler.SubjectId) : Scheduler.Outcome :=
  match Scheduler.add state.scheduler subject with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { state := scheduler, result := .accepted context } =>
      match ResumablePreemption.contextFor state.resumable.contexts subject with
      | none => Scheduler.reject state.scheduler .noResumableContext
      | some _ => { state := scheduler, result := .accepted context }

/-- Raw scheduler selection has no context-restore payload.  Empty selection
is a genuine no-op success, but selecting a subject must be performed through
the resumable switch operation that consumes its kernel-owned context. -/
private def schedulerDispatch (state : CompositeState) : Scheduler.Outcome :=
  match Scheduler.selectNext state.scheduler with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { state := scheduler, result := .accepted none } =>
      { state := scheduler, result := .accepted none }
  | { result := .accepted (some _), .. } =>
      Scheduler.reject state.scheduler .noResumableContext

/-- Voluntary yield cannot cross the composite boundary without an outgoing
register/frame payload.  The resumable preemption operation owns that atomic
save/select/restore step. -/
private def schedulerYield (state : CompositeState) : Scheduler.Outcome :=
  match Scheduler.yield state.scheduler with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { result := .accepted _, .. } =>
      Scheduler.reject state.scheduler .noResumableContext

/-- A raw tick has the same missing-save obligation as raw yield. -/
private def schedulerTick (state : CompositeState) : Scheduler.Outcome :=
  match Scheduler.tick state.scheduler with
  | { result := .rejected reason, .. } => Scheduler.reject state.scheduler reason
  | { result := .accepted _, .. } =>
      Scheduler.reject state.scheduler .noResumableContext

theorem schedulerDispatch_rejected_unchanged state reason
    (hrejected : (schedulerDispatch state).result = .rejected reason) :
    (schedulerDispatch state).state = state.scheduler := by
  unfold schedulerDispatch at hrejected ⊢
  generalize hselect : Scheduler.selectNext state.scheduler = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected actual => simp [Scheduler.reject]
      | accepted context =>
          cases context with
          | none => simp at hrejected
          | some selected => simp [Scheduler.reject]

theorem schedulerDispatch_accepted_none_unchanged state
    (haccepted : (schedulerDispatch state).result = .accepted none) :
    (schedulerDispatch state).state = state.scheduler := by
  unfold schedulerDispatch at haccepted ⊢
  generalize hselect : Scheduler.selectNext state.scheduler = outcome at haccepted ⊢
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason => simp [Scheduler.reject] at haccepted
      | accepted context =>
          cases context with
          | some selected => simp [Scheduler.reject] at haccepted
          | none =>
              have hraw : scheduler = state.scheduler := by
                simp only [Scheduler.selectNext] at hselect
                split at hselect <;> simp_all [Scheduler.reject]
                next => split at hselect <;> simp_all [Scheduler.reject]
              exact hraw

theorem schedulerDispatch_accepted_is_none state context
    (haccepted : (schedulerDispatch state).result = .accepted context) :
    context = none := by
  unfold schedulerDispatch at haccepted
  generalize hselect : Scheduler.selectNext state.scheduler = outcome at haccepted
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason => simp [Scheduler.reject] at haccepted
      | accepted actual => cases actual <;> simp_all [Scheduler.reject]

theorem schedulerYield_rejected_unchanged state reason
    (hrejected : (schedulerYield state).result = .rejected reason) :
    (schedulerYield state).state = state.scheduler := by
  unfold schedulerYield at hrejected ⊢
  generalize hyield : Scheduler.yield state.scheduler = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerYield_ne_accepted state context :
    (schedulerYield state).result ≠ .accepted context := by
  unfold schedulerYield
  generalize hyield : Scheduler.yield state.scheduler = outcome
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerTick_rejected_unchanged state reason
    (hrejected : (schedulerTick state).result = .rejected reason) :
    (schedulerTick state).state = state.scheduler := by
  unfold schedulerTick at hrejected ⊢
  generalize htick : Scheduler.tick state.scheduler = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerTick_ne_accepted state context :
    (schedulerTick state).result ≠ .accepted context := by
  unfold schedulerTick
  generalize htick : Scheduler.tick state.scheduler = outcome
  cases outcome with
  | mk scheduler result => cases result <;> simp [Scheduler.reject]

theorem schedulerAdmission_rejected_unchanged state subject reason
    (hrejected : (schedulerAdmission state subject).result = .rejected reason) :
    (schedulerAdmission state subject).state = state.scheduler := by
  unfold schedulerAdmission at hrejected ⊢
  generalize hadd : Scheduler.add state.scheduler subject = outcome at hrejected ⊢
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected actual => simp [Scheduler.reject]
      | accepted context =>
          cases hcontext : ResumablePreemption.contextFor
              state.resumable.contexts subject <;>
            simp_all [Scheduler.reject]

theorem schedulerAdmission_accepted_exact state subject context next
    (haccepted : schedulerAdmission state subject =
      { state := next, result := .accepted context }) :
    Scheduler.add state.scheduler subject =
        { state := next, result := .accepted context } ∧
      ∃ saved, saved ∈ state.resumable.contexts ∧ saved.owner = subject := by
  unfold schedulerAdmission at haccepted
  generalize hadd : Scheduler.add state.scheduler subject = outcome at haccepted
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason => simp [Scheduler.reject] at haccepted
      | accepted actual =>
          cases hcontext : ResumablePreemption.contextFor
              state.resumable.contexts subject with
          | none => simp [hcontext, Scheduler.reject] at haccepted
          | some saved =>
              simp only [hcontext] at haccepted
              injection haccepted with hnext hresult
              subst next
              cases hresult
              refine ⟨rfl, saved, ?_, ?_⟩
              · exact List.mem_of_find?_eq_some hcontext
              · exact ResumablePreemption.contextFor_owner
                  state.resumable.contexts subject saved hcontext

theorem schedulerAdmission_eq_add_of_staged state subject saved
    (hsaved : saved ∈ state.resumable.contexts ∧ saved.owner = subject) :
    schedulerAdmission state subject = Scheduler.add state.scheduler subject := by
  have hsome : ResumablePreemption.contextFor state.resumable.contexts subject ≠ none := by
    intro hnone
    rw [ResumablePreemption.contextFor, List.find?_eq_none] at hnone
    exact hnone saved hsaved.1 (by simp [hsaved.2])
  unfold schedulerAdmission
  generalize hadd : Scheduler.add state.scheduler subject = outcome
  cases outcome with
  | mk scheduler result =>
      cases result with
      | rejected reason =>
          have hstate := Scheduler.add_rejected_unchanged state.scheduler subject reason
            (by simp [hadd])
          have hscheduler : scheduler = state.scheduler := by
            rw [← hstate, hadd]
          simp [hadd, hscheduler, Scheduler.reject]
      | accepted context =>
          cases hcontext : ResumablePreemption.contextFor
              state.resumable.contexts subject with
          | none => exact False.elim (hsome hcontext)
          | some actual => simp [hadd, hcontext]

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
  let lifecycle := resumable.scheduler.lifecycle
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  let virtualMemory := resumable.translations.virtual
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler := resumable.scheduler
    preemption := { state.preemption with scheduler := resumable.scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable
    blockingIPC := { state.blockingIPC with scheduler := resumable.scheduler } }

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
    resumable
    blockingIPC := { state.blockingIPC with scheduler := resumable.scheduler } }

/-- Publish the exact #71 capability/mailbox state through every consumer of
the shared capability registry.  Pending sealed descendants and their trace
remain owned solely by `CapabilityTransfer.State`. -/
private def installTransfers (state : CompositeState)
    (transfers : CapabilityTransfer.State) : CompositeState :=
  let capabilities := transfers.capabilities
  let lifecycle := { state.lifecycle with capabilities }
  let scheduler := { state.scheduler with lifecycle }
  let virtualMemory := { state.virtualMemory with
    memory := { state.virtualMemory.memory with capabilities } }
  let endpoints := transfers.toEndpointState
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers
    blockingIPC := { state.blockingIPC with scheduler } }

/-- Publish authoritative subject cleanup and discard every sealed transfer
that could retain a retired sender, endpoint, or carried object.  The final
`installTransfers` call republishes the canceled mailbox together with the
empty in-flight store, so IPC and transfer consumers cannot drift. -/
private def installTerminatedResumable (state : CompositeState)
    (resumable : ResumablePreemption.State) : CompositeState :=
  let lifecycle := resumable.scheduler.lifecycle
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  let endpoints := { state.ipc.endpoints with
    capabilities := lifecycle.capabilities
    mailbox := restrictMailboxes lifecycle state.ipc.endpoints.mailbox }
  let transfers := CapabilityTransfer.cancelAllOffers
    { state.transfers with toEndpointState := endpoints }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler := resumable.scheduler
    preemption := { state.preemption with scheduler := resumable.scheduler }
    virtualMemory := resumable.translations.virtual
    ipc := { state.ipc with
      virtualMemory := resumable.translations.virtual
      endpoints := transfers.toEndpointState }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable
    transfers
    blockingIPC := { state.blockingIPC with scheduler := resumable.scheduler } }

/-- Publish one explicit subject termination through both authoritative cleanup
stores.  The blocking transition runs against the live pre-state, so it can
remove the exact waiter/context pair before the resumable/resource publisher
installs the same terminated lifecycle everywhere else. -/
private def installTerminatedSubject (state : CompositeState)
    (subject : BlockingIPC.SubjectId)
    (resumable : ResumablePreemption.State) : CompositeState :=
  installTerminatedResumable (publishTerminatedBlockingSubject state subject) resumable

/-- Publish interrupt-driven subject cleanup through the same authoritative
resumable/resource path as explicit termination, then close the kernel copy
window as required by every completed inbound entry. -/
private def publishInterruptCleanup (state : CompositeState)
    (subject : Interrupt.SubjectId) : CompositeState :=
  let cleaned := installTerminatedResumable state
    (ResumablePreemption.cleanupSubject state.resumable subject)
  { cleaned with execution := { cleaned.execution with copyOverride := false } }

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
      translations := { translations with virtual := virtualMemory } }
    blockingIPC := { state.blockingIPC with scheduler } }

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
    rw [hresumableSchedulerCoherent, hschedulerCoherent] at hvalid habsent htranslation
    rw [hresumableSchedulerCoherent] at hagreement
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
  · simp [installVirtualMemory, CompositeState.BlockingIPCCoherent,
      hlive.2.1, hlive.2.2, hschedulerCoherent]

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

/-- Total classification of ordinary, nonfatal composite rejections.  This is
defined on the public reply itself, so a refinement boundary can decide the
class without manufacturing an operation-specific proof witness.  Entry and
user-return failures are excluded: they are transactional or fatal results,
not state-preserving subsystem rejections. -/
def OperationReply.isNonfatalRejection : OperationReply → Bool
  | .syscall (.rejected _) => true
  | .ipc (.syscall (.sendHandleRejected _)) => true
  | .ipc (.syscall (.sendRejected _)) => true
  | .ipc (.syscall (.receiveHandleRejected _)) => true
  | .ipc (.syscall (.receiveRejected _)) => true
  | .ipc .sealedTransferPending => true
  | .resume _ (some .fatalEntry) => false
  | .resume _ (some _) => true
  | .transferOffer (.rejected _) => true
  | .transferAccept (.rejected _) _ => true
  | .capability (.rejected _) => true
  | .map (.rejected _) => true
  | .unmap (.rejected _) => true
  | .createSubject (.rejected _) => true
  | .terminateSubject (.rejected _) => true
  | .scheduleRemove (.rejected _) => true
  | .scheduler (.rejected _) => true
  | _ => false

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

/-- Public observation of IPC after the composite sealed-transfer guard and
authoritative caller/address-space projection have been applied. -/
def authoritativeIPCReply (state : CompositeState) (call : IPCSyscall.Call) :
    CompositeIPCReply :=
  (dispatchIPC state call).reply

/-- Exact composite post-state selected by one typed operation.  This is public
so refinement layers can state that their adapter agrees with the gate. -/
def applyOperation (state : CompositeState) : Operation → CompositeState
  | .interrupt frame =>
      let entry := dispatchHardware state.execution frame
      match entry.action with
      | .contained subject => publishInterruptCleanup state subject
      | .fatal _ =>
          installResumable { state with execution := entry.state }
            { state.resumable with halted := true }
      | .timer | .syscall | .rejected _ => { state with execution := entry.state }
      | .alreadyHalted _ => state
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
      match outcome.error with
      | some .fatalEntry =>
          if outcome.state.halted then
            let entry := dispatchHardware state.execution frame
            installResumable { state with execution := entry.state } outcome.state
          else state
      | some _ => state
      | none => installResumable state outcome.state
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
      | .accepted => installCopiedCapabilities state outcome.state
  | .capabilityRevoke authoritySlot victim victimSlot =>
      let outcome := Capability.revokeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCopiedCapabilities state outcome.state
  | .capabilityRevokeSubtree authoritySlot victim victimSlot =>
      let outcome := Capability.revokeSubtreeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      match outcome.result with
      | .rejected _ => state
      | .accepted => installCopiedCapabilities state outcome.state
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
      | .accepted =>
          installTerminatedSubject state subject
            (ResumablePreemption.cleanupSubject state.resumable subject)
  | .scheduleAdd subject =>
      let outcome := schedulerAdmission state subject
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installSchedulerAdmission state outcome.state
  | .scheduleRemove subject =>
      let outcome := ResumablePreemption.remove state.resumable subject
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installSchedulerRemoval state outcome.state
  | .scheduleNext =>
      let outcome := schedulerDispatch state
      match outcome.result with
      | .rejected _ => state
      | .accepted none => state
      | .accepted (some _) => installScheduler state outcome.state
  | .scheduleYield =>
      let outcome := schedulerYield state
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .scheduleTick =>
      let outcome := schedulerTick state
      match outcome.result with
      | .rejected _ => state
      | .accepted _ => installScheduler state outcome.state
  | .terminateCurrent =>
      let outcome := Scheduler.terminateCurrent state.scheduler
      match outcome.result with
      | .rejected _ => state
      | .accepted _ =>
          match state.scheduler.lifecycle.current with
          | none => state
          | some subject =>
              installTerminatedSubject state subject
                (ResumablePreemption.cleanupSubject state.resumable subject)
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
        (Capability.revokeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject
          authoritySlot victim victimSlot).result
  | .capabilityRevokeSubtree authoritySlot victim victimSlot =>
      .capability
        (Capability.revokeSubtreeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject
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
  | .scheduleAdd subject => .scheduler (schedulerAdmission state subject).result
  | .scheduleRemove subject =>
      .scheduleRemove (ResumablePreemption.remove state.resumable subject).result
  | .scheduleNext => .scheduler (schedulerDispatch state).result
  | .scheduleYield => .scheduler (schedulerYield state).result
  | .scheduleTick => .scheduler (schedulerTick state).result
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
  | resumePreempt frame registers reason
      (hnonfatal : reason ≠ .fatalEntry)
      (herror : (ResumablePreemption.switch state.resumable state.execution.core
        frame registers).error = some reason) :
      SubsystemRejection state (.resumePreempt frame registers)
        (.resume none (some reason))
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
      (h : (Capability.revokeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject
        authoritySlot victim victimSlot).result = .rejected reason) :
      SubsystemRejection state (.capabilityRevoke authoritySlot victim victimSlot)
        (.capability (.rejected reason))
  | capabilityRevokeSubtree authoritySlot victim victimSlot reason
      (h : (Capability.revokeSubtreeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject
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
  | scheduleAdd subject reason
      (h : (schedulerAdmission state subject).result = .rejected reason) :
      SubsystemRejection state (.scheduleAdd subject) (.scheduler (.rejected reason))
  | scheduleRemove subject reason
      (h : (ResumablePreemption.remove state.resumable subject).result = .rejected reason) :
      SubsystemRejection state (.scheduleRemove subject) (.scheduleRemove (.rejected reason))
  | scheduleNext reason (h : (schedulerDispatch state).result = .rejected reason) :
      SubsystemRejection state .scheduleNext (.scheduler (.rejected reason))
  | scheduleYield reason (h : (schedulerYield state).result = .rejected reason) :
      SubsystemRejection state .scheduleYield (.scheduler (.rejected reason))
  | scheduleTick reason (h : (schedulerTick state).result = .rejected reason) :
      SubsystemRejection state .scheduleTick (.scheduler (.rejected reason))
  | terminateCurrent reason (h : (Scheduler.terminateCurrent state.scheduler).result = .rejected reason) :
      SubsystemRejection state .terminateCurrent (.scheduler (.rejected reason))

/-- A contained user fault is published to both scheduler views in the same
composite step, so neither can select from the pre-termination lifecycle. -/
theorem interrupt_contained_synchronizes_lifecycle state frame subject
    (hcontained : (dispatchHardware state.execution frame).action = .contained subject) :
    let next := applyOperation state (.interrupt frame)
    next.scheduler.lifecycle = next.execution.core.lifecycle ∧
      next.preemption.scheduler.lifecycle = next.execution.core.lifecycle := by
  simp [applyOperation, hcontained, publishInterruptCleanup,
    installTerminatedResumable]

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
  have herror := ResumablePreemption.halted_reports_fatalEntry
    state.resumable state.execution.core frame registers hhalted
  simp [applyOperation, herror, hhalted, installResumable, installLifecycle]

/-- Resumable save/select/restore republishes the scheduler-selected current
subject as the only execution caller and active address space.  Incoming frame
and register payloads therefore cannot leave the composite execution latch
bound to the preemption victim after an accepted switch. -/
theorem resumePreempt_synchronizes_current_context state frame registers
    (hcoherent : state.Coherent) :
    let next := applyOperation state (.resumePreempt frame registers)
    ∀ subject, next.scheduler.lifecycle.current = some subject →
      next.execution.core.context.currentSubject = subject ∧
      next.execution.core.context.activeAddressSpace = subject := by
  rcases hcoherent with
    ⟨_, hschedulerLifecycle, _, _, _, _, _, _, _, _, hcontext, _, _⟩
  have hcontextScheduler : ∀ subject,
      state.scheduler.lifecycle.current = some subject →
        state.execution.core.context.currentSubject = subject ∧
          state.execution.core.context.activeAddressSpace = subject := by
    intro subject hcurrent
    apply hcontext
    rw [← hschedulerLifecycle]
    exact hcurrent
  simp only [applyOperation]
  generalize hs : ResumablePreemption.switch state.resumable state.execution.core
    frame registers = outcome
  cases herror : outcome.error with
  | none =>
    simp only [herror, installResumable]
    intro subject hcurrent
    simp [hcurrent]
  | some reason =>
    cases reason with
    | fatalEntry =>
      cases hhalted : outcome.state.halted <;>
        simp only [herror, hhalted, Bool.false_eq_true, if_false, if_true,
          installResumable]
      · exact hcontextScheduler
      · intro subject hcurrent
        simp [hcurrent]
    | nonTimer | malformedIncoming | noCurrent | contextMismatch | duplicateSave |
        staleActiveSpace | bankFull | schedulerRejected | noDestination | staleDestination =>
      simpa [herror] using hcontextScheduler

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

private theorem classified_rejection_is_subsystem state operation
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    SubsystemRejection state operation (operationReply state operation) := by
  cases operation with
  | interrupt frame | selectUserReturn purpose | restart =>
      simp [operationReply, OperationReply.isNonfatalRejection] at hrejected
  | userReturn request =>
      simp only [operationReply] at hrejected
      split at hrejected <;> simp [OperationReply.isNonfatalRejection] at hrejected
  | syscall call =>
      cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
      | accepted => simp [operationReply, hreply, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hreply] using SubsystemRejection.syscall call reason hreply
  | ipc call =>
      cases hreply : (dispatchIPC state call).reply with
      | sealedTransferPending =>
          simpa [operationReply, hreply] using SubsystemRejection.ipcSealed call hreply
      | syscall reply =>
          cases reply with
          | sent | delivered sender word0 word1 =>
              simp [operationReply, hreply, OperationReply.isNonfatalRejection] at hrejected
          | sendHandleRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcSendHandle call reason hreply
          | sendRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcSend call reason hreply
          | receiveHandleRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcReceiveHandle call reason hreply
          | receiveRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcReceive call reason hreply
  | resumePreempt frame registers =>
      cases herror : (ResumablePreemption.switch state.resumable state.execution.core
          frame registers).error with
      | none => simp [operationReply, herror, OperationReply.isNonfatalRejection] at hrejected
      | some reason =>
          cases reason <;>
            simp_all [operationReply, OperationReply.isNonfatalRejection,
              ResumablePreemption.rejected_exposes_no_restore]
          all_goals
            apply SubsystemRejection.resumePreempt <;> simp_all
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      cases hresult : (CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.transferOffer
            endpointWord sourceWord sourceKind payload rights reason hresult
  | transferAccept endpointWord destinationSlot =>
      cases hresult : (CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot).result with
      | delivered envelope =>
          simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.transferAccept
            endpointWord destinationSlot reason _ hresult rfl
  | capabilityCopy source destination destinationSlot rights =>
      cases hresult : (Capability.copy state.capabilities
          state.execution.core.context.currentSubject source destination destinationSlot rights).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.capabilityCopy
            source destination destinationSlot rights reason hresult
  | capabilityRevoke authoritySlot victim victimSlot =>
      cases hresult : (Capability.revokeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim victimSlot).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.capabilityRevoke
            authoritySlot victim victimSlot reason hresult
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      cases hresult : (Capability.revokeSubtreeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim victimSlot).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.capabilityRevokeSubtree
            authoritySlot victim victimSlot reason hresult
  | map slot page permissions =>
      cases hresult : (VirtualMapping.map state.virtualMemory
          state.execution.core.context.currentSubject slot
          state.execution.core.context.activeAddressSpace page permissions).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.map slot page permissions reason hresult
  | unmap page =>
      cases hresult : (VirtualMapping.unmap state.virtualMemory
          state.execution.core.context.currentSubject state.execution.core.context.activeAddressSpace
          page).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.unmap page reason hresult
  | createSubject subject =>
      cases hresult : (SubjectLifecycle.create state.lifecycle subject).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.createSubject subject reason hresult
  | terminateSubject subject =>
      cases hresult : (SubjectLifecycle.terminate state.lifecycle subject).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.terminateSubject subject reason hresult
  | scheduleAdd subject =>
      cases hresult : (schedulerAdmission state subject).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.scheduleAdd subject reason hresult
  | scheduleRemove subject =>
      cases hresult : (ResumablePreemption.remove state.resumable subject).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.scheduleRemove subject reason hresult
  | scheduleNext =>
      cases hresult : (schedulerDispatch state).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.scheduleNext reason hresult
  | scheduleYield =>
      cases hresult : (schedulerYield state).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.scheduleYield reason hresult
  | scheduleTick =>
      cases hresult : (schedulerTick state).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.scheduleTick reason hresult
  | terminateCurrent =>
      cases hresult : (Scheduler.terminateCurrent state.scheduler).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.terminateCurrent reason hresult

/-- The total public reply classifier is sufficient to obtain global rejection
atomicity.  Unlike `gate_subsystem_rejection_atomicity`, callers do not need to
construct a matching `SubsystemRejection` witness: every reply constructor is
classified here, and every classified rejection returns the literal pre-state. -/
theorem gate_classified_rejection_atomicity state operation
    (hmode : state.execution.mode = .running)
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    (gate state operation).result = .completed (operationReply state operation) ∧
      (gate state operation).state = state := by
  refine ⟨by simp [gate, hmode], ?_⟩
  exact gate_subsystem_rejection_atomicity state operation
    (operationReply state operation) (by simp [gate, hmode])
    (classified_rejection_is_subsystem state operation hrejected)

/-- Classified subsystem rejection is globally atomic even when the outer
execution latch is busy or already halted; those modes reject before invoking
the classified subsystem transition. -/
theorem gate_classified_rejection_global_atomicity state operation
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    (gate state operation).state = state := by
  cases hmode : state.execution.mode with
  | running => exact (gate_classified_rejection_atomicity state operation hmode hrejected).2
  | handling active => simp [gate, hmode]
  | halted record => simp [gate, hmode]

/-- A total classified rejection also preserves the complete composite
invariant, as a direct consequence of byte-for-byte state preservation. -/
theorem gate_classified_rejection_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state)
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    RuntimeWellFormed (gate state operation).state ∧
      (gate state operation).state = state := by
  have hatomic := gate_classified_rejection_global_atomicity state operation hrejected
  exact ⟨by simpa [hatomic] using hstate, hatomic⟩

/-- Every ordinary resumable-preemption error is exposed as its exact typed
reply and leaves the complete composite state byte-for-byte unchanged.  The
distinguished `fatalEntry` error is excluded because it belongs to the
absorbing fatal result class. -/
theorem gate_resumePreempt_rejected_atomic state frame registers reason
    (hmode : state.execution.mode = .running)
    (hnonfatal : reason ≠ .fatalEntry)
    (herror : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).error = some reason) :
    (gate state (.resumePreempt frame registers)).result =
        .completed (.resume none (some reason)) ∧
      (gate state (.resumePreempt frame registers)).state = state := by
  have hrestored := ResumablePreemption.rejected_exposes_no_restore
    state.resumable state.execution.core frame registers reason herror
  have hresult : (gate state (.resumePreempt frame registers)).result =
      .completed (.resume none (some reason)) := by
    simp [gate, hmode, operationReply, herror, hrestored]
  refine ⟨hresult, ?_⟩
  exact gate_subsystem_rejection_atomicity state
    (.resumePreempt frame registers) (.resume none (some reason)) hresult
    (.resumePreempt frame registers reason hnonfatal herror)

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
          hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive,
          hblockingCoherent⟩
      have hselected := selectLiveReturnAuthority_execution_wellFormed state purpose hexecution
      have harmed := selectLiveReturnAuthority_armed_implies_live state purpose
      simp only [gate, hmode, applyOperation]
      rw [selectLiveReturnAuthority_eq_execution_update]
      refine ⟨?_, hselected, hlifecycle, hcapabilities, hvirtual, hipc,
        hscheduler, hpreemption, hresumable, htransfers, ?_, ?_, ?_⟩
      · simpa [CompositeState.Coherent] using hcoherent
      · simpa using hhalted
      · intro harmedSelected
        have hliveSelected := harmed (by simpa using harmedSelected)
        simpa [CompositeState.ReturnPlanLive] using hliveSelected
      · simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent

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
  have hplan : state.ReturnPlanLive = true := hstate.2.2.2.2.2.2.2.2.2.2.2.1 harmed
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
              hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority,
              hblockingCoherent⟩
          have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
          have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
            state.execution request .unselectedAuthority none hexecution
          have hresumableHalted : ResumablePreemption.WellFormed
              { state.resumable with halted := true } :=
            (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
          simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
            RuntimeWellFormed, CompositeState.Coherent,
            ResumablePreemption.wellFormed_set_halted]
          exact ⟨hliveMailbox,
            by simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent⟩
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
                  hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority,
                  hblockingCoherent⟩
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
              exact ⟨hliveMailbox,
                by simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent⟩
    · rcases hstate with
        ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
          hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority,
          hblockingCoherent⟩
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
      exact ⟨hliveMailbox,
        by simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent⟩
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

/-- An accepted sealed-transfer offer is monotonic in the live authority
registry.  Publishing its exact capability and endpoint post-state therefore
preserves every composite consumer, while retaining the pending sealed
descendant and mailbox as one atomic transfer state. -/
theorem gate_transferOffer_accepted_preserves_runtimeWellFormed state endpointWord sourceWord
    sourceKind payload rights
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (CapabilityTransfer.offerWords state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
      payload rights).result = .accepted) :
    RuntimeWellFormed
        (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).state ∧
      (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer .accepted) := by
  let next := (CapabilityTransfer.offerWords state.transfers
    state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
    payload rights).state
  have htransfer : CapabilityTransfer.WellFormed next :=
    CapabilityTransfer.offerWords_accepted_preserves_wellFormed state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
      payload rights hstate.2.2.2.2.2.2.2.2.2.1 haccepted
  have hregistry := CapabilityTransfer.offerWords_accepted_preserves_authority_registry
    state.transfers state.execution.core.context.currentSubject endpointWord sourceWord
    sourceKind payload rights haccepted
  change next.capabilities.subjects = state.transfers.capabilities.subjects ∧
      next.capabilities.objects = state.transfers.capabilities.objects ∧
      next.capabilities.kinds = state.transfers.capabilities.kinds ∧
      next.capabilities.slots = state.transfers.capabilities.slots ∧
      next.allocator = state.transfers.allocator ∧
      next.binding = state.transfers.binding ∧
      next.issued = state.transfers.issued ∧
      next.issuedAddressSpace = state.transfers.issuedAddressSpace at hregistry
  rcases hregistry with ⟨hsubjects, hobjects, hkinds, hslots, hallocator,
    hbinding, hissued, hissuedSpace⟩
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, _htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  rw [htransfersCoherent] at hsubjects hobjects hkinds hslots hallocator hbinding
  rw [htransfersCoherent] at hissued hissuedSpace
  have hsubjectsLifecycle := hsubjects.trans
    (congrArg Capability.State.subjects hipcCapabilitiesCoherent)
  have hobjectsLifecycle := hobjects.trans
    (congrArg Capability.State.objects hipcCapabilitiesCoherent)
  have hkindsLifecycle := hkinds.trans
    (congrArg Capability.State.kinds hipcCapabilitiesCoherent)
  have hslotsLifecycle := hslots.trans
    (congrArg Capability.State.slots hipcCapabilitiesCoherent)
  have hsubjectsVirtual := hsubjectsLifecycle.trans
    (congrArg Capability.State.subjects hvirtualCapabilitiesCoherent).symm
  have hobjectsVirtual := hobjectsLifecycle.trans
    (congrArg Capability.State.objects hvirtualCapabilitiesCoherent).symm
  have hkindsVirtual := hkindsLifecycle.trans
    (congrArg Capability.State.kinds hvirtualCapabilitiesCoherent).symm
  have hslotsVirtual := hslotsLifecycle.trans
    (congrArg Capability.State.slots hvirtualCapabilitiesCoherent).symm
  have hcallerTransfer : state.transfers.capabilities.subjects
      state.execution.core.context.currentSubject = true :=
    CapabilityTransfer.offerWords_accepted_caller_live state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights
      haccepted
  have htransferCapabilitiesCoherent :
      state.transfers.capabilities = state.lifecycle.capabilities := by
    rw [htransfersCoherent, hipcCapabilitiesCoherent]
  have hsenderTransfer : ∀ object envelope,
      state.transfers.mailbox object = some envelope →
        state.transfers.capabilities.subjects envelope.sender = true := by
    intro object envelope hmailbox
    rw [htransferCapabilitiesCoherent]
    exact hliveSender object envelope (by simpa [htransfersCoherent] using hmailbox)
  have hliveMailbox' :=
    CapabilityTransfer.offerWords_accepted_preserves_live_mailbox_senders state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights
      hcallerTransfer hsenderTransfer haccepted
  have hcapabilities' : Capability.WellFormed next.capabilities := htransfer.1.1
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next.capabilities } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next.capabilities } } := by
    rcases hvirtual with ⟨hwell, _hcaps, hspaces, howned⟩
    refine ⟨?_, hcapabilities', ?_, ?_⟩
    · simpa [VirtualMapping.WellFormed, Capability.HasAuthority, hsubjectsVirtual,
        hslotsVirtual]
        using hwell
    · simpa [Capability.HasAuthority, hobjectsVirtual, hkindsVirtual, hslotsVirtual]
        using hspaces
    · simpa [hobjectsVirtual, hkindsVirtual] using howned
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next.capabilities } }
        endpoints := next.toEndpointState } := ⟨hvirtual', htransfer.1⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with capabilities := next.capabilities } } := by
    rcases hscheduler with ⟨_, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle]
        using hready
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle]
        using hcurrent
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } } } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        translations := { state.resumable.translations with virtual :=
          { state.virtualMemory with memory :=
            { state.virtualMemory.memory with capabilities := next.capabilities } } } } := by
    rcases hresumable with
      ⟨_, hcapacity, hunique, hvalid, habsent, hready, htranslation,
        _hvirtual, hresources, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ⟨rfl, hvirtual'⟩, ?_, ?_⟩
    · simpa [ResumablePreemption.validContext, hresumableSchedulerCoherent,
        hschedulerCoherent, hsubjectsLifecycle] using hvalid
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement, hresumableVirtualCoherent,
        hresumableSchedulerCoherent, hschedulerCoherent] using htranslation
    · simpa [ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent, hkindsLifecycle] using hresources
    · simpa [TLB.Coherent] using htlb
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        returnAuthorityArmed := false } := by
    rcases hexecution with ⟨_, _hbound, hmodeWellFormed⟩
    refine ⟨?_, by simp, ?_⟩
    · simpa [Interrupt.WellFormed] using hlifecycle'
    · simpa using hmodeWellFormed
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    refine ⟨?_, hexecution', hlifecycle', hcapabilities', hvirtual', hipc',
      hscheduler', hpreemption', hresumable', htransfer, ?_, ?_⟩
    · simp [installTransfers, CompositeState.Coherent]
      refine ⟨?_, ?_, ?_⟩
      · intro subject hcurrent
        exact hauthorityCoherent subject hcurrent
      · intro object hfalse
        apply htransfer.1.2.2.2.1 object
        intro htrue
        have hfalse' : next.capabilities.objects object = false := by
          simpa [next] using hfalse
        rw [htrue] at hfalse'
        contradiction
      · intro object envelope hmailbox
        exact hliveMailbox' object envelope hmailbox
    · simpa [installTransfers] using hhalted
    · exact ⟨by simp [installTransfers], ⟨rfl, rfl⟩⟩
  · simp [gate, hmode, operationReply, haccepted]

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

/-- Publishing a transfer transition is globally safe when it retains the
live registries and all pre-existing authority, and when every surviving
mailbox has a pre-state provenance witness.  This is the common composite
boundary used by receipt, whose only capability mutation fills a checked-empty
slot and whose only mailbox mutation consumes the selected message. -/
private theorem installTransfers_preserves_runtimeWellFormed state next
    (hstate : RuntimeWellFormed state)
    (htransfer : CapabilityTransfer.WellFormed next)
    (hsubjects : next.capabilities.subjects = state.transfers.capabilities.subjects)
    (hobjects : next.capabilities.objects = state.transfers.capabilities.objects)
    (hkinds : next.capabilities.kinds = state.transfers.capabilities.kinds)
    (hauthority : ∀ subject object right,
      Capability.HasAuthority state.transfers.capabilities subject object right →
        Capability.HasAuthority next.capabilities subject object right)
    (hmailbox : ∀ object envelope, next.mailbox object = some envelope →
      state.transfers.mailbox object = some envelope) :
    RuntimeWellFormed (installTransfers state next) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, _hcapabilities, hvirtual, _hipc,
      hscheduler, hpreemption, hresumable, _htransfers, hhalted, _hlivePlan⟩
  rcases hcoherent with
    ⟨_hexecutionCoherent, hschedulerCoherent, _hpreemptionCoherent,
      _hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, _hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      _hdeadMailbox, hliveSender⟩
  have hsubjectsLifecycle :
      next.capabilities.subjects = state.lifecycle.capabilities.subjects :=
    hsubjects.trans ((congrArg (fun endpoints : EndpointIPC.State =>
      endpoints.capabilities.subjects) htransfersCoherent).trans
      (congrArg Capability.State.subjects hipcCapabilitiesCoherent))
  have hobjectsLifecycle :
      next.capabilities.objects = state.lifecycle.capabilities.objects :=
    hobjects.trans ((congrArg (fun endpoints : EndpointIPC.State =>
      endpoints.capabilities.objects) htransfersCoherent).trans
      (congrArg Capability.State.objects hipcCapabilitiesCoherent))
  have hkindsLifecycle :
      next.capabilities.kinds = state.lifecycle.capabilities.kinds :=
    hkinds.trans ((congrArg (fun endpoints : EndpointIPC.State =>
      endpoints.capabilities.kinds) htransfersCoherent).trans
      (congrArg Capability.State.kinds hipcCapabilitiesCoherent))
  have hcapabilities' : Capability.WellFormed next.capabilities := htransfer.1.1
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next.capabilities } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next.capabilities } } := by
    rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hcapabilities,
      haddressSpaces, hownedAddressSpaces⟩
    refine ⟨⟨?_, ?_⟩, hcapabilities', ?_, ?_⟩
    · intro addressSpace subject howner
      have hold := hownerLive addressSpace subject howner
      rw [hvirtualCapabilitiesCoherent] at hold
      simpa [hsubjectsLifecycle] using hold
    · intro addressSpace page mapping hmapping
      obtain ⟨subject, frame, howner, hpermissions, hbinding, hframe,
        hread, hwrite⟩ := hmappings addressSpace page mapping hmapping
      refine ⟨subject, frame, howner, hpermissions, hbinding, hframe, ?_, ?_⟩
      · intro hpermission
        apply hauthority subject mapping.object .read
        rw [htransfersCoherent, hipcCapabilitiesCoherent,
          ← hvirtualCapabilitiesCoherent]
        exact hread hpermission
      · intro hpermission
        apply hauthority subject mapping.object .write
        rw [htransfersCoherent, hipcCapabilitiesCoherent,
          ← hvirtualCapabilitiesCoherent]
        exact hwrite hpermission
    · intro addressSpace subject howner
      obtain ⟨hlive, hkind, hissuedAddressSpace, hissuedMemory, hrevoke⟩ :=
        haddressSpaces addressSpace subject howner
      refine ⟨?_, ?_, hissuedAddressSpace, hissuedMemory, ?_⟩
      · rw [hvirtualCapabilitiesCoherent] at hlive
        simpa [hobjectsLifecycle] using hlive
      · rw [hvirtualCapabilitiesCoherent] at hkind
        simpa [hkindsLifecycle] using hkind
      · apply hauthority subject addressSpace .revoke
        rw [htransfersCoherent, hipcCapabilitiesCoherent,
          ← hvirtualCapabilitiesCoherent]
        exact hrevoke
    · intro addressSpace hlive hkind
      apply hownedAddressSpaces addressSpace
      · change next.capabilities.objects addressSpace = true at hlive
        rw [hobjectsLifecycle] at hlive
        rw [hvirtualCapabilitiesCoherent]
        exact hlive
      · change next.capabilities.kinds addressSpace = some .addressSpace at hkind
        rw [hkindsLifecycle] at hkind
        rw [hvirtualCapabilitiesCoherent]
        exact hkind
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next.capabilities } }
        endpoints := next.toEndpointState } := ⟨hvirtual', htransfer.1⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with capabilities := next.capabilities } } := by
    rcases hscheduler with ⟨_, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using hready
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using hcurrent
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } } } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        translations := { state.resumable.translations with virtual :=
          { state.virtualMemory with memory :=
            { state.virtualMemory.memory with capabilities := next.capabilities } } } } := by
    rcases hresumable with
      ⟨_, hcapacity, hunique, hvalid, habsent, hready, htranslation,
        _hvirtual, hresources, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ⟨rfl, hvirtual'⟩, ?_, ?_⟩
    · simpa [ResumablePreemption.validContext, hresumableSchedulerCoherent,
        hschedulerCoherent, hsubjectsLifecycle] using hvalid
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement, hresumableVirtualCoherent,
        hresumableSchedulerCoherent, hschedulerCoherent] using htranslation
    · simpa [ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent, hkindsLifecycle] using hresources
    · simpa [TLB.Coherent] using htlb
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        returnAuthorityArmed := false } := by
    rcases hexecution with ⟨_, _hbound, hmodeWellFormed⟩
    refine ⟨?_, by simp, ?_⟩
    · simpa [Interrupt.WellFormed] using hlifecycle'
    · simpa using hmodeWellFormed
  refine ⟨?_, hexecution', hlifecycle', hcapabilities', hvirtual', hipc',
    hscheduler', hpreemption', hresumable', htransfer, ?_, ?_⟩
  · simp [installTransfers, CompositeState.Coherent]
    refine ⟨?_, ?_, ?_⟩
    · intro subject hcurrent
      exact hauthorityCoherent subject hcurrent
    · intro object hfalse
      apply htransfer.1.2.2.2.1 object
      intro htrue
      rw [htrue] at hfalse
      contradiction
    · intro object envelope hnextMailbox
      have hold := hliveSender object envelope (by
        simpa [htransfersCoherent] using hmailbox object envelope hnextMailbox)
      simpa [hsubjectsLifecycle] using hold
  · simpa [installTransfers] using hhalted
  · exact ⟨by simp [installTransfers], ⟨rfl, rfl⟩⟩

/-- A delivered public transfer receipt is a complete global mutation: it
atomically consumes the selected mailbox and pending tag, installs the sealed
descendant into the receiver's checked-empty slot, and preserves every
composite runtime invariant. -/
theorem gate_transferAccept_delivered_preserves_runtimeWellFormed state endpointWord
    destinationSlot envelope
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (CapabilityTransfer.acceptWord state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot).result =
        .delivered envelope) :
    RuntimeWellFormed (gate state (.transferAccept endpointWord destinationSlot)).state ∧
      (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept (.delivered envelope)
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord
            destinationSlot).deliveredWord) := by
  let next := (CapabilityTransfer.acceptWord state.transfers
    state.execution.core.context.currentSubject endpointWord destinationSlot).state
  have htransfer : CapabilityTransfer.WellFormed next :=
    CapabilityTransfer.acceptWord_preserves_wellFormed state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot
      hstate.2.2.2.2.2.2.2.2.2.1
  have hmetadata := CapabilityTransfer.acceptWord_delivered_preserves_registry_and_authority
    state.transfers state.execution.core.context.currentSubject endpointWord destinationSlot
      envelope hdelivered
  change next.capabilities.subjects = state.transfers.capabilities.subjects ∧
      next.capabilities.objects = state.transfers.capabilities.objects ∧
      next.capabilities.kinds = state.transfers.capabilities.kinds ∧
      next.capabilities.slotCapacity = state.transfers.capabilities.slotCapacity ∧
      (∀ subject slot capability,
        state.transfers.capabilities.slots subject slot = some capability →
          next.capabilities.slots subject slot = some capability) ∧
      (∀ subject object right,
        Capability.HasAuthority state.transfers.capabilities subject object right →
          Capability.HasAuthority next.capabilities subject object right) at hmetadata
  rcases hmetadata with ⟨hsubjects, hobjects, hkinds, _hcapacity, _hslots, hauthority⟩
  constructor
  · simp only [gate, hmode, applyOperation, hdelivered]
    exact installTransfers_preserves_runtimeWellFormed state next hstate htransfer
      hsubjects hobjects hkinds hauthority (by
        intro object found hmailbox
        exact CapabilityTransfer.acceptWord_mailbox_provenance state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot
          object found (by simpa [next] using hmailbox))
  · simp [gate, hmode, operationReply, hdelivered]

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
    (haccepted : schedulerAdmission state subject =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state (.scheduleAdd subject)).state.scheduler = next ∧
      Scheduler.WellFormed (gate state (.scheduleAdd subject)).state.scheduler := by
  obtain ⟨hadd, _hsaved⟩ := schedulerAdmission_accepted_exact
    state subject context next haccepted
  have hpreserved := Scheduler.add_preserves_wellFormed state.scheduler subject hwellFormed
  rw [hadd] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted,
    installSchedulerAdmission, hpreserved]

/-- The only accepted raw dispatch is empty selection, whose exact scheduler
post-state is the unchanged authoritative scheduler. -/
theorem gate_scheduleNext_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : schedulerDispatch state =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleNext).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleNext).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleNext).state.scheduler := by
  have hnone : context = none := schedulerDispatch_accepted_is_none state context (by
    simp [haccepted])
  subst context
  have hnext : next = state.scheduler := by
    have hold := schedulerDispatch_accepted_none_unchanged state (by simp [haccepted])
    simpa [haccepted] using hold
  subst next
  simp [gate, hmode, operationReply, applyOperation, haccepted, hwellFormed]

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

/-- Raw voluntary yield has no accepted composite result because it carries no
outgoing context payload.  This theorem records that unreachable contract. -/
theorem gate_scheduleYield_accepted_sound state context next
    (_hmode : state.execution.mode = .running)
    (haccepted : schedulerYield state =
      { state := next, result := .accepted context })
    (_hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleYield).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleYield).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleYield).state.scheduler := by
  exact False.elim ((schedulerYield_ne_accepted state context) (by simp [haccepted]))

/-- Raw timer tick likewise has no accepted composite result; resumable timer
switching is owned by the save/select/restore operation. -/
theorem gate_scheduleTick_accepted_sound state context next
    (_hmode : state.execution.mode = .running)
    (haccepted : schedulerTick state =
      { state := next, result := .accepted context })
    (_hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleTick).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleTick).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleTick).state.scheduler := by
  exact False.elim ((schedulerTick_ne_accepted state context) (by simp [haccepted]))

/-- Accepted current-subject termination identifies the kernel-selected victim
and publishes the authoritative resumable cleanup for that subject.  This is
deliberately stronger than exposing the raw scheduler post-state: owned address
spaces, translations, mailboxes, transfers, and saved contexts are retired by
the composite mutation too. -/
theorem gate_terminateCurrent_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.terminateCurrent state.scheduler =
      { state := next, result := .accepted context })
    (_hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .terminateCurrent).result =
        .completed (.scheduler (.accepted context)) ∧
      ∃ subject, state.scheduler.lifecycle.current = some subject ∧
        (gate state .terminateCurrent).state =
          installTerminatedSubject state subject
            (ResumablePreemption.cleanupSubject state.resumable subject) := by
  cases hcurrent : state.scheduler.lifecycle.current with
  | none => simp [Scheduler.terminateCurrent, hcurrent, Scheduler.reject] at haccepted
  | some subject =>
      constructor
      · simp [gate, hmode, operationReply, haccepted]
      · refine ⟨subject, rfl, ?_⟩
        simp [gate, hmode, applyOperation, haccepted, hcurrent]

/-- Accepted capability copying publishes the exact fresh capability state to
every consumer.  The composite reply cannot report success while lifecycle,
IPC, scheduler, mapping, or saved-context projections retain the old registry. -/
theorem gate_capabilityCopy_accepted_synchronizes state source destination destinationSlot
    rights next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.copy state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights =
        { state := next, result := .accepted })
    (hcoherent : state.Coherent)
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
  have hregistries := Capability.copy_preserves_registries state.capabilities
    state.execution.core.context.currentSubject source destination destinationSlot rights
  rw [haccepted] at hregistries
  rcases hregistries with ⟨hsubjects, hobjects, _hkinds, _hcapacity⟩
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    rcases hcoherent with
      ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
        hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
        htransfers, hauthority, hdeadMailbox, hliveSender⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthority
    · intro object hdead
      have hdeadNext : next.objects object ≠ true := by
        simpa [installCopiedCapabilities] using hdead
      apply hdeadMailbox object
      rw [← hcapabilities, ← hobjects]
      exact hdeadNext
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjects, hcapabilities]
      exact hold
  rcases installCopiedCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed
      (installCopiedCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent'
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                        (And.intro htransfers hpublished)))))))))

/-- Accepted delegation is a complete runtime-preservation slice.  It retains
all resource projections exactly, publishes the fresh derivation to every
capability consumer, preserves authority already used by mappings, and keeps
every pending sealed identity disjoint from live slots. -/
theorem gate_capabilityCopy_accepted_preserves_runtimeWellFormed state source destination
    destinationSlot rights next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.copy state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights =
        { state := next, result := .accepted }) :
    RuntimeWellFormed
        (gate state (.capabilityCopy source destination destinationSlot rights)).state ∧
      (gate state (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability .accepted) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlivePlan⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  have hcapabilities' : Capability.WellFormed next := by
    have hpreserved := Capability.copy_preserves_wellFormed state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights
      hcapabilities
    simpa [haccepted] using hpreserved
  have hregistries := Capability.copy_preserves_registries state.capabilities
    state.execution.core.context.currentSubject source destination destinationSlot rights
  rw [haccepted] at hregistries
  rcases hregistries with ⟨hsubjects, hobjects, hkinds, hslotCapacity⟩
  have hsubjectsLifecycle : next.subjects = state.lifecycle.capabilities.subjects :=
    hsubjects.trans (congrArg Capability.State.subjects hcapabilitiesCoherent)
  have hobjectsLifecycle : next.objects = state.lifecycle.capabilities.objects :=
    hobjects.trans (congrArg Capability.State.objects hcapabilitiesCoherent)
  have hkindsLifecycle : next.kinds = state.lifecycle.capabilities.kinds :=
    hkinds.trans (congrArg Capability.State.kinds hcapabilitiesCoherent)
  have hauthority : ∀ subject object right,
      Capability.HasAuthority state.capabilities subject object right →
        Capability.HasAuthority next subject object right := by
    intro subject object right hold
    have hpreserved := Capability.copy_preserves_authority state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights
      subject object right hold
    simpa [haccepted] using hpreserved
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next } } := by
    rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hcapabilities,
      haddressSpaces, hownedAddressSpaces⟩
    refine ⟨⟨?_, ?_⟩, hcapabilities', ?_, ?_⟩
    · intro addressSpace subject howner
      have hold := hownerLive addressSpace subject howner
      rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hold
      rw [hsubjects]
      exact hold
    · intro addressSpace page mapping hmapping
      obtain ⟨subject, frame, howner, hpermissions, hbinding, hframe,
        hread, hwrite⟩ := hmappings addressSpace page mapping hmapping
      refine ⟨subject, frame, howner, hpermissions, hbinding, hframe, ?_, ?_⟩
      · intro hpermission
        apply hauthority subject mapping.object .read
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hread
        exact hread hpermission
      · intro hpermission
        apply hauthority subject mapping.object .write
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hwrite
        exact hwrite hpermission
    · intro addressSpace subject howner
      obtain ⟨hlive, hkind, hissuedAddressSpace, hissuedMemory, hrevoke⟩ :=
        haddressSpaces addressSpace subject howner
      refine ⟨?_, ?_, hissuedAddressSpace, hissuedMemory, ?_⟩
      · rw [hobjects]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · rw [hkinds]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
      · apply hauthority subject addressSpace .revoke
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hrevoke
        exact hrevoke
    · intro addressSpace hlive hkind
      apply hownedAddressSpaces addressSpace
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
  have hendpoint' : EndpointIPC.WellFormed
      { state.ipc.endpoints with capabilities := next } := by
    rcases hipc.2 with ⟨_hcapabilities, hissued, hmailbox, hdead, hhistory⟩
    refine ⟨hcapabilities', ?_, ?_, ?_, ?_⟩
    · intro object hlive hkind
      apply hissued object
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
    · intro object envelope hmail
      obtain ⟨hlive, hkind, hendpoint, hsent⟩ := hmailbox object envelope hmail
      refine ⟨?_, ?_, hendpoint, hsent⟩
      · rw [hobjects]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · rw [hkinds]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
    · intro object hretired
      apply hdead object
      intro hlive
      apply hretired
      rw [hobjects]
      rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
      exact hlive
    · exact hhistory
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next } }
        endpoints := { state.ipc.endpoints with capabilities := next } } :=
    ⟨hvirtual', hendpoint'⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } := by
    rcases hscheduler with
      ⟨_hlifecycle, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · intro subject hmember
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using
        hready subject hmember
    · intro subject hselected
      have hselectedOld : state.scheduler.lifecycle.current = some subject := by
        simpa [hschedulerCoherent] using hselected
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using
        hcurrent subject hselectedOld
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } } := by
    exact ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with
          lifecycle := { state.lifecycle with capabilities := next } }
        translations := { state.resumable.translations with
          virtual := { state.virtualMemory with
            memory := { state.virtualMemory.memory with capabilities := next } } } } := by
    rcases hresumable with
      ⟨_hscheduler, hcapacity, hunique, hvalid, habsent, hready,
        htranslation, _hvirtual, hkindsAgreement, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro context hcontext
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context hcontext
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at hlive hrunnable howner
      refine ⟨hframe, hspace, ?_, hrunnable, howner⟩
      rw [hsubjectsLifecycle]
      exact hlive
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent,
        hresumableVirtualCoherent] using htranslation
    · exact ⟨rfl, hvirtual'⟩
    · rcases hkindsAgreement with ⟨hmemoryKinds, hendpointKinds⟩
      refine ⟨?_, ?_⟩
      · intro object owner frame howned
        have hold := hmemoryKinds object owner frame (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        rw [hkindsLifecycle]
        exact hold
      · intro object owner howned
        have hold := hendpointKinds object owner (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        rw [hkindsLifecycle]
        exact hold
    · simpa [TLB.Coherent] using htlb
  have htransfers' : CapabilityTransfer.WellFormed
      { state.transfers with
        toEndpointState := { state.ipc.endpoints with capabilities := next } } := by
    rcases htransfers with ⟨_hendpoints, hpending⟩
    refine ⟨hendpoint', ?_⟩
    intro endpoint transfer hpendingNew
    have hpendingOld : state.transfers.pending endpoint = some transfer := hpendingNew
    obtain ⟨henvelope, hlive, hkind, hrights, hderivation, hparent,
      hparentIdentity, hidentity, habsentIdentity, huniquePending⟩ :=
      hpending endpoint transfer hpendingOld
    have htransferCapabilities : state.transfers.capabilities = state.capabilities := by
      rw [htransfersCoherent, hipcCapabilitiesCoherent, ← hcapabilitiesCoherent]
    rw [htransferCapabilities] at hlive hkind hderivation hparent hidentity habsentIdentity
    have hderivation' : next.derivations transfer.identity =
        some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) := by
      have hold := Capability.copy_preserves_derivation_of_lt state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
        transfer.identity hidentity
      rw [haccepted] at hold
      exact hold.trans hderivation
    obtain ⟨parentParent, parentRights, hparentDerivation, hsubset⟩ := hparent
    have hparentDerivation' : next.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) := by
      have hold := Capability.copy_preserves_derivation_of_lt state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
        transfer.parent (Nat.lt_trans hparentIdentity hidentity)
      rw [haccepted] at hold
      exact hold.trans hparentDerivation
    have habsentIdentity' : ∀ subject slot capability,
        next.slots subject slot = some capability → capability.identity ≠ transfer.identity := by
      have hold := Capability.copy_preserves_absent_identity state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
        transfer.identity hidentity habsentIdentity
      simpa [haccepted] using hold
    have hidentity' : transfer.identity < next.nextIdentity :=
      (hcapabilities'.2.1 transfer.identity (some transfer.parent) transfer.object
        transfer.kind transfer.rights hderivation').1
    refine ⟨by simpa [htransfersCoherent] using henvelope, ?_, ?_, hrights, hderivation',
      ⟨parentParent, parentRights, hparentDerivation', hsubset⟩,
      hparentIdentity, hidentity', habsentIdentity', huniquePending⟩
    · rw [hobjects]
      exact hlive
    · rw [hkinds]
      exact hkind
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthorityCoherent
    · intro object hdead
      apply hdeadMailbox object
      have hdeadNext : next.objects object ≠ true := by
        simpa [installCopiedCapabilities] using hdead
      rw [← hobjectsLifecycle]
      exact hdeadNext
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjectsLifecycle]
      exact hold
  have hexecution' : WellFormed
      (installCopiedCapabilities state next).execution := by
    rcases hexecution with ⟨hcore, _hbound, hmodeWellFormed⟩
    refine ⟨?_, by simp [installCopiedCapabilities], hmodeWellFormed⟩
    · simpa [Interrupt.WellFormed, installCopiedCapabilities] using hlifecycle'
  have hlivePlan' :
      (installCopiedCapabilities state next).execution.returnAuthorityArmed = true →
        (installCopiedCapabilities state next).ReturnPlanLive = true := by
    simp [installCopiedCapabilities]
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    exact ⟨hcoherent', hexecution', hlifecycle', hcapabilities', hvirtual', hipc',
      hscheduler', hpreemption', hresumable', htransfers',
      by simpa [installCopiedCapabilities] using hhalted, ⟨hlivePlan', ⟨rfl, rfl⟩⟩⟩
  · simp [gate, hmode, operationReply, haccepted]

/-- The authority fragment consumed by live virtual mappings and address-space
ownership.  Revocation may remove arbitrary delegated rights, but a composite
runtime publication is well formed when these three resource-critical rights
remain available through some live capability. -/
def RuntimeAuthorityPreserved (before after : Capability.State) : Prop :=
  ∀ subject object right,
    (right = .read ∨ right = .write ∨ right = .revoke) →
    Capability.HasAuthority before subject object right →
    Capability.HasAuthority after subject object right

/-- Removing slots while retaining registries, history, and runtime-critical
authority preserves every global projection.  This is shared by direct and
transitive revocation; `hslots` also preserves the sealed-transfer invariant
that pending identities are absent from live slots. -/
private theorem installRevokedCapabilities_preserves_runtimeWellFormed state next
    (hstate : RuntimeWellFormed state)
    (hwellFormed : Capability.WellFormed next)
    (hsubjects : next.subjects = state.capabilities.subjects)
    (hobjects : next.objects = state.capabilities.objects)
    (hkinds : next.kinds = state.capabilities.kinds)
    (hnextIdentity : next.nextIdentity = state.capabilities.nextIdentity)
    (hderivations : next.derivations = state.capabilities.derivations)
    (hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.capabilities.slots subject slot = some capability)
    (hauthority : RuntimeAuthorityPreserved state.capabilities next) :
    RuntimeWellFormed (installCopiedCapabilities state next) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, _hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, _hlivePlan⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, _hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, _hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  have hsubjectsLifecycle : next.subjects = state.lifecycle.capabilities.subjects :=
    hsubjects.trans (congrArg Capability.State.subjects hcapabilitiesCoherent)
  have hobjectsLifecycle : next.objects = state.lifecycle.capabilities.objects :=
    hobjects.trans (congrArg Capability.State.objects hcapabilitiesCoherent)
  have hkindsLifecycle : next.kinds = state.lifecycle.capabilities.kinds :=
    hkinds.trans (congrArg Capability.State.kinds hcapabilitiesCoherent)
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next } } := by
    rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hcapabilities,
      haddressSpaces, hownedAddressSpaces⟩
    refine ⟨⟨?_, ?_⟩, hwellFormed, ?_, ?_⟩
    · intro addressSpace subject howner
      have hold := hownerLive addressSpace subject howner
      rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hold
      rw [hsubjects]
      exact hold
    · intro addressSpace page mapping hmapping
      obtain ⟨subject, frame, howner, hpermissions, hbinding, hframe,
        hread, hwrite⟩ := hmappings addressSpace page mapping hmapping
      refine ⟨subject, frame, howner, hpermissions, hbinding, hframe, ?_, ?_⟩
      · intro hpermission
        apply hauthority subject mapping.object .read (Or.inl rfl)
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hread
        exact hread hpermission
      · intro hpermission
        apply hauthority subject mapping.object .write (Or.inr (Or.inl rfl))
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hwrite
        exact hwrite hpermission
    · intro addressSpace subject howner
      obtain ⟨hlive, hkind, hissuedAddressSpace, hissuedMemory, hrevoke⟩ :=
        haddressSpaces addressSpace subject howner
      refine ⟨?_, ?_, hissuedAddressSpace, hissuedMemory, ?_⟩
      · rw [hobjects]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · rw [hkinds]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
      · apply hauthority subject addressSpace .revoke (Or.inr (Or.inr rfl))
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hrevoke
        exact hrevoke
    · intro addressSpace hlive hkind
      apply hownedAddressSpaces addressSpace
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
  have hendpoint' : EndpointIPC.WellFormed
      { state.ipc.endpoints with capabilities := next } := by
    rcases hipc.2 with ⟨_hcapabilities, hissued, hmailbox, hdead, hhistory⟩
    refine ⟨hwellFormed, ?_, ?_, ?_, hhistory⟩
    · intro object hlive hkind
      apply hissued object
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
    · intro object envelope hmail
      obtain ⟨hlive, hkind, hendpoint, hsent⟩ := hmailbox object envelope hmail
      refine ⟨?_, ?_, hendpoint, hsent⟩
      · change next.objects object = true
        rw [hobjects]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · change next.kinds object = some .endpoint
        rw [hkinds]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
    · intro object hretired
      apply hdead object
      intro hlive
      apply hretired
      change next.objects object = true
      rw [hobjects]
      rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
      exact hlive
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next } }
        endpoints := { state.ipc.endpoints with capabilities := next } } :=
    ⟨hvirtual', hendpoint'⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } := by
    rcases hscheduler with ⟨_hlifecycle, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · intro subject hmember
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using
        hready subject hmember
    · intro subject hselected
      have hold := hcurrent subject (by simpa [hschedulerCoherent] using hselected)
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using hold
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with
          lifecycle := { state.lifecycle with capabilities := next } }
        translations := { state.resumable.translations with
          virtual := { state.virtualMemory with
            memory := { state.virtualMemory.memory with capabilities := next } } } } := by
    rcases hresumable with
      ⟨_hscheduler, hcapacity, hunique, hvalid, habsent, hready,
        htranslation, _hvirtual, hkindsAgreement, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro context hcontext
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context hcontext
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at hlive hrunnable howner
      exact ⟨hframe, hspace, by simpa [hsubjectsLifecycle] using hlive, hrunnable, howner⟩
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent,
        hresumableVirtualCoherent] using htranslation
    · exact ⟨rfl, hvirtual'⟩
    · rcases hkindsAgreement with ⟨hmemoryKinds, hendpointKinds⟩
      refine ⟨?_, ?_⟩
      · intro object owner frame howned
        have hold := hmemoryKinds object owner frame (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        simpa [hkindsLifecycle] using hold
      · intro object owner howned
        have hold := hendpointKinds object owner (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        simpa [hkindsLifecycle] using hold
    · simpa [TLB.Coherent] using htlb
  have htransfers' : CapabilityTransfer.WellFormed
      { state.transfers with
        toEndpointState := { state.ipc.endpoints with capabilities := next } } := by
    rcases htransfers with ⟨_hendpoints, hpending⟩
    refine ⟨hendpoint', ?_⟩
    intro endpoint transfer hpendingNew
    obtain ⟨henvelope, hlive, hkind, hrights, hderivation, hparent,
      hparentIdentity, hidentity, habsentIdentity, huniquePending⟩ :=
      hpending endpoint transfer hpendingNew
    have htransferCapabilities : state.transfers.capabilities = state.capabilities := by
      rw [htransfersCoherent, hipcCapabilitiesCoherent, ← hcapabilitiesCoherent]
    rw [htransferCapabilities] at hlive hkind hderivation hparent hidentity habsentIdentity
    obtain ⟨parentParent, parentRights, hparentDerivation, hsubset⟩ := hparent
    have hderivation' : next.derivations transfer.identity =
        some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) := by
      rw [hderivations]
      exact hderivation
    have hparentDerivation' : next.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) := by
      rw [hderivations]
      exact hparentDerivation
    have habsentIdentity' : ∀ subject slot capability,
        next.slots subject slot = some capability → capability.identity ≠ transfer.identity := by
      intro subject slot capability hslot
      exact habsentIdentity subject slot capability (hslots subject slot capability hslot)
    refine ⟨by simpa [htransfersCoherent] using henvelope, ?_, ?_, hrights, hderivation',
      ⟨parentParent, parentRights, hparentDerivation', hsubset⟩,
      hparentIdentity, by simpa [hnextIdentity] using hidentity,
      habsentIdentity', huniquePending⟩
    · simpa [hobjects] using hlive
    · simpa [hkinds] using hkind
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthorityCoherent
    · intro object hdead
      apply hdeadMailbox object
      rw [← hcapabilitiesCoherent, ← hobjects]
      simpa [installCopiedCapabilities] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      simpa [hsubjectsLifecycle] using hold
  have hexecution' : WellFormed (installCopiedCapabilities state next).execution := by
    rcases hexecution with ⟨hcore, _hbound, hmodeWellFormed⟩
    exact ⟨by simpa [Interrupt.WellFormed, installCopiedCapabilities] using hlifecycle',
      by simp [installCopiedCapabilities], hmodeWellFormed⟩
  exact ⟨hcoherent', hexecution', hlifecycle', hwellFormed, hvirtual', hipc',
    hscheduler', hpreemption', hresumable', htransfers',
    by simpa [installCopiedCapabilities] using hhalted,
    ⟨by simp [installCopiedCapabilities], ⟨rfl, rfl⟩⟩⟩

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
    (haccepted : Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hcoherent : state.Coherent)
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
  have hraw := (Capability.revokeRuntimeSafe_accepted_raw state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted).1
  have hpreserved := Capability.revoke_preserves_wellFormed state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot hwellFormed
  rw [hraw] at hpreserved
  have hmetadata := Capability.revoke_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    rcases hcoherent with
      ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
        hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
        htransfers, hauthority, hdeadMailbox, hliveSender⟩
    rcases hmetadata with ⟨hsubjects, hobjects, _hkinds, _hcapacity, _hnext, _hderivations⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthority
    · intro object hdead
      apply hdeadMailbox object
      rw [← hcapabilities, ← hobjects]
      simpa [installCopiedCapabilities] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjects, hcapabilities]
      exact hold
  rcases installCopiedCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed
      (installCopiedCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent'
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
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hcoherent : state.Coherent)
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
  have hraw := (Capability.revokeSubtreeRuntimeSafe_accepted_raw state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted).1
  have hpreserved := Capability.revokeSubtree_preserves_wellFormed
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim victimSlot
    hwellFormed
  rw [hraw] at hpreserved
  have hmetadata := Capability.revokeSubtree_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    rcases hcoherent with
      ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
        hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
        htransfers, hauthority, hdeadMailbox, hliveSender⟩
    rcases hmetadata with ⟨hsubjects, hobjects, _hkinds, _hcapacity, _hnext, _hderivations⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthority
    · intro object hdead
      apply hdeadMailbox object
      rw [← hcapabilities, ← hobjects]
      simpa [installCopiedCapabilities] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjects, hcapabilities]
      exact hold
  rcases installCopiedCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed
      (installCopiedCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent'
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                      (And.intro htransfers hpublished)))))))))

/-- Accepted direct revocation preserves the complete runtime invariant when
the removed slot was not the last source of authority used by live mappings or
address-space ownership.  Success is paired with the exact typed capability
reply in the same gate step. -/
theorem gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state authoritySlot victim
    victimSlot next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted }) :
    RuntimeWellFormed
        (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state ∧
      (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) := by
  obtain ⟨hraw, _hsafe⟩ := Capability.revokeRuntimeSafe_accepted_raw state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted
  have hauthority : RuntimeAuthorityPreserved state.capabilities next :=
    Capability.revokeRuntimeSafe_accepted_preserves_critical_authority state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted
  have hmetadata := Capability.revoke_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  rcases hmetadata with
    ⟨hsubjects, hobjects, hkinds, _hcapacity, hnextIdentity, hderivations⟩
  have hwellFormed : Capability.WellFormed next := by
    have hold := Capability.revoke_preserves_wellFormed state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot hstate.2.2.2.1
    simpa [hraw] using hold
  have hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.capabilities.slots subject slot = some capability := by
    intro subject slot capability hslot
    have hold := Capability.revoke_slot_survives state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot
      subject slot capability
    rw [hraw] at hold
    exact hold hslot
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    exact installRevokedCapabilities_preserves_runtimeWellFormed state next hstate hwellFormed
      hsubjects hobjects hkinds hnextIdentity hderivations hslots hauthority
  · simp [gate, hmode, operationReply, haccepted]

/-- The same preservation boundary applies to transitive lineage revocation.
The slot-survival projection guarantees that clearing additional descendants
cannot make a pending sealed identity suddenly live. -/
theorem gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state authoritySlot
    victim victimSlot next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted }) :
    RuntimeWellFormed
        (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state ∧
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) := by
  obtain ⟨hraw, _hsafe⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_raw
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim victimSlot
    next haccepted
  have hauthority : RuntimeAuthorityPreserved state.capabilities next :=
    Capability.revokeSubtreeRuntimeSafe_accepted_preserves_critical_authority state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot next
      hstate.2.2.2.1 haccepted
  have hmetadata := Capability.revokeSubtree_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  rcases hmetadata with
    ⟨hsubjects, hobjects, hkinds, _hcapacity, hnextIdentity, hderivations⟩
  have hwellFormed : Capability.WellFormed next := by
    have hold := Capability.revokeSubtree_preserves_wellFormed state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot hstate.2.2.2.1
    simpa [hraw] using hold
  have hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.capabilities.slots subject slot = some capability := by
    intro subject slot capability hslot
    have hold := Capability.revokeSubtree_slot_survives state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot
      subject slot capability
    rw [hraw] at hold
    exact hold hslot
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    exact installRevokedCapabilities_preserves_runtimeWellFormed state next hstate hwellFormed
      hsubjects hobjects hkinds hnextIdentity hderivations hslots hauthority
  · simp [gate, hmode, operationReply, haccepted]

/-- A typed direct-revocation denial is globally atomic and therefore retains
the complete runtime invariant. -/
theorem gate_capabilityRevoke_rejected_atomic state authoritySlot victim victimSlot reason
    (hstate : RuntimeWellFormed state)
    (hresult : (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
      .completed (.capability (.rejected reason)))
    (hrejected : (Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot).result =
        .rejected reason) :
    (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state = state ∧
      RuntimeWellFormed
        (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state := by
  have hold := gate_subsystem_rejection_preserves_runtimeWellFormed state
    (.capabilityRevoke authoritySlot victim victimSlot)
    (.capability (.rejected reason)) hstate hresult
    (.capabilityRevoke authoritySlot victim victimSlot reason hrejected)
  exact ⟨hold.2, hold.1⟩

/-- A typed subtree-revocation denial is likewise a literal state-preserving
gate result. -/
theorem gate_capabilityRevokeSubtree_rejected_atomic state authoritySlot victim victimSlot reason
    (hstate : RuntimeWellFormed state)
    (hresult : (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
      .completed (.capability (.rejected reason)))
    (hrejected : (Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot).result =
        .rejected reason) :
    (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state = state ∧
      RuntimeWellFormed
        (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state := by
  have hold := gate_subsystem_rejection_preserves_runtimeWellFormed state
    (.capabilityRevokeSubtree authoritySlot victim victimSlot)
    (.capability (.rejected reason)) hstate hresult
    (.capabilityRevokeSubtree authoritySlot victim victimSlot reason hrejected)
  exact ⟨hold.2, hold.1⟩

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

/-- Every public operation that can consult or change capability authority is
confined to the subject selected by the execution latch.  The operation data
can choose handles, slots, rights, pages, and payload words, but it cannot
supply an actor or active address space: each typed reply is the exact result
of the named subsystem transition under the authoritative kernel identity. -/
theorem authority_operations_result_sound state
    syscallCall ipcCall endpointWord sourceWord sourceKind payload rights
    source destination destinationSlot authoritySlot victim victimSlot slot page permissions
    (hmode : state.execution.mode = .running) :
    (gate state (.syscall syscallCall)).result =
        .completed (.syscall
          (Syscall.dispatch state.virtualMemory state.syscallContext syscallCall).reply) ∧
    (gate state (.ipc ipcCall)).result =
        .completed (.ipc (authoritativeIPCReply state ipcCall)) ∧
    (gate state
        (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer
          (CapabilityTransfer.offerWords state.transfers
            state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
            payload rights).result) ∧
    (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).result
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).deliveredWord) ∧
    (gate state (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability
          (Capability.copy state.capabilities
            state.execution.core.context.currentSubject source destination destinationSlot
            rights).result) ∧
    (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeSubtreeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (gate state (.map slot page permissions)).result =
        .completed (.map
          (VirtualMapping.map state.virtualMemory
            state.execution.core.context.currentSubject slot
            state.execution.core.context.activeAddressSpace page permissions).result) ∧
    (gate state (.unmap page)).result =
        .completed (.unmap
          (VirtualMapping.unmap state.virtualMemory
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).result) := by
  simp [gate, hmode, operationReply, authoritativeIPCReply]

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

private theorem dispatchHardware_running_returnAuthority_unarmed state frame
    (hmode : state.mode = .running) :
    (dispatchHardware state frame).state.returnAuthorityArmed = false := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
  generalize hdispatch : Interrupt.dispatchHardware
    { state.core with context := { state.core.context with entryActive := false } }
    frame = outcome
  cases outcome with
  | mk next action => cases action <;> simp [halt]

private theorem dispatchHardware_running_not_alreadyHalted state frame record
    (hmode : state.mode = .running) :
    (dispatchHardware state frame).action ≠ .alreadyHalted record := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
  generalize hdispatch : Interrupt.dispatchHardware
    { state.core with context := { state.core.context with entryActive := false } }
    frame = outcome
  cases outcome with
  | mk next action => cases action <;> simp [halt]

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
  have hunarmed := dispatchHardware_running_returnAuthority_unarmed
    state.execution frame hmode
  have hnotAlready record := dispatchHardware_running_not_alreadyHalted
    state.execution frame record hmode
  simp only [gate, hmode, applyOperation]
  generalize hdispatch : dispatchHardware state.execution frame = entry at hunarmed
  cases haction : entry.action with
  | contained subject =>
      simp [publishInterruptCleanup, installTerminatedResumable]
  | fatal reason => simp [installResumable]
  | timer => simpa using hunarmed
  | syscall => simpa using hunarmed
  | rejected reason => simpa using hunarmed
  | alreadyHalted record =>
      apply False.elim
      apply hnotAlready record
      rw [hdispatch]
      exact haction

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

/-- Capability delegation discharges the reusable operation obligation for
both typed outcomes.  Accepted copy uses the exact fresh subsystem state;
every denial is classified by `SubsystemRejection` and is globally atomic. -/
theorem capabilityCopy_operationPreservesRuntimeWellFormed source destination
    destinationSlot rights :
    OperationPreservesRuntimeWellFormed
      (.capabilityCopy source destination destinationSlot rights) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hcopy : Capability.copy state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_capabilityCopy_accepted_preserves_runtimeWellFormed state source
              destination destinationSlot rights next hstate hmode hcopy).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.capabilityCopy source destination destinationSlot rights)
              (.capability (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hcopy])
              (.capabilityCopy source destination destinationSlot rights reason
                (by simp [hcopy]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.capabilityCopy source destination destinationSlot rights) hstate hmode

/-- Fail-closed direct revocation is a complete operation family.  The
runtime-safe adapter converts any attempt to remove authority required by live
resources into a typed atomic rejection; every accepted removal supplies the
authority-preservation fact needed by the global invariant. -/
theorem capabilityRevoke_operationPreservesRuntimeWellFormed authoritySlot victim victimSlot :
    OperationPreservesRuntimeWellFormed
      (.capabilityRevoke authoritySlot victim victimSlot) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hrevoke : Capability.revokeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state
              authoritySlot victim victimSlot next hstate hmode hrevoke).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.capabilityRevoke authoritySlot victim victimSlot)
              (.capability (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hrevoke])
              (.capabilityRevoke authoritySlot victim victimSlot reason
                (by simp [hrevoke]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.capabilityRevoke authoritySlot victim victimSlot) hstate hmode

/-- Transitive revocation uses the same fail-closed publication rule while
clearing every descendant admitted by the capability lineage model. -/
theorem capabilityRevokeSubtree_operationPreservesRuntimeWellFormed authoritySlot victim
    victimSlot :
    OperationPreservesRuntimeWellFormed
      (.capabilityRevokeSubtree authoritySlot victim victimSlot) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hrevoke : Capability.revokeSubtreeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state
              authoritySlot victim victimSlot next hstate hmode hrevoke).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.capabilityRevokeSubtree authoritySlot victim victimSlot)
              (.capability (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hrevoke])
              (.capabilityRevokeSubtree authoritySlot victim victimSlot reason
                (by simp [hrevoke]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.capabilityRevokeSubtree authoritySlot victim victimSlot) hstate hmode

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

/-- Every public sealed-transfer offer is now a complete composite operation
family: authority/handle failures are typed atomic rejections, while success
publishes the exact pending descendant and endpoint mailbox without weakening
any runtime invariant. -/
theorem transferOffer_operationPreservesRuntimeWellFormed endpointWord sourceWord sourceKind
    payload rights :
    OperationPreservesRuntimeWellFormed
      (.transferOffer endpointWord sourceWord sourceKind payload rights) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hoffer : CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_transferOffer_accepted_preserves_runtimeWellFormed state endpointWord
              sourceWord sourceKind payload rights hstate hmode (by simp [hoffer])).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.transferOffer endpointWord sourceWord sourceKind payload rights)
              (.transferOffer (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hoffer])
              (.transferOffer endpointWord sourceWord sourceKind payload rights reason
                (by simp [hoffer]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.transferOffer endpointWord sourceWord sourceKind payload rights) hstate hmode

/-- Every public sealed-transfer receipt is a complete composite operation
family: malformed, stale, and unavailable receipts reject atomically, while a
delivery consumes the mailbox and installs authority in one globally
well-formed step. -/
theorem transferAccept_operationPreservesRuntimeWellFormed endpointWord destinationSlot :
    OperationPreservesRuntimeWellFormed
      (.transferAccept endpointWord destinationSlot) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases haccept : CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot with
    | mk next result deliveredWord =>
        cases result with
        | delivered envelope =>
            exact (gate_transferAccept_delivered_preserves_runtimeWellFormed state
              endpointWord destinationSlot envelope hstate hmode (by simp [haccept])).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.transferAccept endpointWord destinationSlot)
              (.transferAccept (.rejected reason) deliveredWord) hstate
              (by simp [gate, hmode, operationReply, haccept])
              (.transferAccept endpointWord destinationSlot reason deliveredWord
                (by simp [haccept]) (by simp [haccept]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.transferAccept endpointWord destinationSlot) hstate hmode

/-! ### Accepted termination cleanup

Subject termination is published through the authoritative resumable cleanup,
not through lifecycle synchronization alone.  Consequently the accepted gate
step removes every scheduler and saved-context reference in the same mutation
that retires the subject identity. -/

/-- Typed acceptance of subject termination exposes the cleanup facts needed
by every future operation-family preservation proof: the subject is dead,
cannot remain current or queued, has no resumable context, and no in-flight
sealed descendant survives the lifecycle teardown. -/
theorem terminateSubject_accepted_cleans_runtime_references state subject lifecycle
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.terminate state.lifecycle subject =
      { state := lifecycle, result := .accepted }) :
    (gate state (.terminateSubject subject)).result =
        .completed (.terminateSubject .accepted) ∧
      (gate state (.terminateSubject subject)).state.lifecycle.capabilities.subjects
          subject = false ∧
      subject ∉ (gate state (.terminateSubject subject)).state.scheduler.ready ∧
      (gate state (.terminateSubject subject)).state.scheduler.lifecycle.current ≠
          some subject ∧
      ResumablePreemption.contextFor
          (gate state (.terminateSubject subject)).state.resumable.contexts subject = none ∧
      (gate state (.terminateSubject subject)).state.blockingIPC.waiterEndpoint subject = none ∧
      (gate state (.terminateSubject subject)).state.blockingContexts subject = none ∧
      (∀ endpoint,
        (gate state (.terminateSubject subject)).state.transfers.pending endpoint = none) := by
  have hdead := ResumablePreemption.cleanup_terminates_subject
    state.resumable subject
  have hscheduler := ResumablePreemption.cleanup_removes_scheduler_membership
    state.resumable subject
  have hcontext := ResumablePreemption.cleanup_removes_context
    state.resumable subject
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    simp [haccepted]
  have hblockingClean := BlockingIPCContext.terminate_accepted_cleans_self
    state.blockingIPCContext subject hblockingAccepted
  simp only [gate, hmode, operationReply, applyOperation, haccepted]
  simp only [installTerminatedSubject, publishTerminatedBlockingSubject,
    hblockingAccepted, installTerminatedResumable, installTransfers,
    installResumable, installLifecycle]
  exact ⟨trivial, hdead, hscheduler.1, hscheduler.2, hcontext,
    hblockingClean.1, hblockingClean.2,
    CapabilityTransfer.cancelAllOffers_pending _⟩

/-- Accepted termination preserves both scheduler projections, including when
cleanup leaves a lone current subject with no queued peer.  Such a state is
well formed because the next resumable timer operation rejects atomically. -/
theorem gate_terminateSubject_accepted_preserves_schedulerWellFormed
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    Scheduler.WellFormed
        (gate state (.terminateSubject subject)).state.scheduler ∧
      Preemption.WellFormed
        (gate state (.terminateSubject subject)).state.preemption := by
  have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
    state.resumable subject hstate.2.2.2.2.2.2.2.2.1
  have hscheduler := hcleanup.1
  have hpreemption := hstate.2.2.2.2.2.2.2.1
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    exact haccepted
  refine ⟨?_, ?_⟩
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using hscheduler
  · rcases hpreemption with ⟨_, hticks⟩
    refine ⟨?_, ?_⟩
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
        installTransfers, installResumable, installLifecycle] using hscheduler
    · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
        publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
        installTerminatedResumable] using hticks

/-- Accepted termination preserves the saved-context bank's capacity,
uniqueness, validity, current-subject exclusion, and ready-queue agreement,
including cleanup of the final queued peer.  These are the context-specific
components of `ResumablePreemption.WellFormed`; the virtual-memory projection
is deliberately left to the resource-cleanup integration slice. -/
theorem gate_terminateSubject_accepted_preserves_resumableContextBank
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    let next := (gate state (.terminateSubject subject)).state.resumable
    next.contexts.length ≤ next.capacity ∧
      next.contexts.Pairwise (fun first second => first.owner ≠ second.owner) ∧
      (∀ context, context ∈ next.contexts →
        ResumablePreemption.validContext next context) ∧
      (∀ candidate, next.scheduler.lifecycle.current = some candidate →
        ResumablePreemption.contextFor next.contexts candidate = none) ∧
      ResumablePreemption.ReadyContextAgreement next := by
  have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
    state.resumable subject hstate.2.2.2.2.2.2.2.2.1
  rcases hcleanup with
    ⟨_, hcapacity, hunique, hvalid, habsent, hready, _, _, _, _⟩
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    exact haccepted
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using hcapacity
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using hunique
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle,
      ResumablePreemption.validContext] using hvalid
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle] using habsent
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, installTerminatedResumable,
      installTransfers, installResumable, installLifecycle,
      ResumablePreemption.ReadyContextAgreement] using hready

/-- The authoritative resumable cleanup publisher preserves the full runtime
invariant for every subject identifier.  This common boundary is used by both
explicit termination and interrupt-contained user faults. -/
private theorem installTerminatedResumable_cleanup_preserves_runtimeWellFormed
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running) :
    RuntimeWellFormed
      (installTerminatedResumable state
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  let cleaned := ResumablePreemption.cleanupSubject state.resumable subject
  have hcleanup := ResumablePreemption.cleanupSubject_preserves_wellFormed
    state.resumable subject hstate.2.2.2.2.2.2.2.2.1
  change ResumablePreemption.WellFormed cleaned at hcleanup
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  let endpoints : EndpointIPC.State :=
    { state.ipc.endpoints with
      capabilities := cleaned.scheduler.lifecycle.capabilities
      mailbox := restrictMailboxes cleaned.scheduler.lifecycle state.ipc.endpoints.mailbox }
  have hcleanVirtual := hcleanup.2.2.2.2.2.2.2.1
  have hcleanCapabilities : Capability.WellFormed
      cleaned.scheduler.lifecycle.capabilities := by
    rw [← hcleanVirtual.1]
    exact hcleanVirtual.2.2.1
  have hendpoint : EndpointIPC.WellFormed endpoints := by
    rcases hipc.2 with ⟨_oldCapabilities, hissued, hmailbox, _hdead, hhistory⟩
    refine ⟨by simpa [endpoints] using hcleanCapabilities, ?_, ?_, ?_, hhistory⟩
    · intro object hlive hkind
      have holdLive := ResumablePreemption.cleanup_live_object_was_live
        state.resumable subject object hlive
      have holdKind := ResumablePreemption.cleanup_object_kind_was_kind
        state.resumable subject object .endpoint hkind
      rw [hresumableSchedulerCoherent, hschedulerCoherent,
        ← hipcCapabilitiesCoherent] at holdLive holdKind
      exact hissued object holdLive holdKind
    · intro object envelope hnext
      cases hold : state.ipc.endpoints.mailbox object with
      | none => simp [endpoints, restrictMailboxes, hold] at hnext
      | some actual =>
          have hfacts := hnext
          have holdMailbox := hmailbox object actual hold
          simp [endpoints, restrictMailboxes, hold] at hfacts
          rcases hfacts with ⟨⟨hlive, _hliveSender⟩, rfl⟩
          obtain ⟨_holdLive, holdKind, hendpoint, hhistoryMember⟩ := holdMailbox
          exact ⟨by simpa [endpoints] using hlive,
            ResumablePreemption.cleanup_live_object_preserves_kind
              state.resumable subject object .endpoint hlive (by
                rw [hresumableSchedulerCoherent, hschedulerCoherent,
                  ← hipcCapabilitiesCoherent]
                exact holdKind),
            hendpoint, hhistoryMember⟩
    · intro object hretired
      by_cases hlive : cleaned.scheduler.lifecycle.capabilities.objects object = true
      · exact False.elim (hretired (by simpa [endpoints] using hlive))
      · cases hmail : state.ipc.endpoints.mailbox object <;>
          simp [endpoints, restrictMailboxes, hlive, hmail]
  let transferBase : CapabilityTransfer.State :=
    { state.transfers with toEndpointState := endpoints }
  let transfers := CapabilityTransfer.cancelAllOffers transferBase
  have htransfer : CapabilityTransfer.WellFormed transfers := by
    apply CapabilityTransfer.cancelAllOffers_preserves_wellFormed
    exact hendpoint
  have hfinalDead : ∀ object,
      cleaned.scheduler.lifecycle.capabilities.objects object ≠ true →
        transfers.mailbox object = none := by
    intro object hretired
    exact htransfer.1.2.2.2.1 object (by simpa [transfers, transferBase, endpoints] using hretired)
  have hfinalSender : ∀ object envelope, transfers.mailbox object = some envelope →
      cleaned.scheduler.lifecycle.capabilities.subjects envelope.sender = true := by
    intro object envelope hmail
    cases hpending : state.transfers.pending object with
    | some transfer =>
        simp [transfers, transferBase, CapabilityTransfer.cancelAllOffers,
          CapabilityTransfer.cancelWhere, hpending] at hmail
    | none =>
        cases hold : state.ipc.endpoints.mailbox object with
        | none =>
            simp [transfers, transferBase, endpoints, CapabilityTransfer.cancelAllOffers,
              CapabilityTransfer.cancelWhere, restrictMailboxes, hpending, hold] at hmail
        | some actual =>
            simp [transfers, transferBase, endpoints, CapabilityTransfer.cancelAllOffers,
              CapabilityTransfer.cancelWhere, restrictMailboxes, hpending, hold] at hmail
            rcases hmail with ⟨⟨_hlive, hsender⟩, heq⟩
            cases heq
            exact hsender
  have hfinalAuthority : ∀ candidate, cleaned.scheduler.lifecycle.current = some candidate →
      (match cleaned.scheduler.lifecycle.current with
        | some subject => { state.execution.core.context with
            currentSubject := subject, activeAddressSpace := subject }
        | none => state.execution.core.context).currentSubject = candidate ∧
      (match cleaned.scheduler.lifecycle.current with
        | some subject => { state.execution.core.context with
            currentSubject := subject, activeAddressSpace := subject }
        | none => state.execution.core.context).activeAddressSpace = candidate := by
    intro candidate hcurrent
    simp [hcurrent]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [installTerminatedResumable, CompositeState.Coherent,
      transfers, transferBase, endpoints] using
        And.intro hcleanVirtual.1
          (And.intro hfinalAuthority (And.intro hfinalDead hfinalSender))
  · rcases hexecution with ⟨_hexecutionCore, _hbound, hmodeWellFormed⟩
    refine ⟨hcleanup.1.1, by simp [installTerminatedResumable], ?_⟩
    simp [hmode] at hmodeWellFormed
    simp only [installTerminatedResumable, hmode]
    change (match cleaned.scheduler.lifecycle.current with
      | some subject => { state.execution.core.context with
          currentSubject := subject, activeAddressSpace := subject }
      | none => state.execution.core.context).entryActive = false
    cases hcurrent : cleaned.scheduler.lifecycle.current <;>
      simpa [hcurrent] using hmodeWellFormed
  · simpa [installTerminatedResumable] using hcleanup.1.1
  · simpa [installTerminatedResumable] using hcleanCapabilities
  · simpa [installTerminatedResumable] using hcleanVirtual.2
  · exact ⟨by simpa [installTerminatedResumable] using hcleanVirtual.2,
      by simpa [installTerminatedResumable, transfers, transferBase, endpoints] using htransfer.1⟩
  · simpa [installTerminatedResumable] using hcleanup.1
  · exact ⟨by simpa [installTerminatedResumable] using hcleanup.1, hpreemption.2⟩
  · simpa [installTerminatedResumable] using hcleanup
  · simpa [installTerminatedResumable, transfers, transferBase, endpoints] using htransfer
  · simpa [installTerminatedResumable, cleaned,
      ResumablePreemption.cleanupSubject] using hhalted
  · exact ⟨by simp [installTerminatedResumable], ⟨rfl, rfl⟩⟩

/-- Accepted subject termination is one complete runtime operation family:
authoritative lifecycle/resource/context cleanup and sealed-offer cancellation
are published atomically through every duplicated consumer. -/
theorem gate_terminateSubject_accepted_preserves_runtimeWellFormed
    state subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted) :
    RuntimeWellFormed (gate state (.terminateSubject subject)).state := by
  have hpreserved := installTerminatedResumable_cleanup_preserves_runtimeWellFormed
    state subject hstate hmode
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    exact haccepted
  unfold RuntimeWellFormed at hpreserved ⊢
  rcases hpreserved with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive, hblocking⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, CompositeState.Coherent] using hcoherent
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, WellFormed] using hexecution
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hlifecycle
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hcapabilities
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hvirtual
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hipc
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hscheduler
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hpreemption
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hresumable
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using htransfers
  · simpa [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable] using hhalted
  · simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, hlive]
  · simp [gate, hmode, applyOperation, haccepted, installTerminatedSubject,
      publishTerminatedBlockingSubject, hblockingAccepted, publishBlockingIPCContext,
      installTerminatedResumable, CompositeState.BlockingIPCCoherent, hblocking]

/-- Every public subject-termination request preserves the global invariant:
never-issued/already-dead subjects reject atomically, while acceptance performs
the complete lifecycle, resource, context, mailbox, and transfer cleanup. -/
theorem terminateSubject_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.terminateSubject subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hterminate : SubjectLifecycle.terminate state.lifecycle subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.terminateSubject subject) (.terminateSubject (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hterminate])
              (.terminateSubject subject reason (by simp [hterminate]))).1
        | accepted =>
            exact gate_terminateSubject_accepted_preserves_runtimeWellFormed
              state subject hstate hmode (by simp [hterminate])
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.terminateSubject subject) hstate hmode

/-! ### Scheduler rejection preservation

The raw accepted dispatch/yield/tick operations do not yet own the resumable
context-bank update needed to satisfy `RuntimeWellFormed`.  Their typed
rejections, however, are complete operation-level slices: the scheduler
transition is literally unchanged, and the composite gate publishes no
synchronization repair.  Stating these facts at the public gate boundary keeps
the accepted context-publication obligation explicit while allowing rejected
scheduler traces to compose with the already-covered operation families. -/

/-- Empty dispatch is the accepted scheduler case that needs no resumable
context publication: `selectNext` returns `accepted none` only when it retains
the exact scheduler state.  The composite gate therefore reports the typed
success while preserving every runtime projection byte-for-byte. -/
theorem scheduleNext_accepted_none_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (schedulerDispatch state).result = .accepted none) :
    RuntimeWellFormed (gate state .scheduleNext).state ∧
      (gate state .scheduleNext).state = state ∧
      (gate state .scheduleNext).result =
        .completed (.scheduler (.accepted none)) := by
  have hunchanged := schedulerDispatch_accepted_none_unchanged state haccepted
  simp [gate, hmode, applyOperation, operationReply, haccepted, hunchanged, hstate]

theorem scheduleNext_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (schedulerDispatch state).result = .rejected reason) :
    RuntimeWellFormed (gate state .scheduleNext).state ∧
      (gate state .scheduleNext).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := schedulerDispatch_rejected_unchanged state reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .scheduleNext hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

theorem scheduleYield_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (schedulerYield state).result = .rejected reason) :
    RuntimeWellFormed (gate state .scheduleYield).state ∧
      (gate state .scheduleYield).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := schedulerYield_rejected_unchanged state reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .scheduleYield hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

theorem scheduleTick_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (schedulerTick state).result = .rejected reason) :
    RuntimeWellFormed (gate state .scheduleTick).state ∧
      (gate state .scheduleTick).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := schedulerTick_rejected_unchanged state reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .scheduleTick hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

theorem terminateCurrent_rejected_preserves_runtimeWellFormed state reason
    (hstate : RuntimeWellFormed state)
    (hrejected : (Scheduler.terminateCurrent state.scheduler).result = .rejected reason) :
    RuntimeWellFormed (gate state .terminateCurrent).state ∧
      (gate state .terminateCurrent).state = state := by
  by_cases hmode : state.execution.mode = .running
  · have hunchanged := Scheduler.terminateCurrent_rejected_unchanged
      state.scheduler reason hrejected
    simp [gate, hmode, applyOperation, hrejected, hunchanged, hstate]
  · have hpreserved := gate_rejected_mode_preserves_runtimeWellFormed
      state .terminateCurrent hstate hmode
    cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => exact ⟨hpreserved, by simp [gate, hactual]⟩
    | halted record => exact ⟨hpreserved, by simp [gate, hactual]⟩

/-- Current-subject termination is the scheduler-selected spelling of the
authoritative subject-cleanup operation.  On a coherent runtime both select
the same live subject and publish the same lifecycle, resource, mailbox,
translation, and saved-context cleanup; busy and halted modes remain absorbed
by the outer gate. -/
theorem terminateCurrent_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .terminateCurrent := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hcurrent : state.scheduler.lifecycle.current with
    | none =>
        have hrejected : (Scheduler.terminateCurrent state.scheduler).result =
            .rejected .noCurrent := by
          simp [Scheduler.terminateCurrent, hcurrent, Scheduler.reject]
        exact (terminateCurrent_rejected_preserves_runtimeWellFormed
          state .noCurrent hstate hrejected).1
    | some subject =>
        have hschedulerLifecycle : state.scheduler.lifecycle = state.lifecycle :=
          hstate.1.2.1
        have hlifecycleCurrent : state.lifecycle.current = some subject := by
          rw [← hschedulerLifecycle]
          exact hcurrent
        have hsame :
            (gate state .terminateCurrent).state =
              (gate state (.terminateSubject subject)).state := by
          cases hterminate : SubjectLifecycle.terminate state.lifecycle subject with
          | mk lifecycle result =>
              cases result <;>
                simp [gate, hmode, applyOperation, Scheduler.terminateCurrent,
                  Scheduler.reject, hcurrent, hschedulerLifecycle, hlifecycleCurrent,
                  hterminate]
        rw [hsame]
        exact terminateSubject_operationPreservesRuntimeWellFormed subject state hstate
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .terminateCurrent hstate hmode

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
            · exact ⟨by simp [installSchedulerRemoval], ⟨rfl, rfl⟩⟩
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.scheduleRemove subject) hstate hmode

/-- Accepted capability revocation composes with authoritative resumable-aware
scheduler removal.  In particular, the scheduler/lifecycle cleanup step starts
from the exact globally well-formed capability post-state rather than a stale
pre-revocation projection. -/
theorem capabilityRevoke_then_scheduleRemove_preserves_runtimeWellFormed state authoritySlot
    victim victimSlot capabilities subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := capabilities, result := .accepted }) :
    RuntimeWellFormed (runOperations state
      [.capabilityRevoke authoritySlot victim victimSlot, .scheduleRemove subject]) := by
  simp only [runOperations]
  apply scheduleRemove_operationPreservesRuntimeWellFormed subject
  exact (gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state authoritySlot victim
    victimSlot capabilities hstate hmode haccepted).1

/-- Transitive lineage revocation has the same scheduler/lifecycle composition
boundary: all capability consumers observe the accepted subtree post-state
before resumable context and active-translation cleanup executes. -/
theorem capabilityRevokeSubtree_then_scheduleRemove_preserves_runtimeWellFormed state
    authoritySlot victim victimSlot capabilities subject
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := capabilities, result := .accepted }) :
    RuntimeWellFormed (runOperations state
      [.capabilityRevokeSubtree authoritySlot victim victimSlot, .scheduleRemove subject]) := by
  simp only [runOperations]
  apply scheduleRemove_operationPreservesRuntimeWellFormed subject
  exact (gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state authoritySlot
    victim victimSlot capabilities hstate hmode haccepted).1

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
                rw [hcoherent.2.1] at habsent htranslation hkinds
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
              · exact ⟨by simp [installCreatedSubject], ⟨rfl, rfl⟩⟩
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.createSubject subject) hstate hmode

/-- Composite queue admission can report success only when the inserted
subject's kernel-owned context was already staged in the pre-state. -/
theorem gate_scheduleAdd_accepted_runtimeWellFormed_requires_staged_context
    state subject context next
    (_hmode : state.execution.mode = .running)
    (haccepted : schedulerAdmission state subject =
      { state := next, result := .accepted context }) :
    ∃ saved, saved ∈ state.resumable.contexts ∧ saved.owner = subject := by
  exact (schedulerAdmission_accepted_exact state subject context next haccepted).2

/-- Queue admission retains the authoritative lifecycle and appends exactly
the admitted subject.  These small projections keep the composite proof from
depending on the validation order inside `Scheduler.add`. -/
private theorem schedulerAdd_accepted_projections state subject context next
    (haccepted : Scheduler.add state subject =
      { state := next, result := .accepted context }) :
    next.lifecycle = state.lifecycle ∧ next.ready = state.ready ++ [subject] := by
  simp only [Scheduler.add] at haccepted
  split at haccepted <;> try simp_all [Scheduler.reject]
  split at haccepted <;> try simp_all [Scheduler.reject]
  split at haccepted <;> try simp_all [Scheduler.reject]
  next addressSpace hspace =>
    split at haccepted <;> try simp_all [Scheduler.reject]
    split at haccepted <;> try simp_all [Scheduler.reject]
    rcases haccepted with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Accepted queue admission preserves the complete runtime invariant when
the subject's kernel-owned initial context was staged before admission.  The
narrow publication step changes no lifecycle, resource, mailbox, translation,
or execution projection and adds the staged context owner to the ready queue
observed by both scheduler consumers. -/
theorem gate_scheduleAdd_accepted_preserves_runtimeWellFormed
    state subject context next saved
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context })
    (hsaved : saved ∈ state.resumable.contexts ∧ saved.owner = subject) :
    RuntimeWellFormed (gate state (.scheduleAdd subject)).state ∧
      (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.accepted context)) := by
  have hadmission : schedulerAdmission state subject =
      { state := next, result := .accepted context } := by
    rw [schedulerAdmission_eq_add_of_staged state subject saved hsaved, haccepted]
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  obtain ⟨hlifecycleNext, hreadyNext⟩ :=
    schedulerAdd_accepted_projections state.scheduler subject context next haccepted
  have hscheduler' : Scheduler.WellFormed next := by
    have hold := Scheduler.add_preserves_wellFormed state.scheduler subject hscheduler
    simpa [haccepted] using hold
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with scheduler := next } := by
    rcases hresumable with
      ⟨_hscheduler, hcapacity, hunique, hvalid, habsent,
        ⟨hreadyContexts, hsuspendedReady⟩,
        htranslation, hvirtualAgreement, hkinds, htlb⟩
    rw [hresumableSchedulerCoherent] at hreadyContexts hsuspendedReady
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, htlb⟩
    · intro candidate hcandidate
      have hold := hvalid candidate hcandidate
      simpa [ResumablePreemption.validContext, hlifecycleNext,
        hresumableSchedulerCoherent] using hold
    · intro current hcurrent
      apply habsent current
      simpa [hlifecycleNext, hresumableSchedulerCoherent] using hcurrent
    · refine ⟨?_, ?_⟩
      · intro candidate hmember
        rw [hreadyNext] at hmember
        rcases List.mem_append.mp hmember with hold | hold
        · exact hreadyContexts candidate hold
        · simp only [List.mem_singleton] at hold
          subst candidate
          exact ⟨saved, hsaved.1, hsaved.2⟩
      · intro candidate hcandidate hsuspended
        rw [hreadyNext]
        exact List.mem_append_left _ (hsuspendedReady candidate hcandidate hsuspended)
    · rcases htranslation with ⟨howner, hactive⟩
      refine ⟨?_, ?_⟩
      · simpa [hlifecycleNext, hresumableSchedulerCoherent] using howner
      · simpa [hlifecycleNext, hresumableSchedulerCoherent] using hactive
    · rcases hvirtualAgreement with ⟨hcapabilities, hwellFormed⟩
      exact ⟨by simpa [hlifecycleNext, hresumableSchedulerCoherent] using hcapabilities,
        hwellFormed⟩
    · rcases hkinds with ⟨hmemory, hendpoint⟩
      refine ⟨?_, ?_⟩
      · intro object owner frame howned
        have hold := hmemory object owner frame (by
          simpa [hlifecycleNext, hresumableSchedulerCoherent] using howned)
        simpa [hlifecycleNext, hresumableSchedulerCoherent] using hold
      · intro object owner howned
        have hold := hendpoint object owner (by
          simpa [hlifecycleNext, hresumableSchedulerCoherent] using howned)
        simpa [hlifecycleNext, hresumableSchedulerCoherent] using hold
  have hcoherent' : (installSchedulerAdmission state next).Coherent := by
    simp only [installSchedulerAdmission, CompositeState.Coherent]
    refine ⟨hexecutionCoherent, ?_, trivial, hcapabilitiesCoherent,
      hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, trivial, hresumableVirtualCoherent,
      htransfersCoherent, hauthorityCoherent, hdeadMailbox, hliveSender⟩
    rw [hlifecycleNext, hschedulerCoherent]
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler := next } :=
    ⟨hscheduler', hpreemption.2⟩
  constructor
  · simp only [gate, hmode, applyOperation, hadmission]
    exact ⟨hcoherent', hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler', hpreemption', hresumable', htransfers, hhalted,
      hlive.1, by simp [installSchedulerAdmission,
        CompositeState.BlockingIPCCoherent, hlifecycleNext, hschedulerCoherent]⟩
  · simp [gate, hmode, operationReply, hadmission]

/-- Negative admission regression: an otherwise accepted raw insertion cannot
cross the composite gate without its kernel-owned resumable context. -/
theorem scheduleAdd_missing_context_rejected_atomic state subject context next
    (hmode : state.execution.mode = .running)
    (hadd : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context })
    (hmissing : ResumablePreemption.contextFor state.resumable.contexts subject = none) :
    (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.rejected .noResumableContext)) ∧
      (gate state (.scheduleAdd subject)).state = state := by
  simp [gate, hmode, operationReply, applyOperation, schedulerAdmission,
    hadd, hmissing, Scheduler.reject]

/-- Queue admission is a complete public operation family: raw scheduler
rejections and missing-context integration failures are atomic, while every
reported success publishes the exact staged context owner to both scheduler
consumers and preserves the complete runtime invariant. -/
theorem scheduleAdd_operationPreservesRuntimeWellFormed subject :
    OperationPreservesRuntimeWellFormed (.scheduleAdd subject) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hadmission : schedulerAdmission state subject with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.scheduleAdd subject) (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hadmission])
              (.scheduleAdd subject reason (by simp [hadmission]))).1
        | accepted context =>
            obtain ⟨hadd, saved, hmember, howner⟩ :=
              schedulerAdmission_accepted_exact state subject context next hadmission
            exact (gate_scheduleAdd_accepted_preserves_runtimeWellFormed
              state subject context next saved hstate hmode hadd ⟨hmember, howner⟩).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.scheduleAdd subject) hstate hmode

/-- Raw dispatch is a complete operation family at the composite boundary:
empty selection succeeds without mutation, while a selection that would need
context restoration is rejected atomically. -/
theorem scheduleNext_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .scheduleNext := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hdispatch : schedulerDispatch state with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              .scheduleNext (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hdispatch])
              (.scheduleNext reason (by simp [hdispatch]))).1
        | accepted context =>
            have hnone := schedulerDispatch_accepted_is_none state context (by
              simp [hdispatch])
            subst context
            exact (scheduleNext_accepted_none_preserves_runtimeWellFormed
              state hstate hmode (by simp [hdispatch])).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .scheduleNext hstate hmode

/-- Raw yield cannot mutate without the outgoing saved context, so every
running result is a typed atomic rejection and every non-running result is
absorbed by the outer gate. -/
theorem scheduleYield_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .scheduleYield := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hyield : schedulerYield state with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              .scheduleYield (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hyield])
              (.scheduleYield reason (by simp [hyield]))).1
        | accepted context =>
            exact False.elim ((schedulerYield_ne_accepted state context) (by
              simp [hyield]))
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .scheduleYield hstate hmode

/-- Raw tick is confined to the same atomic missing-save rejection as yield;
timer-driven switching is provided by `resumePreempt`. -/
theorem scheduleTick_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .scheduleTick := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases htick : schedulerTick state with
    | mk next result =>
        cases result with
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              .scheduleTick (.scheduler (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, htick])
              (.scheduleTick reason (by simp [htick]))).1
        | accepted context =>
            exact False.elim ((schedulerTick_ne_accepted state context) (by
              simp [htick]))
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      .scheduleTick hstate hmode

private theorem schedulerSelectNext_preserves_capabilities scheduler :
    (Scheduler.selectNext scheduler).state.lifecycle.capabilities =
      scheduler.lifecycle.capabilities := by
  unfold Scheduler.selectNext
  split <;> try simp [Scheduler.reject]
  all_goals split <;> simp [Scheduler.reject]

private theorem schedulerTick_preserves_capabilities scheduler :
    (Scheduler.tick scheduler).state.lifecycle.capabilities =
      scheduler.lifecycle.capabilities := by
  unfold Scheduler.tick Scheduler.yield
  split
  · simp [Scheduler.reject]
  next subject hcurrent =>
    split
    · simp [Scheduler.reject]
    · let staged : Scheduler.State :=
        { scheduler with
          ready := scheduler.ready ++ [subject]
          lifecycle := { scheduler.lifecycle with current := none } }
      generalize hselect : Scheduler.selectNext staged = outcome
      cases outcome with
      | mk next result =>
          cases result with
          | rejected reason => simp [Scheduler.reject]
          | accepted context =>
              have hcapabilities : next.lifecycle.capabilities =
                  staged.lifecycle.capabilities := by
                have hstate := congrArg
                  (fun outcome => outcome.state.lifecycle.capabilities) hselect
                rw [schedulerSelectNext_preserves_capabilities] at hstate
                exact hstate.symm
              simpa [staged] using hcapabilities

private theorem resumeSwitch_preserves_capabilities (state : CompositeState) frame registers
    (hcoherent : state.Coherent) :
    ((ResumablePreemption.switch state.resumable state.execution.core frame registers).state.scheduler.lifecycle.capabilities) =
      state.lifecycle.capabilities := by
  have hprojection : state.resumable.scheduler.lifecycle.capabilities =
      state.lifecycle.capabilities := by
    rw [hcoherent.2.2.2.2.2.2.2.1, hcoherent.2.1]
  simp only [ResumablePreemption.switch]
  split <;> try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals
    rw [schedulerTick_preserves_capabilities]
    exact hprojection

private theorem resumeSwitch_preserves_virtualMemory (state : CompositeState) frame registers
    (hcoherent : state.Coherent) :
    ((ResumablePreemption.switch state.resumable state.execution.core frame registers).state.translations.virtual) =
      state.virtualMemory := by
  have hprojection : state.resumable.translations.virtual = state.virtualMemory := by
    exact hcoherent.2.2.2.2.2.2.2.2.1
  simp only [ResumablePreemption.switch]
  split <;> try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals simpa [TLB.switch] using hprojection

private theorem resumeSwitch_halted_preserves_scheduler state interrupt frame registers
    (hhalted : (ResumablePreemption.switch state interrupt frame registers).state.halted = true) :
    (ResumablePreemption.switch state interrupt frame registers).state.scheduler =
      state.scheduler := by
  simp only [ResumablePreemption.switch] at hhalted ⊢
  split <;> try simp_all [ResumablePreemption.reject]
  split <;> try simp_all [ResumablePreemption.reject, ResumablePreemption.halt]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> simp_all [ResumablePreemption.reject]

/-- Publishing a nonterminal save/select/restore result preserves every
runtime projection.  The resumable model owns the scheduler and translation
updates; this boundary republishes those authoritative views without changing
capability authority, IPC mailboxes, or transfer state. -/
private theorem installResumable_nonfatal_preserves_runtimeWellFormed state next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hnext : ResumablePreemption.WellFormed next)
    (hcapabilities : next.scheduler.lifecycle.capabilities =
      state.lifecycle.capabilities)
    (hvirtual : next.translations.virtual = state.virtualMemory)
    (hhalted : next.halted = false) :
    RuntimeWellFormed (installResumable state next) := by
  rcases hstate with
    ⟨hcoherent, hexecution, _hlifecycle, hcapabilityWellFormed,
      hvirtualWellFormed, hipc, _hscheduler, hpreemption, _hresumable,
      htransfers, _hterminal, _hlive⟩
  rcases hcoherent with
    ⟨_hexecutionLifecycle, hschedulerLifecycle, _hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, _hresumableScheduler, _htranslationVirtual,
      htransferEndpoints, _hauthority, hdeadMailbox, hliveSender⟩
  have hscheduler' : Scheduler.WellFormed next.scheduler := hnext.1
  have hlifecycle' : SubjectLifecycle.WellFormed next.scheduler.lifecycle :=
    hscheduler'.1
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with
          lifecycle := next.scheduler.lifecycle
          context := match next.scheduler.lifecycle.current with
            | some subject => { state.execution.core.context with
                currentSubject := subject, activeAddressSpace := subject }
            | none => state.execution.core.context }
        returnAuthorityArmed := false } := by
    refine ⟨?_, by simp, ?_⟩
    · exact hlifecycle'
    · cases hcurrent : next.scheduler.lifecycle.current <;>
        simpa [hcurrent, hmode] using hexecution.2.2
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler := next.scheduler } :=
    ⟨hscheduler', hpreemption.2⟩
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with virtualMemory := state.virtualMemory } := by
    rw [← hipcVirtual]
    exact hipc
  have hcoherent' : (installResumable state next).Coherent := by
    simp [CompositeState.Coherent, installResumable, hvirtual, hcapabilities,
      hmemoryCapabilities, hipcCapabilities, htransferEndpoints,
      hdeadMailbox, hliveSender]
    refine ⟨?_, ?_, ?_⟩
    · intro subject hcurrent
      simp [hcurrent]
    · intro object hdead
      exact hdeadMailbox object (by simp [hdead])
    · exact hliveSender
  refine ⟨hcoherent', hexecution', hlifecycle', ?_, ?_, ?_, hscheduler',
    hpreemption', hnext, htransfers, ?_, ?_⟩
  · simpa [installResumable, hcapabilities, hcapabilitiesLifecycle] using
      hcapabilityWellFormed
  · simpa [installResumable, hvirtual] using hvirtualWellFormed
  · simpa [installResumable, hvirtual] using hipc'
  · simp [installResumable, hhalted, hmode]
  · exact ⟨by simp [installResumable], ⟨rfl, rfl⟩⟩

/-- Every nonfatal resumable preemption step preserves the complete global
runtime invariant.  This includes successful save/select/restore as well as
all typed, state-preserving precondition failures; attacker-controlled frame
and register payloads cannot desynchronize the selected execution identity. -/
theorem gate_resumePreempt_nonfatal_preserves_runtimeWellFormed state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = false) :
    RuntimeWellFormed (gate state (.resumePreempt frame registers)).state := by
  have hnext := ResumablePreemption.switch_preserves_wellFormed
    state.resumable state.execution.core frame registers
      hstate.2.2.2.2.2.2.2.2.1
  have hcapabilities := resumeSwitch_preserves_capabilities state frame registers
    hstate.1
  have hvirtual := resumeSwitch_preserves_virtualMemory state frame registers
    hstate.1
  have hpublished := installResumable_nonfatal_preserves_runtimeWellFormed state
    (ResumablePreemption.switch state.resumable state.execution.core frame registers).state
    hstate hmode hnext hcapabilities hvirtual hhalted
  cases herror : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).error with
  | none => simpa [gate, hmode, applyOperation, herror] using hpublished
  | some reason =>
      cases reason <;> simp [gate, hmode, applyOperation, herror, hhalted, hstate]

private theorem resumeSwitch_halted_requires_fatal_dispatch state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    ∃ reason, (Interrupt.dispatchHardware state.execution.core frame).action =
      .fatal reason := by
  have hresumable : state.resumable.halted = false := by
    cases hvalue : state.resumable.halted with
    | false => rfl
    | true =>
        obtain ⟨record, hrecord⟩ := hstate.2.2.2.2.2.2.2.2.2.2.1.mp hvalue
        rw [hmode] at hrecord
        contradiction
  simp only [ResumablePreemption.switch, hresumable, Bool.false_eq_true, if_false]
    at hhalted
  generalize hdispatch : Interrupt.dispatchHardware state.execution.core frame = outcome
    at hhalted
  cases outcome with
  | mk next action =>
      cases action with
      | fatal reason =>
          exact ⟨reason, rfl⟩
      | contained subject =>
          simp [ResumablePreemption.reject, hresumable] at hhalted
      | timer =>
          simp only at hhalted
          split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> simp_all [ResumablePreemption.reject]
      | syscall =>
          simp [ResumablePreemption.reject, hresumable] at hhalted
      | rejected reason =>
          simp [ResumablePreemption.reject, hresumable] at hhalted

private theorem resumeSwitch_halted_state_eq state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    (ResumablePreemption.switch state.resumable state.execution.core frame registers).state =
      { state.resumable with halted := true } := by
  obtain ⟨reason, hfatal⟩ := resumeSwitch_halted_requires_fatal_dispatch
    state frame registers hstate hmode hhalted
  have hresumable : state.resumable.halted = false := by
    cases hvalue : state.resumable.halted with
    | false => rfl
    | true =>
        obtain ⟨record, hrecord⟩ := hstate.2.2.2.2.2.2.2.2.2.2.1.mp hvalue
        rw [hmode] at hrecord
        contradiction
  simp [ResumablePreemption.switch, hresumable, hfatal, ResumablePreemption.halt]

private theorem fatalInterrupt_dispatchHardware_halts execution frame reason
    (hmode : execution.mode = .running)
    (hentry : execution.core.context.entryActive = false)
    (hfatal : (Interrupt.dispatchHardware execution.core frame).action = .fatal reason) :
    ∃ record, (dispatchHardware execution frame).state.mode = .halted record := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
  have hprepared :
      { execution.core with context :=
        { execution.core.context with entryActive := false } } = execution.core := by
    cases hcore : execution.core with
    | mk lifecycle context =>
        cases hcontext : context with
        | mk current space stack active => simp_all
  rw [hprepared]
  generalize hdispatch : Interrupt.dispatchHardware execution.core frame = outcome
    at hfatal ⊢
  cases outcome with
  | mk next action =>
      cases action <;> simp_all [halt]

private theorem dispatchHardware_preserves_wellFormed_internal state frame
    (hstate : WellFormed state) :
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
              | kernel =>
                  simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
              | user =>
                  simpa [hvector, WellFormed, Interrupt.WellFormed] using
                    SubjectLifecycle.terminateState_preserves_wellFormed
                      state.core.lifecycle state.core.context.currentSubject hlifecycle
          | timer => simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
          | syscall =>
              cases frame.savedPrivilege <;>
                simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle

private theorem dispatchHardware_fatal_halts state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    ∃ record, (dispatchHardware state frame).state.mode = .halted record := by
  cases hmode : state.mode with
  | handling active =>
      simp [dispatchHardware, hmode, halt] at hfatal ⊢
  | halted record =>
      simp [dispatchHardware, hmode] at hfatal
  | running =>
      simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry] at hfatal ⊢
      generalize hdispatch : Interrupt.dispatchHardware
        { state.core with context := { state.core.context with entryActive := false } }
        frame = outcome at hfatal ⊢
      cases outcome with
      | mk next action => cases action <;> simp_all [halt]

private theorem interruptDispatch_ordinary_state state frame
    (hordinary : (Interrupt.dispatchHardware state frame).action = .timer ∨
      (Interrupt.dispatchHardware state frame).action = .syscall ∨
      ∃ reason, (Interrupt.dispatchHardware state frame).action = .rejected reason) :
    (Interrupt.dispatchHardware state frame).state = state := by
  unfold Interrupt.dispatchHardware at hordinary ⊢
  by_cases hentry : state.context.entryActive
  · simp [hentry] at hordinary
  · simp only [hentry, Bool.false_eq_true, ↓reduceIte] at hordinary ⊢
    cases hvector : Interrupt.decodeVector frame.vector with
    | none => simp [hvector] at hordinary
    | some vector =>
        cases vector with
        | pageFault =>
            cases hprivilege : frame.savedPrivilege <;>
              simp [hvector, hprivilege] at hordinary
        | timer => simp [hvector]
        | syscall =>
            cases hprivilege : frame.savedPrivilege <;>
              simp [hvector, hprivilege] at hordinary ⊢

private theorem dispatchHardware_ordinary_state state frame
    (hmode : state.mode = .running)
    (hentry : state.core.context.entryActive = false)
    (hordinary : (dispatchHardware state frame).action = .timer ∨
      (dispatchHardware state frame).action = .syscall ∨
      ∃ reason, (dispatchHardware state frame).action = .rejected reason) :
    (dispatchHardware state frame).state =
      { state with returnAuthorityArmed := false, copyOverride := false } := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry] at hordinary ⊢
  have hprepared :
      { state.core with context := { state.core.context with entryActive := false } } =
        state.core := by
    cases hcore : state.core with
    | mk lifecycle context =>
        cases hcontext : context with
        | mk current space stack active => simp_all
  rw [hprepared] at hordinary ⊢
  generalize hdispatch : Interrupt.dispatchHardware state.core frame = outcome
    at hordinary ⊢
  cases outcome with
  | mk next action =>
      cases action with
      | fatal reason => simp [halt] at hordinary
      | contained subject => simp at hordinary
      | timer =>
          have hcore := interruptDispatch_ordinary_state state.core frame
            (Or.inl (by rw [hdispatch]))
          simp_all
      | syscall =>
          have hcore := interruptDispatch_ordinary_state state.core frame
            (Or.inr (Or.inl (by rw [hdispatch])))
          simp_all
      | rejected reason =>
          have hcore := interruptDispatch_ordinary_state state.core frame
            (Or.inr (Or.inr ⟨reason, by rw [hdispatch]⟩))
          simp_all

/-- Closing the kernel-owned copy window changes no component of the global
runtime invariant. -/
private theorem closeCopyWindow_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed
      { state with execution := { state.execution with copyOverride := false } } := by
  unfold RuntimeWellFormed CompositeState.Coherent WellFormed ReturnAuthorityBound
    CompositeState.ReturnPlanLive CompositeState.BlockingIPCCoherent at hstate ⊢
  simpa using hstate

/-- Completed ordinary inbound entry clears transient return and copy
authority without changing any authoritative subsystem state. -/
private theorem clearInboundAuthority_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed
      { state with execution :=
          { state.execution with returnAuthorityArmed := false, copyOverride := false } } := by
  have hclosed := closeCopyWindow_preserves_runtimeWellFormed state hstate
  unfold RuntimeWellFormed CompositeState.Coherent WellFormed at hclosed ⊢
  rcases hclosed with
    ⟨hcoherent, ⟨hcore, _hbound, hentry⟩, hlifecycle, hcapabilities,
      hvirtual, hipc, hscheduler, hpreemption, hresumable, htransfers,
      hterminal, hlive⟩
  exact ⟨hcoherent, ⟨hcore, by simp, hentry⟩, hlifecycle, hcapabilities,
    hvirtual, hipc, hscheduler, hpreemption, hresumable, htransfers,
    hterminal, ⟨by simp, by simpa [CompositeState.BlockingIPCCoherent] using hlive.2⟩⟩

private theorem installResumable_fatal_preserves_runtimeWellFormed state entry
    (hstate : RuntimeWellFormed state)
    (hentry : WellFormed entry)
    (hentryMode : ∃ record, entry.mode = .halted record) :
    RuntimeWellFormed
      (installResumable { state with execution := entry }
        { state.resumable with halted := true }) := by
  rcases hstate with
    ⟨hcoherent, _hexecution, hlifecycle, hcapabilityWellFormed,
      hvirtualWellFormed, hipc, hschedulerWellFormed, hpreemption, _hresumable,
      htransfers, _hterminal, _hlive⟩
  rcases hcoherent with
    ⟨hexecutionLifecycle, hschedulerLifecycle, hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, hresumableScheduler, htranslationVirtual,
      htransferEndpoints, hauthority, hdeadMailbox, hliveSender⟩
  rcases hentry with ⟨_hentryCore, _hentryBound, hentryWellFormed⟩
  obtain ⟨record, hrecord⟩ := hentryMode
  have hentryExecution : WellFormed
      { entry with
        core := { entry.core with
          lifecycle := state.resumable.scheduler.lifecycle
          context := match state.resumable.scheduler.lifecycle.current with
            | some subject => { entry.core.context with
                currentSubject := subject, activeAddressSpace := subject }
            | none => entry.core.context }
        returnAuthorityArmed := false } := by
    refine ⟨?_, by simp, ?_⟩
    · simpa [Interrupt.WellFormed, hresumableScheduler, hschedulerLifecycle] using
        hlifecycle
    · rw [hrecord]
      cases hcurrent : state.resumable.scheduler.lifecycle.current <;>
        simpa [hcurrent, hrecord] using hentryWellFormed
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with virtualMemory := state.virtualMemory } := by
    rw [← hipcVirtual]
    exact hipc
  have hcoherent' :
      (installResumable { state with execution := entry }
        { state.resumable with halted := true }).Coherent := by
    simp [CompositeState.Coherent, installResumable, hresumableScheduler,
      htranslationVirtual, hschedulerLifecycle, hcapabilitiesLifecycle, hmemoryCapabilities,
      hipcCapabilities, htransferEndpoints, hdeadMailbox, hliveSender]
    refine ⟨?_, ?_, ?_⟩
    · intro subject hcurrent
      simp [hcurrent]
    · intro object hdead
      exact hdeadMailbox object (by simpa [hschedulerLifecycle] using hdead)
    · intro object envelope hmailbox
      exact hliveSender object envelope hmailbox
  refine ⟨hcoherent', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htransfers, ?_, ?_⟩
  · simpa [installResumable] using hentryExecution
  · simpa [installResumable, hresumableScheduler, hschedulerLifecycle] using hlifecycle
  · simpa [installResumable, hresumableScheduler, hschedulerLifecycle,
      hcapabilitiesLifecycle] using
      hcapabilityWellFormed
  · simpa [installResumable, htranslationVirtual] using hvirtualWellFormed
  · simpa [installResumable, htranslationVirtual] using hipc'
  · simpa [installResumable, hresumableScheduler] using hschedulerWellFormed
  · simpa [installResumable, hresumableScheduler, Preemption.WellFormed] using
      (And.intro hschedulerWellFormed hpreemption.2)
  · simpa [installResumable] using
      (ResumablePreemption.wellFormed_set_halted state.resumable true).2 _hresumable
  · simp [installResumable, hrecord]
  · exact ⟨by simp [installResumable], ⟨rfl, rfl⟩⟩

/-- A resumable-model fatal entry latches the same typed composite fail-stop
mode while freezing the scheduler, context bank, translations, IPC, and
authority projections. -/
theorem gate_resumePreempt_fatal_preserves_runtimeWellFormed state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    RuntimeWellFormed (gate state (.resumePreempt frame registers)).state := by
  obtain ⟨reason, hfatal⟩ := resumeSwitch_halted_requires_fatal_dispatch
    state frame registers hstate hmode hhalted
  have hentryActive : state.execution.core.context.entryActive = false := by
    simpa [hmode] using hstate.2.1.2.2
  have hentryMode := fatalInterrupt_dispatchHardware_halts state.execution frame reason
    hmode hentryActive hfatal
  have hentryWellFormed : WellFormed (dispatchHardware state.execution frame).state := by
    rcases hstate.2.1 with ⟨hlifecycle, hbound, hmodeWellFormed⟩
    simp only [hmode] at hmodeWellFormed
    simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
    unfold Interrupt.dispatchHardware
    cases hvector : Interrupt.decodeVector frame.vector with
    | none => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
    | some vector =>
        cases vector with
        | pageFault =>
            cases frame.savedPrivilege with
            | kernel =>
                simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
            | user =>
                simpa [hvector, WellFormed, Interrupt.WellFormed] using
                  SubjectLifecycle.terminateState_preserves_wellFormed
                    state.execution.core.lifecycle
                    state.execution.core.context.currentSubject hlifecycle
        | timer => simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
        | syscall =>
            cases frame.savedPrivilege <;>
              simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
  have hnext := resumeSwitch_halted_state_eq state frame registers hstate hmode hhalted
  have herror := ResumablePreemption.halted_reports_fatalEntry
    state.resumable state.execution.core frame registers hhalted
  have hpublished := installResumable_fatal_preserves_runtimeWellFormed state
    (dispatchHardware state.execution frame).state
    hstate hentryWellFormed hentryMode
  simpa [gate, hmode, applyOperation, herror, hhalted, hnext] using hpublished

/-- Resumable preemption is now a complete composite operation family:
successful switches, typed nonfatal rejection, fatal latching, and outer-gate
absorption all preserve the global runtime invariant. -/
theorem resumePreempt_operationPreservesRuntimeWellFormed frame registers :
    OperationPreservesRuntimeWellFormed (.resumePreempt frame registers) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hhalted : (ResumablePreemption.switch state.resumable
        state.execution.core frame registers).state.halted
    · exact gate_resumePreempt_nonfatal_preserves_runtimeWellFormed
        state frame registers hstate hmode hhalted
    · exact gate_resumePreempt_fatal_preserves_runtimeWellFormed
        state frame registers hstate hmode hhalted
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.resumePreempt frame registers) hstate hmode

/-! ### Inbound interrupt preservation -/

/-- Every normalized hardware frame is a complete composite operation family.
Contained user faults reuse authoritative termination cleanup, fatal entry
synchronizes both halt latches, and ordinary timer/syscall/rejection entry only
closes transient return/copy authority.  No branch repairs an unrelated
projection of an invalid pre-state. -/
theorem interrupt_operationPreservesRuntimeWellFormed frame :
    OperationPreservesRuntimeWellFormed (.interrupt frame) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · have hentryActive : state.execution.core.context.entryActive = false := by
      simpa [hmode] using hstate.2.1.2.2
    let entry := dispatchHardware state.execution frame
    have hentryWellFormed : WellFormed entry.state := by
      exact dispatchHardware_preserves_wellFormed_internal
        state.execution frame hstate.2.1
    cases haction : entry.action with
    | contained subject =>
        have hcleaned := installTerminatedResumable_cleanup_preserves_runtimeWellFormed
          state subject hstate hmode
        have hclosed := closeCopyWindow_preserves_runtimeWellFormed
          (installTerminatedResumable state
            (ResumablePreemption.cleanupSubject state.resumable subject)) hcleaned
        simpa [gate, hmode, applyOperation, entry, haction, publishInterruptCleanup] using
          hclosed
    | fatal reason =>
        have hentryMode : ∃ record, entry.state.mode = .halted record := by
          apply dispatchHardware_fatal_halts state.execution frame reason
          simpa [entry] using haction
        have hpublished := installResumable_fatal_preserves_runtimeWellFormed
          state entry.state hstate hentryWellFormed hentryMode
        simpa [gate, hmode, applyOperation, entry, haction] using hpublished
    | timer =>
        have hordinary := dispatchHardware_ordinary_state state.execution frame
          hmode hentryActive (Or.inl (by simpa [entry] using haction))
        have hcleared := clearInboundAuthority_preserves_runtimeWellFormed state hstate
        simpa [gate, hmode, applyOperation, entry, haction, hordinary] using hcleared
    | syscall =>
        have hordinary := dispatchHardware_ordinary_state state.execution frame
          hmode hentryActive (Or.inr (Or.inl (by simpa [entry] using haction)))
        have hcleared := clearInboundAuthority_preserves_runtimeWellFormed state hstate
        simpa [gate, hmode, applyOperation, entry, haction, hordinary] using hcleared
    | rejected reason =>
        have hordinary := dispatchHardware_ordinary_state state.execution frame
          hmode hentryActive (Or.inr (Or.inr ⟨reason, by simpa [entry] using haction⟩))
        have hcleared := clearInboundAuthority_preserves_runtimeWellFormed state hstate
        simpa [gate, hmode, applyOperation, entry, haction, hordinary] using hcleared
    | alreadyHalted record =>
        have hnotAlready := dispatchHardware_running_not_alreadyHalted
          state.execution frame record hmode
        exact False.elim (hnotAlready (by simpa [entry] using haction))
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.interrupt frame) hstate hmode

/-! ### Complete runtime operation inventory

The constructors below inventory every operation family whose accepted and
rejected results have complete global-preservation proofs.  The legacy
scheduler-only preemption constructor has been retired in favor of
`resumePreempt`, whose input carries the outgoing frame/register payload needed
to update the authoritative context bank atomically. -/

inductive RuntimeTraceOperation : Operation → Prop where
  | interrupt frame : RuntimeTraceOperation (.interrupt frame)
  | selectUserReturn purpose : RuntimeTraceOperation (.selectUserReturn purpose)
  | userReturn request : RuntimeTraceOperation (.userReturn request)
  | syscall call : RuntimeTraceOperation (.syscall call)
  | ipc call : RuntimeTraceOperation (.ipc call)
  | resumePreempt frame registers :
      RuntimeTraceOperation (.resumePreempt frame registers)
  | transferOffer endpointWord sourceWord sourceKind payload rights :
      RuntimeTraceOperation
        (.transferOffer endpointWord sourceWord sourceKind payload rights)
  | transferAccept endpointWord destinationSlot :
      RuntimeTraceOperation (.transferAccept endpointWord destinationSlot)
  | capabilityCopy source destination destinationSlot rights :
      RuntimeTraceOperation
        (.capabilityCopy source destination destinationSlot rights)
  | capabilityRevoke authoritySlot victim victimSlot :
      RuntimeTraceOperation (.capabilityRevoke authoritySlot victim victimSlot)
  | capabilityRevokeSubtree authoritySlot victim victimSlot :
      RuntimeTraceOperation (.capabilityRevokeSubtree authoritySlot victim victimSlot)
  | map slot page permissions : RuntimeTraceOperation (.map slot page permissions)
  | unmap page : RuntimeTraceOperation (.unmap page)
  | createSubject subject : RuntimeTraceOperation (.createSubject subject)
  | terminateSubject subject : RuntimeTraceOperation (.terminateSubject subject)
  | scheduleAdd subject : RuntimeTraceOperation (.scheduleAdd subject)
  | scheduleRemove subject : RuntimeTraceOperation (.scheduleRemove subject)
  | scheduleNext : RuntimeTraceOperation .scheduleNext
  | scheduleYield : RuntimeTraceOperation .scheduleYield
  | scheduleTick : RuntimeTraceOperation .scheduleTick
  | terminateCurrent : RuntimeTraceOperation .terminateCurrent
  | restart : RuntimeTraceOperation .restart

/-- Every operation admitted to the registered mixed-trace surface has a
complete one-step preservation proof for all of its typed results. -/
theorem runtimeTraceOperation_preserves_runtimeWellFormed operation
    (hoperation : RuntimeTraceOperation operation) :
    OperationPreservesRuntimeWellFormed operation := by
  cases hoperation with
  | interrupt frame => exact interrupt_operationPreservesRuntimeWellFormed frame
  | selectUserReturn purpose =>
      exact selectUserReturn_operationPreservesRuntimeWellFormed purpose
  | userReturn request =>
      exact userReturn_operationPreservesRuntimeWellFormed request
  | syscall call => exact syscall_operationPreservesRuntimeWellFormed call
  | ipc call => exact ipc_operationPreservesRuntimeWellFormed call
  | resumePreempt frame registers =>
      exact resumePreempt_operationPreservesRuntimeWellFormed frame registers
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact transferOffer_operationPreservesRuntimeWellFormed endpointWord sourceWord
        sourceKind payload rights
  | transferAccept endpointWord destinationSlot =>
      exact transferAccept_operationPreservesRuntimeWellFormed endpointWord destinationSlot
  | capabilityCopy source destination destinationSlot rights =>
      exact capabilityCopy_operationPreservesRuntimeWellFormed
        source destination destinationSlot rights
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact capabilityRevoke_operationPreservesRuntimeWellFormed
        authoritySlot victim victimSlot
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact capabilityRevokeSubtree_operationPreservesRuntimeWellFormed
        authoritySlot victim victimSlot
  | map slot page permissions =>
      exact map_operationPreservesRuntimeWellFormed slot page permissions
  | unmap page => exact unmap_operationPreservesRuntimeWellFormed page
  | createSubject subject => exact createSubject_operationPreservesRuntimeWellFormed subject
  | terminateSubject subject =>
      exact terminateSubject_operationPreservesRuntimeWellFormed subject
  | scheduleAdd subject => exact scheduleAdd_operationPreservesRuntimeWellFormed subject
  | scheduleRemove subject => exact scheduleRemove_operationPreservesRuntimeWellFormed subject
  | scheduleNext => exact scheduleNext_operationPreservesRuntimeWellFormed
  | scheduleYield => exact scheduleYield_operationPreservesRuntimeWellFormed
  | scheduleTick => exact scheduleTick_operationPreservesRuntimeWellFormed
  | terminateCurrent => exact terminateCurrent_operationPreservesRuntimeWellFormed
  | restart => exact restart_operationPreservesRuntimeWellFormed

/-- The preservation inventory is complete: every public `Operation`
constructor is represented by `RuntimeTraceOperation`.  This exhaustiveness
lemma prevents a newly added operation from silently escaping the universal
gate theorem below. -/
theorem runtimeTraceOperation_complete operation :
    RuntimeTraceOperation operation := by
  cases operation with
  | interrupt frame => exact .interrupt frame
  | selectUserReturn purpose => exact .selectUserReturn purpose
  | userReturn request => exact .userReturn request
  | syscall call => exact .syscall call
  | ipc call => exact .ipc call
  | resumePreempt frame registers => exact .resumePreempt frame registers
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact .transferOffer endpointWord sourceWord sourceKind payload rights
  | transferAccept endpointWord destinationSlot =>
      exact .transferAccept endpointWord destinationSlot
  | capabilityCopy source destination destinationSlot rights =>
      exact .capabilityCopy source destination destinationSlot rights
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact .capabilityRevoke authoritySlot victim victimSlot
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact .capabilityRevokeSubtree authoritySlot victim victimSlot
  | map slot page permissions => exact .map slot page permissions
  | unmap page => exact .unmap page
  | createSubject subject => exact .createSubject subject
  | terminateSubject subject => exact .terminateSubject subject
  | scheduleAdd subject => exact .scheduleAdd subject
  | scheduleRemove subject => exact .scheduleRemove subject
  | scheduleNext => exact .scheduleNext
  | scheduleYield => exact .scheduleYield
  | scheduleTick => exact .scheduleTick
  | terminateCurrent => exact .terminateCurrent
  | restart => exact .restart

/-- Every public operation preserves the global runtime invariant for every
typed result.  There is no registration premise and no excluded constructor. -/
theorem operation_preserves_runtimeWellFormed operation :
    OperationPreservesRuntimeWellFormed operation :=
  runtimeTraceOperation_preserves_runtimeWellFormed operation
    (runtimeTraceOperation_complete operation)

/-- The total composite gate preserves `RuntimeWellFormed` for an arbitrary
public operation, including attacker-controlled words and terminal modes. -/
theorem gate_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state operation).state :=
  operation_preserves_runtimeWellFormed operation state hstate

/-- Arbitrary finite interleavings of all currently registered runtime
families preserve the global invariant.  Calls and handles remain arbitrary,
so each family contributes both its accepted and typed-rejection paths; halted
suffixes are covered by the same theorem because the outer gate is absorbing. -/
theorem runRuntimeTrace_preserves_runtimeWellFormed state operations
    (hstate : RuntimeWellFormed state)
    (hoperations : ∀ operation, operation ∈ operations →
      RuntimeTraceOperation operation) :
    RuntimeWellFormed (runOperations state operations) := by
  apply runOperations_preserves_runtimeWellFormed state operations hstate
  intro operation hmember
  exact runtimeTraceOperation_preserves_runtimeWellFormed operation
    (hoperations operation hmember)

/-- Arbitrary finite operation sequences preserve the global invariant.  This
is the universal composite-gate preservation boundary: unlike the registered
trace lemma, it has no per-member side condition. -/
theorem runOperations_preserves_runtimeWellFormed_universally state operations
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (runOperations state operations) := by
  apply runOperations_preserves_runtimeWellFormed state operations hstate
  intro operation _hmember
  exact operation_preserves_runtimeWellFormed operation

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
      .syscall syscall, .interrupt frame, .ipc ipc,
      .capabilityRevoke 0 1 0, .unmap 0, .terminateSubject 0] = state := by
  simp [runOperations, gate, hhalted]

/-! ## Executable mixed-trace regressions

These fixtures exercise the public composite boundaries rather than only the
dependency-local transitions.  The arbitrary compiled plan and unrelated
composite fields are deliberately parametric: evaluation can therefore depend
only on the authoritative state selected by each operation. -/

private def lifecycleEvidenceCreated (plan : BootPageTablePlan.Plan) : CompositeState :=
  (gate (bootRuntime plan) (.createSubject 1)).state

private def lifecycleEvidenceDuplicate (plan : BootPageTablePlan.Plan) : GateOutcome :=
  gate (lifecycleEvidenceCreated plan) (.createSubject 1)

private def lifecycleEvidenceTerminated (plan : BootPageTablePlan.Plan) : CompositeState :=
  (gate (lifecycleEvidenceDuplicate plan).state (.terminateSubject 1)).state

private def lifecycleEvidenceStaleTermination (plan : BootPageTablePlan.Plan) : GateOutcome :=
  gate (lifecycleEvidenceTerminated plan) (.terminateSubject 1)

/-- One executable trace contains accepted creation, an atomic duplicate
rejection, accepted cross-subsystem cleanup, and an atomic stale-lifetime
rejection.  Issuance remains monotonic while every live projection retires the
subject. -/
example (plan : BootPageTablePlan.Plan) :
    (lifecycleEvidenceDuplicate plan).result =
      .completed (.createSubject (.rejected .alreadyLive)) ∧
    (lifecycleEvidenceStaleTermination plan).result =
      .completed (.terminateSubject (.rejected .alreadyTerminated)) ∧
    (lifecycleEvidenceTerminated plan).lifecycle.issuedSubjects 1 = true ∧
    (lifecycleEvidenceTerminated plan).capabilities.subjects 1 = false ∧
    (lifecycleEvidenceTerminated plan).scheduler.lifecycle.capabilities.subjects 1 = false ∧
    (lifecycleEvidenceTerminated plan).blockingIPC.scheduler.lifecycle.capabilities.subjects 1 =
      false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private def blockingEvidenceCapability (rights : Capability.Rights) : Capability.Capability :=
  { object := 10, kind := .endpoint, rights, identity := 1 }

private def blockingEvidenceCapabilities : Capability.State :=
  { subjects := fun subject => subject < 4
    objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .endpoint else none
    slots := fun subject slot =>
      if slot != 0 then none
      else if subject = 1 then some (blockingEvidenceCapability { send := true })
      else if subject = 2 || subject = 3 then
        some (blockingEvidenceCapability { receive := true })
      else none }

private def blockingEvidenceLifecycle (current : Option SubjectLifecycle.SubjectId) :
    SubjectLifecycle.State :=
  { capabilities := blockingEvidenceCapabilities
    issuedSubjects := fun subject => subject < 4
    ownedMemory := fun _ => none
    addressOwner := fun space => if space < 4 then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun object => if object = 10 then some 0 else none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject < 4
    current }

private def blockingEvidenceStore : BlockingIPC.State :=
  { scheduler :=
      { lifecycle := blockingEvidenceLifecycle (some 2), ready := [1, 3], capacity := 3 }
    mailbox := fun _ => none
    waiters := fun _ => []
    waiterEndpoint := fun _ => none
    waiterCapacity := 2
    completion := fun _ => none }

private def blockingEvidenceRegisters (marker : UInt64) : ResumableContext.Registers :=
  { accumulator := marker, base := marker, count := marker, data := marker
    source := marker, destination := marker, basePointer := marker
    r8 := marker, r9 := marker, r10 := marker, r11 := marker
    r12 := marker, r13 := marker, r14 := marker, r15 := marker }

private def blockingEvidenceContext (owner : Nat) (marker : UInt64) :
    ResumableContext.Context :=
  { owner
    addressSpace := owner
    frame := { demoFrame 32 .user with
      instructionPointer := 0x400000 + marker
      stackPointer := 0x500000 + marker }
    registers := blockingEvidenceRegisters marker
    kind := .suspended }

private def blockingEvidenceComposite (state : CompositeState) : CompositeState :=
  { state with
    execution := { state.execution with
      core := { state.execution.core with
        lifecycle := blockingEvidenceLifecycle (some 2)
        context := { state.execution.core.context with
          currentSubject := 2, activeAddressSpace := 2 } }
      mode := .running }
    scheduler := blockingEvidenceStore.scheduler
    lifecycle := blockingEvidenceLifecycle (some 2)
    blockingIPC := blockingEvidenceStore }

/-- Evidence state for the typed public blocking boundary.  Subjects 1 and 3
have kernel-owned resumable contexts, subject 2 is current, and the modeled
CR3 names subject 2 before it blocks. -/
private def blockingContextEvidenceComposite (state : CompositeState) : CompositeState :=
  let base := blockingEvidenceComposite state
  { base with
    resumable := { base.resumable with
      scheduler := blockingEvidenceStore.scheduler
      contexts := [blockingEvidenceContext 1 0x10, blockingEvidenceContext 3 0x30]
      capacity := 3
      translations := { base.resumable.translations with
        virtual := { base.resumable.translations.virtual with
          owner := (blockingEvidenceLifecycle (some 2)).addressOwner }
        active := some 2
        entries := [] } }
    blockingContexts := fun _ => none }

private def blockingEvidenceFrame : Interrupt.HardwareFrame := demoFrame 32 .user
private def blockingEvidenceRegisters2 : ResumableContext.Registers :=
  blockingEvidenceRegisters 0x22

private def blockingContextEvidenceRejected (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceComposite state)
    (.receive 0x0000000000020000 blockingEvidenceFrame blockingEvidenceRegisters2)

private def blockingContextEvidenceBlocked (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceRejected state).state
    (.receive 0x0000000000010000 blockingEvidenceFrame blockingEvidenceRegisters2)

private def blockingContextEvidenceWoken (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceBlocked state).state
    (.send 0x0000000000010000 0xCAFE 0xBEEF)

private def blockingContextEvidenceCancelled (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceBlocked state).state (.cancel 2)

private def blockingContextEvidenceTerminated (state : CompositeState) : GateOutcome :=
  gate (blockingContextEvidenceBlocked state).state (.terminateSubject 2)

/-- One mixed global blocking-gate trace first rejects a stale handle without
mutation, then blocks subject 2, immediately restores scheduler-selected peer
1 (including the modeled CR3 flush), and finally wakes subject 2 while
restoring its exact saved frame/register context into the resumable bank. -/
example (state : CompositeState) :
    (blockingContextEvidenceRejected state).result =
        .completed (.receive (.handleRejected (.denied .staleHandle))) ∧
      (blockingContextEvidenceRejected state).state =
        blockingContextEvidenceComposite state := by
  exact ⟨rfl, rfl⟩

example (state : CompositeState) :
    (blockingContextEvidenceBlocked state).result = .completed (.receive .blocked) ∧
      (blockingContextEvidenceBlocked state).state.execution.core.context.currentSubject = 1 ∧
      (blockingContextEvidenceBlocked state).state.execution.core.context.activeAddressSpace = 1 ∧
      (blockingContextEvidenceBlocked state).state.resumable.translations.active = some 1 ∧
      (blockingContextEvidenceBlocked state).state.resumable.translations.entries = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
/-- Explicit global termination consumes the waiter and exact blocked context
created by the public blocking gate; the dead subject is never requeued. -/
example (state : CompositeState) :
    (blockingContextEvidenceTerminated state).result =
        .completed (.terminateSubject .accepted) ∧
      (blockingContextEvidenceTerminated state).state.blockingIPC.waiterEndpoint 2 = none ∧
      (blockingContextEvidenceTerminated state).state.blockingContexts 2 = none ∧
      (blockingContextEvidenceTerminated state).state.scheduler.lifecycle.capabilities.subjects
        2 = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A mixed rejected-block-wake trace composes at the authoritative composite
boundary.  The rejected prefix is atomic; both accepted suffix steps preserve
waiter/context coherence; and wake restores the exact released context into
the resumable bank. -/
theorem mixedBlockingWakeTrace_preserves state staleWord liveWord frame registers word0 word1
    saved
    (hstate : BlockingReceiveWellFormed state)
    (hstale : (dispatchBlockingReceive state staleWord frame registers).reply =
      .handleRejected (.denied .staleHandle))
    (_hblocked : (dispatchBlockingReceive state liveWord frame registers).reply = .blocked)
    (hwoke : (dispatchBlockingSend
      (dispatchBlockingReceive state liveWord frame registers).state
      liveWord word0 word1).reply = .woke saved) :
    (dispatchBlockingReceive state staleWord frame registers).state = state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingReceive state liveWord frame registers).state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingSend
          (dispatchBlockingReceive state liveWord frame registers).state
          liveWord word0 word1).state ∧
      ∃ receiver,
        (dispatchBlockingReceive state liveWord frame registers).state.blockingContexts
            receiver = some saved ∧
        ResumablePreemption.contextFor
          (dispatchBlockingSend
            (dispatchBlockingReceive state liveWord frame registers).state
            liveWord word0 word1).state.resumable.contexts receiver = some saved := by
  have hreject := dispatchBlockingReceive_rejected_atomic state staleWord frame registers
    (.handleRejected (.denied .staleHandle))
    (.handle (.denied .staleHandle)) hstale
  have hblockedWf := dispatchBlockingReceive_preserves_wellFormed
    state liveWord frame registers hstate
  have hwokenWf := dispatchBlockingSend_preserves_wellFormed
    (dispatchBlockingReceive state liveWord frame registers).state
    liveWord word0 word1 hblockedWf
  obtain ⟨receiver, hstored, _, hrestored⟩ := dispatchBlockingSend_woke_exact
    (dispatchBlockingReceive state liveWord frame registers).state
    liveWord word0 word1 saved hblockedWf hwoke
  exact ⟨hreject, hblockedWf, hwokenWf, receiver, hstored, hrestored⟩

/-- The corresponding rejected-block-cancel trace has the same preservation
shape and restores the cancelled subject's exact saved context. -/
theorem mixedBlockingCancelTrace_preserves state staleWord liveWord frame registers subject saved
    (hstate : BlockingReceiveWellFormed state)
    (hstale : (dispatchBlockingReceive state staleWord frame registers).reply =
      .handleRejected (.denied .staleHandle))
    (_hblocked : (dispatchBlockingReceive state liveWord frame registers).reply = .blocked)
    (hcancelled : (dispatchBlockingCancel
      (dispatchBlockingReceive state liveWord frame registers).state subject).reply =
        .cancelled saved) :
    (dispatchBlockingReceive state staleWord frame registers).state = state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingReceive state liveWord frame registers).state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingCancel
          (dispatchBlockingReceive state liveWord frame registers).state subject).state ∧
      (dispatchBlockingReceive state liveWord frame registers).state.blockingContexts subject =
        some saved ∧
      ResumablePreemption.contextFor
        (dispatchBlockingCancel
          (dispatchBlockingReceive state liveWord frame registers).state subject).state.resumable.contexts
        subject = some saved := by
  have hreject := dispatchBlockingReceive_rejected_atomic state staleWord frame registers
    (.handleRejected (.denied .staleHandle))
    (.handle (.denied .staleHandle)) hstale
  have hblockedWf := dispatchBlockingReceive_preserves_wellFormed
    state liveWord frame registers hstate
  have hcancelWf := dispatchBlockingCancel_preserves_wellFormed
    (dispatchBlockingReceive state liveWord frame registers).state subject hblockedWf
  obtain ⟨hstored, _, hrestored⟩ := dispatchBlockingCancel_cancelled_exact
    (dispatchBlockingReceive state liveWord frame registers).state subject saved
    hblockedWf hcancelled
  exact ⟨hreject, hblockedWf, hcancelWf, hstored, hrestored⟩

private def blockingEvidenceBlocked (state : CompositeState) : CompositeBlockingIPCOutcome :=
  dispatchBlockingIPC (blockingEvidenceComposite state) (.receive 0x0000000000010000)

private def blockingEvidenceWoken (state : CompositeState) : CompositeBlockingIPCOutcome :=
  dispatchBlockingIPC (blockingEvidenceBlocked state).state
    (.send 0x0000000000010000 0xCAFE 0xBEEF)

/-- The authoritative composite path blocks receiver 2, switches to sender 1,
wakes exactly receiver 2, and reserves the exact delivered envelope. -/
example (state : CompositeState) :
    (blockingEvidenceBlocked state).reply = .receive (.completed .blocked) ∧
    (blockingEvidenceBlocked state).state.execution.core.context.currentSubject = 1 ∧
    (blockingEvidenceWoken state).reply = .woke 2 ∧
    (blockingEvidenceWoken state).state.blockingIPC.waiters 10 = [] ∧
    (blockingEvidenceWoken state).state.blockingIPC.completion 2 = some (.delivered
      { endpoint := 10, sender := 1, payload := { word0 := 0xCAFE, word1 := 0xBEEF } }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Stale fixed-width handles are rejected before any blocking state is
published. -/
example (state : CompositeState) :
    (dispatchBlockingIPC (blockingEvidenceComposite state)
      (.receive 0x0000000000020000)).reply =
        .receive (.handleRejected (.denied .staleHandle)) ∧
    (dispatchBlockingIPC (blockingEvidenceComposite state)
      (.receive 0x0000000000020000)).state = blockingEvidenceComposite state := by
  constructor
  · rfl
  · apply dispatchBlockingIPC_rejection_atomic _ _ _
    · exact .receiveHandle (.denied .staleHandle)
    · rfl

/-- Revocation-style cancellation after blocking wakes the receiver exactly
once; subject termination instead removes it without making the dead identity
runnable.  Both cleanup paths are republished through the authoritative
composite scheduler boundary. -/
example (state : CompositeState) :
    let blocked := (blockingEvidenceBlocked state).state
    let cancelled := publishBlockingIPC blocked (BlockingIPC.cancelSubject blocked.blockingIPC 2)
    let terminated := publishBlockingIPC blocked (BlockingIPC.terminate blocked.blockingIPC 2)
    cancelled.blockingIPC.waiters 10 = [] ∧
      cancelled.blockingIPC.completion 2 = some .cancelled ∧
      cancelled.scheduler.lifecycle.runnable 2 = true ∧
      terminated.blockingIPC.waiters 10 = [] ∧
      terminated.scheduler.lifecycle.capabilities.subjects 2 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- A concrete kernel fault latches the runtime before a heterogeneous suffix;
the stale handle, IPC, revoke, unmap, termination, and restart operations are
all absorbed byte-for-byte. -/
example (state : CompositeState) :
    let running := { state with execution := { state.execution with mode := .running } }
    let halted := (gate running (.interrupt (demoFrame 14 .kernel))).state
    halted.execution.mode = .halted
      { reason := .kernelFault
        active := some (activeEntry (demoFrame 14 .kernel))
        incomingVector := 14
        incomingOrigin := .kernel } ∧
    runOperations halted [
      .ipc (.receive 0x0000000000020000),
      .capabilityRevoke 0 2 0, .unmap 0, .terminateSubject 2, .restart] = halted := by
  simp [gate, applyOperation, operationReply, dispatchHardware, beginEntry, finishEntry,
    activeEntry, demoFrame, Interrupt.dispatchHardware, Interrupt.decodeVector, mapFatal,
    halt, installResumable, runOperations]

end LeanOS.FailStop
