import LeanOS.Interrupt
import LeanOS.InterruptEntry
import LeanOS.BootPageTablePlan
import LeanOS.DMAQuarantine
import LeanOS.IPCSyscall
import LeanOS.BlockingIPC
import LeanOS.BlockingIPCContext
import LeanOS.Preemption
import LeanOS.CapabilityTransfer
import LeanOS.ResumablePreemption
import LeanOS.DirectPortIO
import LeanOS.InvalidationPublication
import LeanOS.CompositeFootprint

/-!
# Irreversible exception fail-stop model: the execution latch

This composite layer makes interrupt entry transactional and fatality absorbing.
The underlying interrupt classifier remains the source of vector, origin, and
subject-containment policy; this layer is the authoritative execution latch.
It owns ordinary and non-maskable entry, the terminal NMI record, and the
outgoing user-return transaction.  `LeanOS.FailStop` re-exports this module
together with the rest of the composite gate.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

inductive FatalReason where
  | kernelFault | unsupportedVector | nestedEntry | doubleFault
  | nonMaskableInterrupt
  | dmaControlSnapshotChanged | dmaInvalidControlSnapshot
  | invalidNmiEntry (reason : InterruptEntry.NmiRejectReason)
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
  interruptedMode : Option InterruptEntry.InterruptedMode := none
  interruptedCr3 : Option UInt64 := none
  terminalStackIdentity : Option UInt64 := none
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
  let record : HaltRecord :=
    { reason, active, incomingVector := incoming.vector
      incomingOrigin := incoming.savedPrivilege }
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

/-! ## Non-maskable terminal entry

Unlike ordinary entry, this transition is admitted while `handling` and never
calls `beginEntry`, `finishEntry`, containment, scheduling, or return
selection.  It consumes the separate terminal normalizer result and changes
only the execution latch plus the two privileged cleanup bits. -/

def interruptedModeOf : Mode → InterruptEntry.InterruptedMode
  | .running => .running
  | .handling _ => .handling
  | .halted _ => .halted

private def latchNmi (state : State) (reason : FatalReason)
    (active : Option ActiveEntry) (vector : Nat) (origin : Interrupt.Privilege)
    (mode : InterruptEntry.InterruptedMode) (cr3 : Option UInt64)
    (stackIdentity : Option UInt64) : EntryOutcome :=
  let record : HaltRecord :=
    { reason, active, incomingVector := vector, incomingOrigin := origin
      interruptedMode := some mode, interruptedCr3 := cr3
      terminalStackIdentity := stackIdentity }
  { state := { state with
      core := { state.core with
        context := { state.core.context with entryActive := true } }
      mode := .halted record
      returnAuthorityArmed := false
      copyOverride := false }
    action := .fatal reason }

/-- Every NMI latch preserves the execution invariant: the lifecycle remains
unchanged, return authority is disarmed, and the terminal entry-active bit is
set in the same atomic update as the halt record. -/
private theorem latchNmi_preserves_wellFormed state reason active vector origin mode cr3
    stackIdentity (hstate : WellFormed state) :
    WellFormed
      (latchNmi state reason active vector origin mode cr3 stackIdentity).state := by
  rcases hstate with ⟨hcore, _hbound, _hmode⟩
  exact ⟨by simpa only [Interrupt.WellFormed, latchNmi] using hcore,
    by simp [latchNmi], by simp [latchNmi]⟩

def acceptedNmiRecord (state : State) (event : InterruptEntry.NormalizedNmi) : HaltRecord :=
  { reason := .nonMaskableInterrupt
    active := match state.mode with | .handling entry => some entry | _ => none
    incomingVector := event.vector.toNat
    incomingOrigin := event.origin
    interruptedMode := some event.interruptedMode
    interruptedCr3 := some event.activeCr3
    terminalStackIdentity := some event.stackIdentity }

/-- Canonical fixed-width words for the later stateful-corpus boundary.  The
active ordinary frame is included rather than summarized by a lossy tag. -/
structure NmiTerminalWords where
  version : UInt64
  reason : UInt64
  incomingVector : UInt64
  incomingOrigin : UInt64
  interruptedModePresent : UInt64
  interruptedMode : UInt64
  cr3Present : UInt64
  interruptedCr3 : UInt64
  stackPresent : UInt64
  terminalStackIdentity : UInt64
  activePresent : UInt64
  activeVector : UInt64
  activeOrigin : UInt64
  activeFrameVector : UInt64
  activeErrorCode : UInt64
  activeRip : UInt64
  activeRsp : UInt64
  activeCs : UInt64
  activeSs : UInt64
  activeFlags : UInt64
  activeCanonicalRip : UInt64
  activeCanonicalRsp : UInt64
  activeFlagsAllowed : UInt64
  deriving DecidableEq, Repr

private def privilegeCode : Interrupt.Privilege → UInt64
  | .kernel => 0 | .user => 1

def encodeNmiTerminalRecord (record : HaltRecord) : Option NmiTerminalWords :=
  if record.reason != .nonMaskableInterrupt then none
  else
    let (cr3Present, cr3) := match record.interruptedCr3 with
      | some value => ((1 : UInt64), value) | none => ((0 : UInt64), 0)
    let (stackPresent, stackIdentity) := match record.terminalStackIdentity with
      | some value => ((1 : UInt64), value) | none => ((0 : UInt64), 0)
    let (modePresent, mode) := match record.interruptedMode with
      | some value => ((1 : UInt64), value.code) | none => ((0 : UInt64), 0)
    let activeWords := match record.active with
      | none => ((0 : UInt64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
      | some active =>
          ((1 : UInt64), UInt64.ofNat active.vector, privilegeCode active.origin,
            UInt64.ofNat active.frame.vector, active.frame.errorCode,
            active.frame.instructionPointer, active.frame.stackPointer,
            active.frame.codeSelector, active.frame.stackSelector, active.frame.flags,
            if active.frame.canonicalInstructionPointer then (1 : UInt64) else 0,
            if active.frame.canonicalStackPointer then (1 : UInt64) else 0,
            if active.frame.flagsAllowed then (1 : UInt64) else 0)
    some ⟨1, 1, UInt64.ofNat record.incomingVector, privilegeCode record.incomingOrigin,
      modePresent, mode, cr3Present, cr3, stackPresent, stackIdentity,
      activeWords.1, activeWords.2.1, activeWords.2.2.1, activeWords.2.2.2.1,
      activeWords.2.2.2.2.1, activeWords.2.2.2.2.2.1,
      activeWords.2.2.2.2.2.2.1, activeWords.2.2.2.2.2.2.2.1,
      activeWords.2.2.2.2.2.2.2.2.1, activeWords.2.2.2.2.2.2.2.2.2.1,
      activeWords.2.2.2.2.2.2.2.2.2.2.1,
      activeWords.2.2.2.2.2.2.2.2.2.2.2.1,
      activeWords.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- NMI is an out-of-band terminal step.  A malformed terminal snapshot also
halts, but retains its exact typed normalization failure rather than granting
an ordinary handler.  An NMI observed after halt returns the original record
unchanged, modeling architectural blocking of a second physical NMI until a
return that this model never performs. -/
def dispatchNmi (state : State) (raw : InterruptEntry.RawNmiEntry)
    (context : InterruptEntry.NmiContext) : EntryOutcome :=
  match state.mode with
  | .halted record => { state, action := .alreadyHalted record }
  | mode =>
      let active := match mode with | .handling entry => some entry | _ => none
      let interruptedMode := interruptedModeOf mode
      if context.interruptedMode != interruptedMode then
        latchNmi state (.invalidNmiEntry .staleKernelContext) active
          raw.descriptor.vector.toNat raw.claimedOrigin interruptedMode none none
      else
        match InterruptEntry.normalizeNmi raw context state.core.context.currentSubject
            state.core.context.activeAddressSpace with
        | .fatal reason =>
            latchNmi state (.invalidNmiEntry reason) active raw.descriptor.vector.toNat
              raw.claimedOrigin interruptedMode none none
        | .accepted event =>
            latchNmi state .nonMaskableInterrupt active event.vector.toNat event.origin
              event.interruptedMode (some event.activeCr3) (some event.stackIdentity)

theorem dispatchNmi_preserves_wellFormed state raw context
    (hstate : WellFormed state) :
    WellFormed (dispatchNmi state raw context).state := by
  cases hmode : state.mode with
  | halted record => simpa [dispatchNmi, hmode] using hstate
  | running =>
      simp only [dispatchNmi, hmode]
      split
      · exact latchNmi_preserves_wellFormed _ _ _ _ _ _ _ _ hstate
      · split <;> exact latchNmi_preserves_wellFormed _ _ _ _ _ _ _ _ hstate
  | handling entry =>
      simp only [dispatchNmi, hmode]
      split
      · exact latchNmi_preserves_wellFormed _ _ _ _ _ _ _ _ hstate
      · split <;> exact latchNmi_preserves_wellFormed _ _ _ _ _ _ _ _ hstate

@[simp] theorem dispatchNmi_core_lifecycle state raw context :
    (dispatchNmi state raw context).state.core.lifecycle = state.core.lifecycle := by
  cases hmode : state.mode with
  | halted record => simp [dispatchNmi, hmode]
  | running | handling =>
      simp [dispatchNmi, hmode]
      split <;> simp [latchNmi]
      split <;> simp [latchNmi]

@[simp] theorem dispatchNmi_currentSubject state raw context :
    (dispatchNmi state raw context).state.core.context.currentSubject =
      state.core.context.currentSubject := by
  cases hmode : state.mode with
  | halted record => simp [dispatchNmi, hmode]
  | running | handling =>
      simp [dispatchNmi, hmode]
      split <;> simp [latchNmi]
      split <;> simp [latchNmi]

@[simp] theorem dispatchNmi_activeAddressSpace state raw context :
    (dispatchNmi state raw context).state.core.context.activeAddressSpace =
      state.core.context.activeAddressSpace := by
  cases hmode : state.mode with
  | halted record => simp [dispatchNmi, hmode]
  | running | handling =>
      simp [dispatchNmi, hmode]
      split <;> simp [latchNmi]
      split <;> simp [latchNmi]

theorem dispatchNmi_nonhalted_halts state raw context
    (hnotHalted : ∀ record, state.mode ≠ .halted record) :
    ∃ record, (dispatchNmi state raw context).state.mode = .halted record := by
  cases hmode : state.mode with
  | halted record => exact False.elim (hnotHalted record hmode)
  | running | handling =>
      simp [dispatchNmi, hmode]
      split <;> simp [latchNmi]
      split <;> simp [latchNmi]

theorem dispatchNmi_nonhalted_disarms state raw context
    (hnotHalted : ∀ record, state.mode ≠ .halted record) :
    (dispatchNmi state raw context).state.returnAuthorityArmed = false := by
  cases hmode : state.mode with
  | halted record => exact False.elim (hnotHalted record hmode)
  | running | handling =>
      simp [dispatchNmi, hmode]
      split <;> simp [latchNmi]
      split <;> simp [latchNmi]

theorem accepted_nmi_terminal state raw context event
    (hmode : state.mode = .running ∨ ∃ active, state.mode = .handling active)
    (hcontext : context.interruptedMode = interruptedModeOf state.mode)
    (haccepted : InterruptEntry.normalizeNmi raw context
      state.core.context.currentSubject state.core.context.activeAddressSpace =
        .accepted event) :
    let next := dispatchNmi state raw context
    next.action = .fatal .nonMaskableInterrupt ∧
      next.state.mode = .halted (acceptedNmiRecord state event) ∧
      next.state.core.lifecycle = state.core.lifecycle ∧
      next.state.core.context.currentSubject = state.core.context.currentSubject ∧
      next.state.core.context.activeAddressSpace = state.core.context.activeAddressSpace ∧
      next.state.core.context.kernelStack = state.core.context.kernelStack ∧
      next.state.returnAddressSpace = state.returnAddressSpace ∧
      next.state.returnPlan = state.returnPlan ∧
      next.state.returnAuthority = state.returnAuthority ∧
      next.state.returnAuthorityArmed = false ∧
      next.state.copyOverride = false := by
  rcases hmode with hmode | ⟨active, hmode⟩
  · simp [dispatchNmi, hmode, hcontext, haccepted, latchNmi, acceptedNmiRecord]
  · simp [dispatchNmi, hmode, hcontext, haccepted, latchNmi, acceptedNmiRecord]

theorem halted_nmi_absorbing state record raw context
    (hmode : state.mode = .halted record) :
    dispatchNmi state raw context = { state, action := .alreadyHalted record } := by
  simp [dispatchNmi, hmode]

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
    · rw [ite_eq_left hchecks]
      refine ⟨hcore, ?_, hmode⟩
      intro _
      exact ⟨view, plan, hview, hplan, hchecks.2.2.2.2.2, hchecks.1,
        hchecks.2.1, hchecks.2.2.1, hchecks.2.2.2.1,
        hchecks.2.2.2.2.1, rfl, rfl, rfl⟩
    · rw [ite_eq_right hchecks]
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

def latchInvalidUserReturn (state : State) (request : Interrupt.UserReturnRequest)
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
theorem latchInvalidUserReturn_preserves_wellFormed state request reason active
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

end LeanOS.FailStop
