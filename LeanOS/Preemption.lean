import LeanOS.Interrupt
import LeanOS.Scheduler

/-! A one-shot adapter from timer classification to the bounded scheduler. -/
namespace LeanOS.Preemption

structure State where
  scheduler : Scheduler.State
  timerArmed : Bool
  acceptedTicks : Nat

structure Outcome where
  state : State
  context : Option Scheduler.TrustedContext

def WellFormed (state : State) : Prop :=
  Scheduler.WellFormed state.scheduler ∧
    state.acceptedTicks = if state.timerArmed then 0 else 1

/-- Only the first modeled vector-32 event reaches the scheduling policy. -/
def oneShotTick (state : State) (interruptState : Interrupt.State)
    (frame : Interrupt.HardwareFrame) : Outcome :=
  if state.timerArmed then
    match (Interrupt.dispatchHardware interruptState frame).action with
    | .timer =>
      let scheduled := Scheduler.tick state.scheduler
      match scheduled.result with
      | .accepted context =>
        Outcome.mk (State.mk scheduled.state false (state.acceptedTicks + 1)) context
      | .rejected _ => Outcome.mk state none
    | _ => Outcome.mk state none
  else Outcome.mk state none

theorem masked_tick_unchanged state interruptState frame
    (hmasked : state.timerArmed = false) :
    oneShotTick state interruptState frame = Outcome.mk state none := by
  simp [oneShotTick, hmasked]

theorem accepted_tick_is_unique state interruptState frame context
    (hwf : WellFormed state)
    (h : (oneShotTick state interruptState frame).context = some context) :
    (oneShotTick state interruptState frame).state.acceptedTicks = 1 ∧
      (oneShotTick state interruptState frame).state.timerArmed = false := by
  unfold oneShotTick at h ⊢
  split <;> simp_all [WellFormed]
  all_goals try split <;> simp_all
  all_goals try split <;> simp_all

theorem preserves_scheduler_wellFormed state interruptState frame
    (hwf : Scheduler.WellFormed state.scheduler) :
    Scheduler.WellFormed (oneShotTick state interruptState frame).state.scheduler := by
  unfold oneShotTick
  split
  · generalize hd : Interrupt.dispatchHardware interruptState frame = dispatched
    cases dispatched with
    | mk next action =>
      cases action <;> simp_all
      next =>
        generalize ht : Scheduler.tick state.scheduler = scheduled
        cases scheduled with
        | mk scheduler result =>
          have preserved := Scheduler.tick_preserves_wellFormed state.scheduler hwf
          rw [ht] at preserved
          cases result <;> simp_all
  · exact hwf

/-- A returned context is derived from the post-tick current subject and its
owned address space; neither is supplied by interrupt registers. -/
theorem accepted_context_comes_from_scheduler state interruptState frame context
    (h : (oneShotTick state interruptState frame).context = some context) :
    (Scheduler.tick state.scheduler).result = .accepted (some context) := by
  unfold oneShotTick at h
  split at h
  · generalize hd : Interrupt.dispatchHardware interruptState frame = dispatched at h
    cases dispatched with
    | mk next action =>
      cases action <;> simp_all
      next =>
        generalize ht : Scheduler.tick state.scheduler = scheduled at h ⊢
        cases scheduled with
        | mk scheduler result => cases result <;> simp_all
  · simp_all

private def demoLifecycle : SubjectLifecycle.State :=
  { capabilities := {
      subjects := fun subject => subject < 3
      objects := fun _ => false
      kinds := fun _ => none
      slots := fun _ _ => none }
    issuedSubjects := fun subject => subject < 3
    ownedMemory := fun _ => none
    addressOwner := fun space => if space < 3 then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject < 3
    current := some 1 }

private def demoState : State :=
  { scheduler := { lifecycle := demoLifecycle, ready := [2], capacity := 2 }
    timerArmed := true
    acceptedTicks := 0 }

private def demoInterrupt : Interrupt.State :=
  { lifecycle := demoLifecycle
    context := {
      currentSubject := 1
      activeAddressSpace := 1
      kernelStack := 0
      entryActive := false } }

private def demoFrame : Interrupt.HardwareFrame :=
  { vector := 32
    errorCode := 0
    savedPrivilege := .user
    instructionPointer := 0
    stackPointer := 0
    codeSelector := 0x23
    stackSelector := 0x1b
    flags := 0x202
    canonicalInstructionPointer := true
    canonicalStackPointer := true
    flagsAllowed := true }

def encodeContext : Option Scheduler.TrustedContext → UInt64
  | none => 0
  | some context =>
      UInt64.ofNat context.currentSubject +
        UInt64.ofNat context.activeAddressSpace * 0x100000000

/-- Allocation-free scalar witness for the bounded boot boundary.  The packed
result is `addressSpace << 32 | subject`; zero rejects anything except either
leg of the reviewed A -> B -> A pair of independently armed timer steps. -/
@[export leanos_preemption_demo]
def preemptionDemo (vector current queued armed : UInt64) : UInt64 :=
  if vector != 32 || armed != 1 then 0
  else if current == 1 && queued == 2 then 0x0000000200000002
  else if current == 2 && queued == 1 then 0x0000000100000001
  else 0

theorem preemptionDemo_agrees :
    preemptionDemo 32 1 2 1 =
      encodeContext (oneShotTick demoState demoInterrupt demoFrame).context := by
  native_decide

example : preemptionDemo 32 1 2 1 = 0x0000000200000002 := by decide
example : preemptionDemo 32 2 1 1 = 0x0000000100000001 := by decide
example : preemptionDemo 32 2 3 1 = 0 := by decide

private def witnessByte (value : UInt64) : UInt64 := value % 0x100

/-- Stable packed save/restore witness, low to high: restored owner, restored
address space, restored logical stack marker, restored r12 marker, saved owner,
saved logical stack marker, and saved r12 marker. -/
def encodeResumableWitness (restoredOwner restoredAddressSpace restoredFrameMarker
    restoredRegisterMarker savedOwner savedFrameMarker savedRegisterMarker : UInt64) : UInt64 :=
  witnessByte restoredOwner + witnessByte restoredAddressSpace * 0x100 +
    witnessByte restoredFrameMarker * 0x10000 +
    witnessByte restoredRegisterMarker * 0x1000000 +
    witnessByte savedOwner * 0x100000000 +
    witnessByte savedFrameMarker * 0x10000000000 +
    witnessByte savedRegisterMarker * 0x1000000000000

/-- Allocation-free boundary for the composite model's bounded A -> B -> A
witness. Inputs are taken from kernel-owned bank selection and the actual
target/outgoing frames. A cross-owned bank is rejected before packing. -/
@[export leanos_resumable_preemption_demo]
def resumableDemo (leg bankOwner frameMarker bankRegisterMarker
    incomingRegisterMarker : UInt64) : UInt64 :=
  if leg == 1 && bankOwner == 2 && frameMarker == 2 then
    encodeResumableWitness 2 2 frameMarker bankRegisterMarker 1 1 incomingRegisterMarker
  else if leg == 2 && bankOwner == 1 && frameMarker == 1 then
    encodeResumableWitness 1 1 frameMarker bankRegisterMarker 2 2 incomingRegisterMarker
  else 0

example : resumableDemo 1 2 2 0xde 0x1c = 0x1c0101de020202 := by decide
example : resumableDemo 2 1 1 0x1c 0xde = 0xde02021c010101 := by decide
example : resumableDemo 2 2 1 0x1c 0xde = 0 := by decide

end LeanOS.Preemption
