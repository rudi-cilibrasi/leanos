import LeanOS.DirectPortIO
import LeanOS.FaultDispatch

/-!
# Composed CPL3 port-denial containment

This module is the first composition slice between the finite direct-port-I/O
authority policy (`LeanOS.DirectPortIO`) and the atomic user-fault
cleanup/survivor-dispatch transition (`LeanOS.FaultDispatch`).  It models the
sequence exercised by the booted machine when subject A executes a raw port-I/O
instruction under the production deny-all CPL3 controls:

1. the untrusted port operation is denied with the modeled `#GP(0)` and the
   complete device projection is preserved (`DirectPortIO.executeUser`); then
2. the same normalized user-fault entry retires the kernel-selected current
   subject and selects the next survivor context in one total transition
   (`FaultDispatch.dispatch`).

The composition proves that the untrusted port, value, width, and register-bank
words cannot select a kernel operation or a survivor, that the device
projection is unchanged, and that a denied attempt can never return to the
faulting subject.  It consumes the two existing model boundaries rather than
introducing a second authorization table, fault scheduler, or vector-13
classifier; the machine image binds the `#GP(0)` denial through the shared
generated vector-13 manifest normalizer and reuses the vector-14 user-fault
containment dispatch for cleanup, exactly as this composition sequences the two
models.  x86 privilege/exception delivery, TSS/IOPL loading, device behaviour,
generated code, assembly, and the final binary remain trusted boundaries.
-/
namespace LeanOS.DirectPortContainment

open LeanOS

/-- One composed containment step: the device-side port outcome produced by the
untrusted user operation and the scheduler-side cleanup/dispatch outcome
produced by the normalized user-fault entry. -/
structure Step where
  port : DirectPortIO.Outcome
  fault : FaultDispatch.Outcome

/-- Sequence the finite port-authority denial with the atomic fault
cleanup/survivor dispatch.  The untrusted `operation` words feed only the
device-side policy; the survivor is chosen solely from the authoritative
scheduler/lifecycle state carried by `schedule` and `entry`. -/
def containDeniedPort
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (operation : DirectPortIO.PortOperation)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result) : Step :=
  { port := DirectPortIO.executeUser devices liveControls operation
    fault := FaultDispatch.dispatch schedule entry }

/-- Explicit machine-facing spelling recording that the attacker register bank
is erased before the composed transition is evaluated. -/
def containDeniedPortWithRegisters {Payload : Type}
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (operation : DirectPortIO.PortOperation)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result)
    (_registers : Payload) : Step :=
  containDeniedPort devices liveControls operation schedule entry

/-- The composed transition is total and deterministic in its inputs. -/
theorem containDeniedPort_total devices liveControls operation schedule entry :
    ∃ step, containDeniedPort devices liveControls operation schedule entry = step :=
  ⟨_, rfl⟩

/-- The composed bounded-trace coherence result.  Under accepted, freshly
matched deny-all controls and any successful atomic cleanup/dispatch, the port
attempt is denied with an unchanged device projection, the finite privilege
view denies CPL3, and the authoritative current subject is retired: it becomes
dead and non-runnable, leaves the ready queue and current slot, and loses its
resumable context.  Every address space and mapping it owned is torn down. -/
theorem denied_port_contained
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (operation : DirectPortIO.PortOperation)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result)
    (hpolicy : DirectPortIO.AcceptedControls devices.controls)
    (hlive : liveControls = devices.controls)
    (hsuccess :
      (∃ reason, (FaultDispatch.dispatch schedule entry).action = .idle reason) ∨
      ∃ reason context,
        (FaultDispatch.dispatch schedule entry).action = .dispatch reason context) :
    let step := containDeniedPort devices liveControls operation schedule entry
    step.port.result = .userDeniedGP ∧
      step.port.state.devices = devices.devices ∧
      DirectPortIO.privilegeAllows liveControls .user = false ∧
      ∃ faulting,
        schedule.scheduler.lifecycle.current = some faulting ∧
          schedule.scheduler.lifecycle.capabilities.subjects faulting = true ∧
          schedule.scheduler.lifecycle.runnable faulting = true ∧
          step.fault.state.scheduler.lifecycle.capabilities.subjects faulting = false ∧
          step.fault.state.scheduler.lifecycle.runnable faulting = false ∧
          faulting ∉ step.fault.state.scheduler.ready ∧
          step.fault.state.scheduler.lifecycle.current ≠ some faulting ∧
          ResumablePreemption.contextFor step.fault.state.contexts faulting = none ∧
          ∀ addressSpace,
            schedule.scheduler.lifecycle.addressOwner addressSpace = some faulting →
              step.fault.state.scheduler.lifecycle.addressOwner addressSpace = none ∧
                ∀ page,
                  step.fault.state.translations.virtual.mappings addressSpace page = none := by
  have hcontrols : devices.controls = DirectPortIO.selectedControls := hpolicy
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (DirectPortIO.executeUser devices liveControls operation).result = _
    rw [DirectPortIO.accepted_user_request_denied_gp devices liveControls operation hpolicy hlive]
  · exact DirectPortIO.user_request_preserves_device_state devices liveControls operation
  · rw [hlive, hcontrols]; exact DirectPortIO.selected_controls_deny_user_cpl
  · exact FaultDispatch.successful_nonresumption schedule entry hsuccess

/-- The untrusted port operation words cannot select a kernel operation on the
device side and cannot select or relabel the survivor on the scheduler side:
the complete fault outcome is a function of the kernel-owned scheduler state and
normalized entry alone. -/
theorem untrusted_words_cannot_select
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result)
    (left right : DirectPortIO.PortOperation) :
    (DirectPortIO.executeUser devices liveControls left).result ≠ .kernelAccepted ∧
      (DirectPortIO.executeUser devices liveControls right).result ≠ .kernelAccepted ∧
      (containDeniedPort devices liveControls left schedule entry).fault =
        (containDeniedPort devices liveControls right schedule entry).fault := by
  refine ⟨?_, ?_, rfl⟩
  · exact DirectPortIO.user_request_never_kernel_accepted devices liveControls left
  · exact DirectPortIO.user_request_never_kernel_accepted devices liveControls right

/-- The attacker register bank is not an input to the composed transition:
erasing or substituting it leaves the entire step unchanged. -/
theorem attacker_registers_cannot_relabel {Payload : Type}
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (operation : DirectPortIO.PortOperation)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result)
    (left right : Payload) :
    containDeniedPortWithRegisters devices liveControls operation schedule entry left =
      containDeniedPortWithRegisters devices liveControls operation schedule entry right :=
  rfl

/-- A denied attempt can never return to the faulting subject: on any
successful composed step the faulting subject is absent from the current slot,
the ready queue, and the resumable context bank of the post-state. -/
theorem denied_attempt_cannot_return_to_faulting
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (operation : DirectPortIO.PortOperation)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result)
    (hpolicy : DirectPortIO.AcceptedControls devices.controls)
    (hlive : liveControls = devices.controls)
    (hsuccess :
      (∃ reason, (FaultDispatch.dispatch schedule entry).action = .idle reason) ∨
      ∃ reason context,
        (FaultDispatch.dispatch schedule entry).action = .dispatch reason context) :
    ∃ faulting,
      schedule.scheduler.lifecycle.current = some faulting ∧
        (containDeniedPort devices liveControls operation schedule entry).fault.state.scheduler.lifecycle.current
          ≠ some faulting ∧
        faulting ∉ (containDeniedPort devices liveControls operation schedule entry).fault.state.scheduler.ready ∧
        ResumablePreemption.contextFor
          (containDeniedPort devices liveControls operation schedule entry).fault.state.contexts
          faulting = none := by
  obtain ⟨_, _, _, faulting, hcurrent, _, _, _, _, hready, hnotcurrent, hcontext, _⟩ :=
    denied_port_contained devices liveControls operation schedule entry hpolicy hlive hsuccess
  exact ⟨faulting, hcurrent, hnotcurrent, hready, hcontext⟩

/-! ## Concrete non-vacuity witness

A two-subject pre-state with subject 1 (A) current and runnable and subject 2
(B) queued as the sole survivor.  The device state uses the accepted deny-all
controls.  These witnesses show the composed containment is not vacuous for
either a serial-console or an `isa-debug-exit` untrusted probe. -/

private def cleanDevices : DirectPortIO.DeviceState := ⟨0, 0, 0, 0⟩

/-- The accepted deny-all control and clean device projection. -/
def witnessDevices : DirectPortIO.State :=
  { controls := DirectPortIO.selectedControls, devices := cleanDevices }

/-- Untrusted serial-console output probe (`OUT` to `0x3f8`). -/
def serialProbe : DirectPortIO.PortOperation :=
  { port := 0x3f8, direction := .output, width := .byte, value := 65 }

/-- Untrusted `isa-debug-exit` output probe (`OUT` to `0xf4`). -/
def debugExitProbe : DirectPortIO.PortOperation :=
  { port := 0xf4, direction := .output, width := .byte, value := 0x11 }

/-- Untrusted PIC control-port output probe (`OUT` to `0x21`). -/
def picProbe : DirectPortIO.PortOperation :=
  { port := 0x21, direction := .output, width := .byte, value := 0xff }

/-- Shared two-subject capability witness (subjects 1 and 2 live). -/
def witnessCapabilities : Capability.State :=
  { subjects := fun subject => subject = 1 || subject = 2
    objects := fun object => object = 1 || object = 2 || object = 20 || object = 30
    kinds := fun object =>
      if object = 1 || object = 2 then some .addressSpace
      else if object = 20 then some .memory
      else if object = 30 then some .endpoint
      else none
    slots := fun holder slot =>
      if holder = 2 && slot = 7 then
        some { object := 20, kind := .memory, rights := { read := true } }
      else none }

/-- Shared two-subject lifecycle witness: A (subject 1) current and runnable,
B (subject 2) runnable and owning resources across every cleanup class. -/
def witnessLifecycle : SubjectLifecycle.State :=
  { capabilities := witnessCapabilities
    issuedSubjects := fun subject => subject = 1 || subject = 2
    ownedMemory := fun object => if object = 20 then some (2, 40) else none
    addressOwner := fun space => if space = 1 || space = 2 then some space else none
    mapping := fun space page => if space = 2 && page = 9 then some 20 else none
    endpointOwner := fun endpoint => if endpoint = 30 then some 2 else none
    mailbox := fun _ => none
    frameOwner := fun frame => if frame = 40 then some 2 else none
    freeFrame := fun frame => !(frame = 40)
    runnable := fun subject => subject = 1 || subject = 2
    current := some 1 }

private def witnessHardwareFrame : Interrupt.HardwareFrame :=
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

private def witnessRegisters : ResumablePreemption.Registers :=
  { accumulator := 0
    base := 0xb2b2cafe51a7e55e
    count := 0x030201
    data := 0x51a7
    source := 0
    destination := 0
    basePointer := 0
    r8 := 0, r9 := 0, r10 := 0, r11 := 0, r12 := 0, r13 := 0, r14 := 0, r15 := 0 }

/-- Shared kernel-owned suspended context of survivor B (subject 2). -/
def witnessSurvivorContext : ResumablePreemption.Context :=
  { owner := 2
    addressSpace := 2
    frame := witnessHardwareFrame
    registers := witnessRegisters
    kind := .suspended }

/-- The authoritative resumable-preemption pre-state: A (subject 1) is the live,
runnable current subject; B (subject 2) is the sole queued survivor with a
kernel-owned suspended context. -/
def witnessSchedule : ResumablePreemption.State :=
  let lifecycle := witnessLifecycle
  let capabilities := witnessCapabilities
  { scheduler := { lifecycle, ready := [2], capacity := 2 }
    contexts := [witnessSurvivorContext]
    capacity := 2
    translations :=
      { virtual :=
          { memory :=
              { capabilities
                allocator :=
                  { frames := [40]
                    status := fun frame => if frame = 40 then .owned 20 else .free }
                binding := fun object => if object = 20 then some 40 else none
                issued := fun object =>
                  object = 1 || object = 2 || object = 20 || object = 30 }
            owner := lifecycle.addressOwner
            mappings := fun space page =>
              if space = 2 && page = 9 then
                some { object := 20, permissions := { read := true } } else none
            issuedAddressSpace := fun space => space = 1 || space = 2 }
        active := some 1
        entries := [] } }

/-- The normalized user-fault entry that drives cleanup/dispatch (vector 14,
user origin, current subject 1, active address space 1). -/
def witnessEntry : InterruptEntry.Result :=
  .accepted
    { vector := 14
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

/-- The composed step dispatches the survivor: A's port write is denied, the
device projection is unchanged, and subject 2 becomes current while subject 1 is
retired. -/
theorem witness_serial_denied_and_dispatched :
    let step := containDeniedPort witnessDevices DirectPortIO.selectedControls
      serialProbe witnessSchedule witnessEntry
    step.port.result = .userDeniedGP ∧
      step.port.state.devices = cleanDevices ∧
      step.fault.action = .dispatch .pageFault witnessSurvivorContext ∧
      step.fault.state.scheduler.lifecycle.current = some 2 ∧
      step.fault.state.scheduler.lifecycle.capabilities.subjects 1 = false ∧
      step.fault.state.scheduler.ready = [] ∧
      ResumablePreemption.contextFor step.fault.state.contexts 1 = none := by
  native_decide

/-- The device projection is byte-for-byte identical whether A probes the
serial console, the `isa-debug-exit` port, or a PIC control port, and the
survivor dispatch is identical across all three untrusted probes. -/
theorem witness_untrusted_probe_independent :
    let serial := containDeniedPort witnessDevices DirectPortIO.selectedControls
      serialProbe witnessSchedule witnessEntry
    let debugExit := containDeniedPort witnessDevices DirectPortIO.selectedControls
      debugExitProbe witnessSchedule witnessEntry
    let pic := containDeniedPort witnessDevices DirectPortIO.selectedControls
      picProbe witnessSchedule witnessEntry
    serial.port.state.devices = debugExit.port.state.devices ∧
      debugExit.port.state.devices = pic.port.state.devices ∧
      serial.fault = debugExit.fault ∧
      debugExit.fault = pic.fault := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> native_decide

/-- The named non-vacuity witness: the general composed theorem applies to the
concrete two-subject pre-state and retires the faulting subject. -/
theorem denied_port_contained_nonvacuous :
    (∃ reason context,
      (FaultDispatch.dispatch witnessSchedule witnessEntry).action = .dispatch reason context) ∧
      (containDeniedPort witnessDevices DirectPortIO.selectedControls serialProbe
        witnessSchedule witnessEntry).port.result = .userDeniedGP ∧
      (containDeniedPort witnessDevices DirectPortIO.selectedControls serialProbe
        witnessSchedule witnessEntry).fault.state.scheduler.lifecycle.capabilities.subjects 1 =
        false := by
  refine ⟨⟨.pageFault, witnessSurvivorContext, by native_decide⟩, ?_, ?_⟩ <;> native_decide

end LeanOS.DirectPortContainment
