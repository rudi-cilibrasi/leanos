/-!
# Finite direct-port-I/O authority

This model separates attacker-supplied port/value words from the trusted
kernel purpose used to authorize an operation.  The selected Phase 2 TSS
policy has IOPL zero and places the absent I/O bitmap immediately beyond the
descriptor limit.  User-origin requests therefore produce a modeled `#GP(0)`
without changing the complete device projection.  Kernel requests are
accepted only when their purpose, port, direction, and width exactly match the
finite reviewed manifest.

The model begins after a trusted adapter has constructed and read back the
control snapshot.  x86 privilege checks, TSS loading, instruction and exception
semantics, devices, generated code, assembly, and the final binary are not
proved here.
-/
namespace LeanOS.DirectPortIO

inductive Direction where
  | input | output
  deriving BEq, DecidableEq, Repr

inductive Width where
  | byte | word | dword
  deriving BEq, DecidableEq, Repr

/-- Match the value consumed by the selected x86 output instruction width.
Upper request bits are not part of the device-visible operation. -/
def Width.normalize : Width → UInt64 → UInt64
  | .byte, value => value % 0x100
  | .word, value => value % 0x10000
  | .dword, value => value % 0x100000000

inductive Purpose where
  | serial | pic | pit | debugExit
  deriving BEq, DecidableEq, Repr

inductive Origin where
  | user | kernel
  deriving BEq, DecidableEq, Repr

/-- The entry boundary, rather than operation words, selects current privilege. -/
def currentCpl : Origin → Nat
  | .user => 3
  | .kernel => 0

/-- Words available to an untrusted subject contain no origin or purpose. -/
structure PortOperation where
  port : Nat
  direction : Direction
  width : Width
  value : UInt64
  deriving DecidableEq, Repr

/-- A kernel purpose is supplied separately by trusted dispatch state. -/
structure KernelRequest where
  purpose : Purpose
  operation : PortOperation
  deriving DecidableEq, Repr

structure AuthorityKey where
  purpose : Purpose
  port : Nat
  direction : Direction
  width : Width
  deriving BEq, DecidableEq, Repr

def KernelRequest.key (request : KernelRequest) : AuthorityKey :=
  { purpose := request.purpose
    port := request.operation.port
    direction := request.operation.direction
    width := request.operation.width }

/-- Exact reviewed authority for the serial console, legacy PIC, PIT, and
isa-debug-exit operations used by the selected slice.  No port range is
implicitly widened. -/
def portManifest : List AuthorityKey :=
  [ ⟨.serial, 0x3f8, .output, .byte⟩
  , ⟨.serial, 0x3f9, .output, .byte⟩
  , ⟨.serial, 0x3fa, .output, .byte⟩
  , ⟨.serial, 0x3fb, .output, .byte⟩
  , ⟨.serial, 0x3fc, .output, .byte⟩
  , ⟨.serial, 0x3fd, .input, .byte⟩
  , ⟨.pic, 0x20, .output, .byte⟩
  , ⟨.pic, 0x21, .output, .byte⟩
  , ⟨.pic, 0xa0, .output, .byte⟩
  , ⟨.pic, 0xa1, .output, .byte⟩
  , ⟨.pit, 0x40, .output, .byte⟩
  , ⟨.pit, 0x43, .output, .byte⟩
  , ⟨.debugExit, 0xf4, .output, .byte⟩ ]

/-- Complete finite privilege-control projection consumed by this slice.
`ioBitmapPresent = false` records that the base is beyond the TSS limit rather
than naming any permissive bitmap bit. -/
structure Controls where
  ioPrivilegeLevel : Nat
  tssDescriptorLimit : Nat
  ioMapBase : Nat
  ioBitmapPresent : Bool
  kernelConfigured : Bool
  readbackMatches : Bool
  deriving BEq, DecidableEq, Repr

def selectedControls : Controls :=
  { ioPrivilegeLevel := 0
    tssDescriptorLimit := 103
    ioMapBase := 104
    ioBitmapPresent := false
    kernelConfigured := true
    readbackMatches := true }

def AcceptedControls (controls : Controls) : Prop := controls = selectedControls

/-- Finite privilege view: CPL at or below IOPL has ambient access; otherwise
this deny-all slice exposes no bitmap permission. -/
def privilegeAllows (controls : Controls) (origin : Origin) : Bool :=
  decide (currentCpl origin ≤ controls.ioPrivilegeLevel) || controls.ioBitmapPresent

theorem selected_controls_deny_user_cpl :
    privilegeAllows selectedControls .user = false := by decide

theorem selected_controls_allow_kernel_cpl :
    privilegeAllows selectedControls .kernel = true := by decide

/-- Abstract state of every device class named by this policy. -/
structure DeviceState where
  serial : UInt64
  pic : UInt64
  pit : UInt64
  debugExit : UInt64
  deriving DecidableEq, Repr

structure State where
  controls : Controls
  devices : DeviceState
  deriving DecidableEq, Repr

inductive RejectReason where
  | malformedPolicy | staleReadback | unauthorizedKernelOperation
  deriving DecidableEq, Repr

inductive Result where
  | userDeniedGP
  | kernelAccepted
  | rejected (reason : RejectReason)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result
  deriving DecidableEq, Repr

/-- Input operations observe but do not mutate this abstract projection.
Output operations affect only the device class selected by trusted purpose and
store exactly the low bits consumed by their authorized x86 operation width. -/
def applyKernel (devices : DeviceState) (request : KernelRequest) : DeviceState :=
  match request.operation.direction with
  | .input => devices
  | .output =>
      let value := request.operation.width.normalize request.operation.value
      match request.purpose with
      | .serial => { devices with serial := value }
      | .pic => { devices with pic := value }
      | .pit => { devices with pit := value }
      | .debugExit => { devices with debugExit := value }

/-- User entry supplies only port operation words.  Origin and kernel purpose
are not fields that those words can select. -/
def executeUser (state : State) (liveControls : Controls)
    (_request : PortOperation) : Outcome :=
  if _hpolicy : state.controls ≠ selectedControls then
    { state, result := .rejected .malformedPolicy }
  else if _hlive : liveControls ≠ state.controls then
    { state, result := .rejected .staleReadback }
  else if privilegeAllows liveControls .user then
    { state, result := .rejected .malformedPolicy }
  else { state, result := .userDeniedGP }

/-- Trusted kernel entry additionally supplies a purpose.  Acceptance requires
kernel privilege and the exact purpose/port/direction/width key in
`portManifest`. -/
def executeKernel (state : State) (liveControls : Controls)
    (request : KernelRequest) : Outcome :=
  if _hpolicy : state.controls ≠ selectedControls then
    { state, result := .rejected .malformedPolicy }
  else if _hlive : liveControls ≠ state.controls then
    { state, result := .rejected .staleReadback }
  else if _hprivilege : privilegeAllows liveControls .kernel then
    if _hauthorized : portManifest.contains request.key then
      { state := { state with devices := applyKernel state.devices request }
        result := .kernelAccepted }
    else { state, result := .rejected .unauthorizedKernelOperation }
  else { state, result := .rejected .malformedPolicy }

theorem executeUser_total state live request :
    ∃ outcome, executeUser state live request = outcome := ⟨_, rfl⟩

theorem executeKernel_total state live request :
    ∃ outcome, executeKernel state live request = outcome := ⟨_, rfl⟩

theorem executeUser_deterministic state live request first second
    (hfirst : executeUser state live request = first)
    (hsecond : executeUser state live request = second) : first = second := by
  rw [← hfirst, hsecond]

theorem executeKernel_deterministic state live request first second
    (hfirst : executeKernel state live request = first)
    (hsecond : executeKernel state live request = second) : first = second := by
  rw [← hfirst, hsecond]

/-- Every user-origin attempt preserves the identical complete device state,
including malformed-policy and stale-read-back rejection paths. -/
theorem user_request_preserves_device_state state live request :
    (executeUser state live request).state.devices = state.devices := by
  unfold executeUser
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem user_request_never_kernel_accepted state live request :
    (executeUser state live request).result ≠ .kernelAccepted := by
  unfold executeUser
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem accepted_user_request_denied_gp state live request
    (hpolicy : AcceptedControls state.controls)
    (hlive : live = state.controls) :
    executeUser state live request = { state, result := .userDeniedGP } := by
  have hcontrols : state.controls = selectedControls := hpolicy
  simp [executeUser, hcontrols, hlive, selected_controls_deny_user_cpl]

/-- Any typed kernel acceptance exposes the exact manifest membership and
fresh control binding that authorized it. -/
theorem kernel_acceptance_confined state live request
    (haccepted : (executeKernel state live request).result = .kernelAccepted) :
    AcceptedControls state.controls ∧
      live = state.controls ∧
      privilegeAllows live .kernel = true ∧
      portManifest.contains request.key = true ∧
      (executeKernel state live request).state.controls = state.controls ∧
      (executeKernel state live request).state.devices =
        applyKernel state.devices request := by
  unfold executeKernel at haccepted
  split at haccepted <;> try contradiction
  rename_i hpolicy
  split at haccepted <;> try contradiction
  rename_i hlive
  split at haccepted <;> try contradiction
  rename_i hprivilege
  split at haccepted <;> try contradiction
  rename_i hauthorized
  cases haccepted
  have hp : state.controls = selectedControls := by simp_all
  have hl : live = state.controls := by simp_all
  have heval : executeKernel state live request =
      { state := { state with devices := applyKernel state.devices request }
        result := .kernelAccepted } := by
    simp [executeKernel, hpolicy, hlive, hprivilege, hauthorized]
  exact ⟨hp, hl, hprivilege, hauthorized, by simp [heval], by simp [heval]⟩

/-- Every typed kernel rejection is atomic for the complete device state. -/
theorem kernel_rejection_preserves_device_state state live request reason
    (hrejected : (executeKernel state live request).result = .rejected reason) :
    (executeKernel state live request).state.devices = state.devices := by
  by_cases hpolicy : state.controls ≠ selectedControls
  · simp [executeKernel, hpolicy]
  · by_cases hlive : live ≠ state.controls
    · simp [executeKernel, hpolicy, hlive]
    · by_cases hprivilege : privilegeAllows live .kernel = true
      · by_cases hauthorized : portManifest.contains request.key = true
        · simp [executeKernel, hpolicy, hlive, hprivilege, hauthorized] at hrejected
        · simp [executeKernel, hpolicy, hlive, hprivilege, hauthorized]
      · simp [executeKernel, hpolicy, hlive, hprivilege]

private def zeroDevices : DeviceState := ⟨0, 0, 0, 0⟩

private def witnessState : State := ⟨selectedControls, zeroDevices⟩

private def witnessOperation : PortOperation :=
  { port := 0x3f8, direction := .output, width := .byte, value := 65 }

private def witnessKernelRequest : KernelRequest :=
  { purpose := .serial, operation := witnessOperation }

private def upperBitByteRequest : KernelRequest :=
  { purpose := .serial
    operation := { witnessOperation with value := 0x100 } }

private def zeroByteRequest : KernelRequest :=
  { purpose := .serial
    operation := { witnessOperation with value := 0 } }

/-- Regression for x86 `outb`: bit 8 of a request is not device-visible, so
`0x100` and `0` have identical accepted byte-output semantics. -/
theorem byte_output_discards_upper_bits :
    executeKernel witnessState selectedControls upperBitByteRequest =
        executeKernel witnessState selectedControls zeroByteRequest ∧
      (executeKernel witnessState selectedControls upperBitByteRequest).state.devices =
        { zeroDevices with serial := 0 } := by
  native_decide

/-! ## Fixed-width differential adapter

The scalar boundary below is deliberately narrower than the rich model.  Two
control-mode words select stored and live snapshots, an origin word selects
either the user path or one trusted kernel purpose, and a direction/width word
selects one of the six x86 operation classes.  Invalid scalar encodings return
the reserved all-ones word before a modeled transition is constructed.

The device projection uses one byte per finite device class.  This is complete
for the selected manifest because every authorized output is byte-wide and the
adapter starts from byte-sized sentinel values.  It is corpus evidence, not a
general serialization of arbitrary `DeviceState` values.
-/

private def adapterDevices : DeviceState :=
  { serial := 0x11, pic := 0x22, pit := 0x33, debugExit := 0x44 }

/-- Canonical control mutations used by the hosted and QEMU differential
corpus.  Mode zero is the accepted snapshot; every other named mode isolates
one rejected control or read-back condition. -/
def decodeControlMode (mode : UInt64) : Option Controls :=
  match mode with
  | 0 => some selectedControls
  | 1 => some { selectedControls with ioPrivilegeLevel := 3 }
  | 2 => some { selectedControls with tssDescriptorLimit := 102 }
  | 3 => some { selectedControls with tssDescriptorLimit := 104 }
  | 4 => some { selectedControls with ioMapBase := 103 }
  | 5 => some { selectedControls with ioBitmapPresent := true }
  | 6 => some { selectedControls with kernelConfigured := false }
  | 7 => some { selectedControls with readbackMatches := false }
  | _ => none

private inductive AdapterOrigin where
  | user
  | kernel (purpose : Purpose)

private def decodeAdapterOrigin : UInt64 → Option AdapterOrigin
  | 0 => some .user
  | 1 => some (.kernel .serial)
  | 2 => some (.kernel .pic)
  | 3 => some (.kernel .pit)
  | 4 => some (.kernel .debugExit)
  | _ => none

private def decodeDirectionWidth : UInt64 → Option (Direction × Width)
  | 0 => some (.input, .byte)
  | 1 => some (.output, .byte)
  | 2 => some (.input, .word)
  | 3 => some (.output, .word)
  | 4 => some (.input, .dword)
  | 5 => some (.output, .dword)
  | _ => none

/-- The differential boundary admits exactly the finite port words needed by
the canonical corpus. Unknown scalar words fail before a `Nat` is constructed,
so the freestanding entry point retains no arbitrary-precision runtime path. -/
private def decodeAdapterPort : UInt64 → Option Nat
  | 0x3f8 => some 0x3f8
  | 0x3f9 => some 0x3f9
  | 0x3fa => some 0x3fa
  | 0x3fb => some 0x3fb
  | 0x3fc => some 0x3fc
  | 0x3fd => some 0x3fd
  | 0x20 => some 0x20
  | 0x21 => some 0x21
  | 0xa0 => some 0xa0
  | 0xa1 => some 0xa1
  | 0x40 => some 0x40
  | 0x43 => some 0x43
  | 0xf4 => some 0xf4
  | 0x3f7 => some 0x3f7
  | _ => none

private def fixedWidthOutcome (storedMode liveMode originPurpose port
    directionWidth value : UInt64) : Option Outcome := do
  let storedControls ← decodeControlMode storedMode
  let liveControls ← decodeControlMode liveMode
  let origin ← decodeAdapterOrigin originPurpose
  let (direction, width) ← decodeDirectionWidth directionWidth
  let decodedPort ← decodeAdapterPort port
  let state : State :=
    { controls := storedControls, devices := adapterDevices }
  let operation : PortOperation :=
    { port := decodedPort, direction, width, value }
  match origin with
  | .user => pure (executeUser state liveControls operation)
  | .kernel purpose =>
      pure (executeKernel state liveControls { purpose, operation })

private def encodeResult : Result → UInt64
  | .userDeniedGP => 1
  | .kernelAccepted => 2
  | .rejected .malformedPolicy => 16
  | .rejected .staleReadback => 17
  | .rejected .unauthorizedKernelOperation => 18

/-- Pack the complete byte-bounded device projection in manifest order. -/
private def encodeDevices (devices : DeviceState) : UInt64 :=
  devices.serial % 0x100 +
    (devices.pic % 0x100) * 0x100 +
    (devices.pit % 0x100) * 0x10000 +
    (devices.debugExit % 0x100) * 0x1000000

private def encodeOutcome (outcome : Outcome) : UInt64 :=
  encodeResult outcome.result * 0x100000000 + encodeDevices outcome.state.devices

/-- Rich-model expectation used when generating the differential corpus. -/
def directPortIOModelExpected (storedMode liveMode originPurpose port directionWidth
    value : UInt64) : UInt64 :=
  match fixedWidthOutcome storedMode liveMode originPurpose port directionWidth value with
  | some outcome => encodeOutcome outcome
  | none => 0xffffffffffffffff

private def adapterInitialDevices : UInt64 := 0x44332211

private def scalarResult (code devices : UInt64) : UInt64 :=
  code * 0x100000000 + devices

private def validControlMode : UInt64 → Bool
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => true
  | _ => false

private def validOriginPurpose : UInt64 → Bool
  | 0 | 1 | 2 | 3 | 4 => true
  | _ => false

private def validDirectionWidth : UInt64 → Bool
  | 0 | 1 | 2 | 3 | 4 | 5 => true
  | _ => false

private def validAdapterPort : UInt64 → Bool
  | 0x3f8 | 0x3f9 | 0x3fa | 0x3fb | 0x3fc | 0x3fd
  | 0x20 | 0x21 | 0xa0 | 0xa1 | 0x40 | 0x43 | 0xf4 | 0x3f7 => true
  | _ => false

private def serialOutputPort : UInt64 → Bool
  | 0x3f8 | 0x3f9 | 0x3fa | 0x3fb | 0x3fc => true
  | _ => false

private def picOutputPort : UInt64 → Bool
  | 0x20 | 0x21 | 0xa0 | 0xa1 => true
  | _ => false

private def pitOutputPort : UInt64 → Bool
  | 0x40 | 0x43 => true
  | _ => false

/-- Allocation-free implementation of the finite scalar boundary.  The rich
model above remains the independent corpus oracle; this implementation uses
only fixed-width words so the freestanding image does not retain Lean heap or
arbitrary-precision-natural helpers. -/
@[export leanos_direct_port_io_demo]
def directPortIODemo (storedMode liveMode originPurpose port directionWidth
    value : UInt64) : UInt64 :=
  if !(validControlMode storedMode && validControlMode liveMode &&
      validOriginPurpose originPurpose && validDirectionWidth directionWidth &&
      validAdapterPort port) then
    0xffffffffffffffff
  else if !(storedMode == 0) then
    0x1044332211
  else if !(liveMode == 0) then
    0x1144332211
  else if originPurpose == 0 then
    0x0144332211
  else if originPurpose == 1 && directionWidth == 1 && serialOutputPort port then
    scalarResult 2 (0x44332200 + value % 0x100)
  else if originPurpose == 1 && directionWidth == 0 && port == 0x3fd then
    0x0244332211
  else if originPurpose == 2 && directionWidth == 1 && picOutputPort port then
    scalarResult 2 (0x44330011 + (value % 0x100) * 0x100)
  else if originPurpose == 3 && directionWidth == 1 && pitOutputPort port then
    scalarResult 2 (0x44002211 + (value % 0x100) * 0x10000)
  else if originPurpose == 4 && directionWidth == 1 && port == 0xf4 then
    scalarResult 2 (0x00332211 + (value % 0x100) * 0x1000000)
  else
    0x1244332211

theorem directPortIODemo_selected_user_agrees :
    directPortIODemo 0 0 0 0x3f8 1 65 =
      directPortIOModelExpected 0 0 0 0x3f8 1 65 := by native_decide

theorem directPortIODemo_selected_kernel_agrees :
    directPortIODemo 0 0 1 0x3f8 1 65 =
      directPortIOModelExpected 0 0 1 0x3f8 1 65 := by native_decide

theorem directPortIODemo_rejection_agrees :
    directPortIODemo 0 0 1 0x20 1 65 =
      directPortIOModelExpected 0 0 1 0x20 1 65 := by native_decide

theorem directPortIODemo_invalid_origin :
    directPortIODemo 0 0 5 0x3f8 1 65 = 0xffffffffffffffff := by
  native_decide

theorem directPortIODemo_invalid_control :
    directPortIODemo 8 0 1 0x3f8 1 65 = 0xffffffffffffffff := by
  native_decide

theorem directPortIODemo_invalid_port :
    directPortIODemo 0 0 1 0xffffffffffffffff 1 65 = 0xffffffffffffffff := by
  native_decide

theorem directPortIODemo_byte_normalization :
    directPortIODemo 0 0 1 0x3f8 1 0x100 =
      directPortIODemo 0 0 1 0x3f8 1 0 := by
  native_decide

/-- Non-vacuity: one reviewed kernel output is accepted and changes only its
device projection, while the same attacker-controlled port/value words are
denied with an identical device state on the user path. -/
theorem policy_nonvacuous :
    (executeKernel witnessState selectedControls witnessKernelRequest).result =
        .kernelAccepted ∧
      (executeKernel witnessState selectedControls witnessKernelRequest).state.devices =
        { zeroDevices with serial := 65 } ∧
      executeUser witnessState selectedControls witnessOperation =
        { state := witnessState, result := .userDeniedGP } := by
  native_decide

end LeanOS.DirectPortIO
